;;; gh-copilot-chat-lsp.el --- copilot.el LSP backend for gh-copilot-chat -*- lexical-binding: t; -*-

;; Copyright (C) 2024  gh-copilot-chat maintainers
;; The MIT License (MIT)

;;; Commentary:
;; This backend uses copilot.el's LSP server connection for gh-copilot-chat,
;; eliminating the need for curl and manual token management.
;;
;; The Copilot Language Server exposes these custom LSP methods for chat
;; (matching VS Code's Copilot Chat panel implementation):
;;
;;   conversation/create   — start a new conversation (returns conversationId)
;;   conversation/turn     — send a follow-up in an existing conversation
;;   conversation/destroy  — dispose of a conversation
;;
;; Streaming uses standard LSP $/progress notifications keyed by a
;; workDoneToken supplied in the request.
;;
;; copilot.el API contract (verified against copilot.el source 20260331):
;;   - `copilot--async-request' is a MACRO that expands at compile time.
;;     It captures `(current-buffer)' and silently drops :success-fn
;;     if that buffer is killed before the response arrives.
;;   - `copilot-on-notification' appends handlers via `cons' without dedup.
;;   - Notification handlers receive one arg: the params plist directly.
;;   - `copilot--connection' is the raw jsonrpc-process-connection object.
;;   - `copilot--connection-alivep' checks process exit status.
;;   - `copilot--workspace-root' returns truename of project root, or nil.
;;   - `copilot--get-language-id' returns language string for current buffer.
;;   - `copilot--path-to-uri' handles Windows drive letters correctly.

;;; Code:

(require 'gh-copilot-chat-body)
(require 'gh-copilot-chat-connection)
(require 'gh-copilot-chat-backend)
(require 'gh-copilot-chat-common)
(require 'gh-copilot-chat-spinner)
(require 'gh-copilot-chat-mcp)

(require 'copilot)
(require 'copilot-chat)

(declare-function flymake-diagnostics "flymake")
(declare-function flymake-diagnostic-beg "flymake")
(declare-function flymake-diagnostic-text "flymake")

;; Use following variables to set
;; `copilot-chat-model'
;; `copilot-chat-use-agent-mode'

;;
;; cleanup copilot-chat
;;
(with-eval-after-load 'copilot-chat
  (remhash '$/progress copilot--notification-handlers)
  (remhash 'conversation/context copilot--request-handlers)
  (remhash 'conversation/invokeClientToolConfirmation copilot--request-handlers)
  (remhash 'conversation/invokeClientTool copilot--request-handlers)
  )

;;
;; Private data structure (per instance)
;;

(cl-defstruct gh-copilot-chat-lsp
  "Private data for the copilot.el LSP backend.
One instance is stored per chat instance in the `gh-copilot-chat--backend' slot."
  (conversation-id nil :type (or null string))
  (current-turn-id nil :type (or null string))
  (work-done-token nil :type (or null string))
  (request-id nil :type (or null integer))
  (streaming-p nil :type boolean)
  (accumulated-text "" :type string))

;;
;; State: mapping tokens → (instance . callback)
;;

(defvar gh-copilot-chat-lsp--handler-installed nil
  "Non-nil once our $/progress handler has been registered.
Guards against duplicate registration since `copilot-on-notification'
uses `cons' without dedup check.")

(defvar gh-copilot-chat-lsp--active-tokens (make-hash-table :test 'equal)
  "Hash table mapping work-done-token → (instance . callback).
Used to route $/progress notifications to the correct chat instance.
Only tokens registered here are handled by our progress handler;
all others fall through to copilot.el's built-in $/progress handler.")

(defvar gh-copilot-chat-lsp--token-counter 0
  "Monotonically increasing counter to guarantee unique tokens.")

(defun gh-copilot-chat-lsp--generate-token (instance)
  "Generate a unique work-done-token string for INSTANCE."
  (cl-incf gh-copilot-chat-lsp--token-counter)
  (format "gh-copilot-chat-%s-%s-%d"
          (gh-copilot-chat-directory instance)
          (format-time-string "%s%3N")
          gh-copilot-chat-lsp--token-counter))

;;
;; $/progress handler
;;

(defun gh-copilot-chat-lsp--extract-reply (value)
  "Extract reply text from $/progress report VALUE.
Handles both the direct :reply key and the nested :editAgentRounds
format used by newer Copilot Language Server versions."
  (let ((reply (or (plist-get value :reply)
                   (when-let* ((rounds (plist-get value :editAgentRounds))
                               ((vectorp rounds))
                               ((> (length rounds) 0)))
                     (mapconcat (lambda (round)
                                  (or (plist-get round :reply) ""))
                                rounds
                                "")))))
    (if (stringp reply)
        reply
      (and reply (format "%s" reply)))))

(defsubst gh-copilot-chat-lsp--handle-conversation-id (backend response)
  "Handle conversation/create result to capture conversationId."
  (copilot--dbind (conversationId turnId) response
    ;; :success-fn of conversation/create is not called in some case,
    ;; make sure to capture conversationId and turnId here as well.
    (when (and conversationId
               (null (gh-copilot-chat-lsp-conversation-id backend)))
      (setf (gh-copilot-chat-lsp-conversation-id backend)
            conversationId))
    (when (and turnId
               (null (gh-copilot-chat-lsp-current-turn-id backend)))
      (setf (gh-copilot-chat-lsp-current-turn-id backend)
            conversationId)))
  )

(defun gh-copilot-chat-lsp--handle-progress (msg)
  "Handle $/progress notifications for gh-copilot-chat.
MSG is the notification params plist with keys :token and :value.

Only tokens present in `gh-copilot-chat-lsp--active-tokens' are
processed; all others are ignored (handled by copilot.el's own handler)."
  (setq gh-copilot-chat-lsp--current-token (plist-get msg :token))
  (let* ((token (plist-get msg :token))
         (value (plist-get msg :value))
         (entry (gethash token gh-copilot-chat-lsp--active-tokens)))
    (when entry
      (let* ((instance (car entry))
             (callback (cdr entry))
             (backend (gh-copilot-chat--backend instance))
             (kind (plist-get value :kind)))
        (when backend
          (cond
           ;; ── Stream begins ──
           ((equal kind "begin")
            (setf (gh-copilot-chat-lsp-streaming-p backend) t)
            ;; :success-fn of conversation/create is not called in some case,
            ;; make sure to capture conversationId and turnId here as well.
            (gh-copilot-chat-lsp--handle-conversation-id backend value))

           ;; ── Stream report (incremental text) ──
           ((equal kind "report")
            (when-let* ((reply (gh-copilot-chat-lsp--extract-reply value)))
              ;; The server sends the full accumulated reply so far.
              ;; Compute the delta (only new text since last report).
              (let* ((accumulated (gh-copilot-chat-lsp-accumulated-text backend))
                     (delta (if (string-prefix-p accumulated reply)
                                (substring reply (length accumulated))
                              ;; Not a prefix — server reset or different format
                              reply)))
                (setf (gh-copilot-chat-lsp-accumulated-text backend) reply)
                (when (and delta (not (string-empty-p delta)))
                  (funcall callback instance delta)))))

           ;; ── Stream ends ──
           ((equal kind "end")
            (setf (gh-copilot-chat-lsp-streaming-p backend) nil)

            ;; print out followUp
            (let* ((result (plist-get value :result))
                   ;; The server normally sends an object here, but
                   ;; guard against any other shape.
                   (result (and (listp result) result))
                   (copilot-chat--follow-up (plist-get result :followUp))
                   (error-msg (copilot-chat--error-text
                               (plist-get result :error))))
              ;; Surface a turn-level error the server reports at the
              ;; end, which would otherwise leave only an empty reply.
              (when error-msg
                (funcall callback instance
                         (copilot-chat--format-error error-msg)))
              (when (and (stringp copilot-chat--follow-up)
                         (not (string-empty-p copilot-chat--follow-up)))
                (funcall callback instance
                         (propertize
                          (format "Follow-up: %s\n\n" copilot-chat--follow-up)
                          'face 'copilot-chat-follow-up-face))))
            
            ;; Signal end-of-response to the frontend
            (funcall callback instance gh-copilot-chat--magic)
            ;; Record full response in instance history
            (let ((full-text (gh-copilot-chat-lsp-accumulated-text backend)))
              (unless (string-empty-p full-text)
                (push `(:content ,full-text :role "assistant")
                      (gh-copilot-chat-history instance))))
            ;; Cleanup — safe: this remhash is NOT inside maphash
            (setf (gh-copilot-chat-lsp-accumulated-text backend) "")
            (remhash token gh-copilot-chat-lsp--active-tokens)
            (gh-copilot-chat--spinner-stop instance))))))))

;;
;; Conversation context request handler
;;

(defun gh-copilot-chat--handle-context (msg)
  "Handle `conversation/context' request MSG."
  ;; (let ((skill-id (plist-get msg :skillId)))
  ;;   (if (equal skill-id "current-editor")
  ;;       (copilot-chat--generate-context-doc)
  ;;     ;; Unknown skill — return empty context
  ;;     nil))
  (setq gh-copilot-chat-lsp--current-token (plist-get msg :token))
  (when-let* ((token (plist-get msg :token))
              (entry (gethash token gh-copilot-chat-lsp--active-tokens))
              (instance (car entry))
              (callback (cdr entry))
              (backend (gh-copilot-chat--backend instance)))
    (funcall callback instance
             (format "*[Warning] NOT handled: conversation/context*: %s" msg))
    )
  )

;;
;; current token, instance and callback
;;

(defvar gh-copilot-chat-lsp--current-token nil
  "Holds the current token")

(defun gh-copilot-chat-lsp--current-instance ()
  (let ((entry (gethash gh-copilot-chat-lsp--current-token gh-copilot-chat-lsp--active-tokens)))
    (or (car entry) (gh-copilot-chat--current-instance))))

(defun gh-copilot-chat-lsp--current-callback ()
  (let ((entry (gethash gh-copilot-chat-lsp--current-token gh-copilot-chat-lsp--active-tokens)))
    (or (cdr entry) 'gh-copilot-chat-prompt-cb)))

(defun gh-copilot-chat--callback (msg)
  "send the msg to the frontend"
  (if-let* ((instance (gh-copilot-chat-lsp--current-instance))
            (callback (gh-copilot-chat-lsp--current-callback))
            ;; (backend (gh-copilot-chat--backend instance))
            )
      (funcall callback instance msg)
    (message "No callback found for token: %s" gh-copilot-chat-lsp--current-token)
    ))

;;
;; conversation/invokeClientToolConfirmation handlers
;;



(defsubst gh-copilot-chat--handle-tool-confirmation (msg)
  (setq gh-copilot-chat-lsp--current-token (plist-get msg :token))
  (copilot-chat--handle-tool-confirmation msg))

;;
;; conversation/invokeClientToolConfirmation handlers
;;

(define-advice copilot-chat--insert-tool-status (:override (name detail) gh)
  (gh-copilot-chat--callback (propertize (format "\n[Tool: %s] %s\n" name detail)
                                         'face 'copilot-chat-tool-face)))
;;(advice-remove 'copilot-chat--insert-tool-status 'gh)

(defsubst gh-copilot-chat--handle-tool-invocation (msg)
  (setq gh-copilot-chat-lsp--current-token (plist-get msg :token))
  (copilot-chat--handle-tool-invocation msg))

;;
;; Tool registration
;;

(define-advice copilot-chat--tool-definitions (:override () gh)
  "Return the list of client tool definitions for agent mode."
  (vector
   (list :name "run_in_terminal"
         :description "Run a shell command in the terminal."
         :inputSchema
         (list :type "object"
               :properties
               (list :command (list :type "string"
                                    :description "Shell command to execute.")
                     :explanation (list :type "string"
                                        :description "Short reason for running the command."))
               :required ["command"]
               :additionalProperties :json-false))
   (list :name "create_file"
         :description "Create a new file with the given content."
         :inputSchema
         (list :type "object"
               :properties
               (list :filePath (list :type "string"
                                     :description "Path of the file to create.")
                     :content (list :type "string"
                                    :description "Full file content to write."))
               :required ["filePath" "content"]
               :additionalProperties :json-false))
   (list :name "get_errors"
         :description "Get diagnostics/errors for the given files."
         :inputSchema
         (list :type "object"
               :properties
               (list :filePaths (list :type "array"
                                      :description "List of file paths to analyze."
                                      :items (list :type "string"
                                                   :description "A file path.")))
               :required ["filePaths"]
               :additionalProperties :json-false))
   (list :name "fetch_web_page"
         :description "Fetch the content of web pages."
         :inputSchema
         (list :type "object"
               :properties
               (list :urls (list :type "array"
                                 :description "List of URLs to fetch."
                                 :items (list :type "string"
                                              :description "A URL to fetch.")))
               :required ["urls"]
               :additionalProperties :json-false))))

(defsubst gh-copilot-chat--register-tools ()
  (copilot-chat--register-tools))

;; register handlers
(defun gh-copilot-chat-lsp--install-handler ()
  "Register our $/progress handler with copilot.el — idempotent.
Safe to call multiple times; only registers once."
  (unless gh-copilot-chat-lsp--handler-installed
    (copilot-on-notification '$/progress
                             #'gh-copilot-chat-lsp--handle-progress)
    (copilot-on-request 'conversation/context
                        #'gh-copilot-chat--handle-context)
    (copilot-on-request 'conversation/invokeClientToolConfirmation
                        #'gh-copilot-chat--handle-tool-confirmation)
    (copilot-on-request 'conversation/invokeClientTool
                        #'gh-copilot-chat--handle-tool-invocation)
    (setq gh-copilot-chat-lsp--handler-installed t)))

;;
;; Backend: init
;;

(defun gh-copilot-chat-lsp--init (instance)
  "Initialize the LSP backend for INSTANCE.
Creates the per-instance private data struct, ensures copilot.el's
server is running, and installs the progress notification handler."
  (setf (gh-copilot-chat--backend instance) (make-gh-copilot-chat-lsp))
  (unless (copilot--connection-alivep)
    (copilot--start-server))
  ;; Handlers must be registered before sending any requests, otherwise we
  (gh-copilot-chat-lsp--install-handler)
  ;; Agent mode requires tool registration upfront, so do it at init time.
  (when copilot-chat-use-agent-mode
    (gh-copilot-chat--register-tools))

  ;; Set the model value for this instance to the default
  (setf (gh-copilot-chat-model instance) (copilot-chat--model)))

;;
;; Backend: clean
;;

(defun gh-copilot-chat-lsp--clean (instance)
  "Clean up the LSP backend for INSTANCE.
Sends conversation/destroy to the server and removes active tokens."
  (when-let* ((backend (gh-copilot-chat--backend instance))
              (conv-id (gh-copilot-chat-lsp-conversation-id backend)))
    ;; Only destroy if server is alive — do NOT restart just for cleanup
    (when (copilot--connection-alivep)
      (condition-case _err
          ;; copilot--async-request is a macro — must be called directly
          (copilot--async-request
           'conversation/destroy
           (list :conversationId conv-id)
           :success-fn (lambda (_) nil)
           :error-fn (lambda (_) nil))
        (error nil)))
    (setf (gh-copilot-chat-lsp-conversation-id backend) nil))
  ;; Remove active tokens for this instance.
  ;; Collect keys first to avoid mutating hash table inside maphash.
  (let ((tokens-to-remove '()))
    (maphash (lambda (token entry)
               (when (eq (car entry) instance)
                 (push token tokens-to-remove)))
             gh-copilot-chat-lsp--active-tokens)
    (dolist (token tokens-to-remove)
      (remhash token gh-copilot-chat-lsp--active-tokens)))
  (setq gh-copilot-chat-lsp--current-token nil)
  (message "gh-copilot-chat: Cleaned up LSP backend"))

;;
;; Backend: login
;;

(defun gh-copilot-chat-lsp--login ()
  "Login using copilot.el's built-in authentication.
Delegates to `copilot-login' which handles the OAuth device flow via
the signInInitiate/signInConfirm LSP methods."
  (unless (copilot--connection-alivep)
    (copilot--start-server))
  ;; Mark gh-copilot-chat as authenticated.
  ;; Actual token lifecycle is managed by the Copilot Language Server.
  (setf (gh-copilot-chat-connection-github-token gh-copilot-chat--connection)
        "managed-by-copilot-el")
  (setf (gh-copilot-chat-connection-token gh-copilot-chat--connection)
        `((expires_at . ,(+ (float-time) (* 365 24 3600)))))
  (setf (gh-copilot-chat-connection-ready gh-copilot-chat--connection) t))

;;
;; Backend: renew-token
;;

(defun gh-copilot-chat-lsp--renew-token ()
  "Renew token — near no-op since copilot.el manages auth.
Ensures the connection is alive and refreshes the sentinel expiry
to prevent gh-copilot-chat from re-triggering the auth flow."
  (unless (copilot--connection-alivep)
    (copilot--start-server))
  (setf (gh-copilot-chat-connection-token gh-copilot-chat--connection)
        `((expires_at . ,(+ (float-time) (* 365 24 3600))))))

;;
;; Backend: ask — message building
;;

(defun gh-copilot-chat-lsp--build-message (instance prompt no-context add-frontend-prompt)
  "Build the full message string from INSTANCE context and PROMPT.
Embeds referenced buffer contents as fenced code blocks, using
copilot.el's `copilot--get-language-id' for accurate language tags."
  (unless no-context
    ;; add buffers as context
    (let ((buffers (gh-copilot-chat-buffers instance))
          (parts '()))
      (dolist (buf buffers)
        (when (buffer-live-p buf)
          (with-current-buffer buf
            (let ((lang (copilot--get-language-id))
                  (content (buffer-substring-no-properties
                            (point-min) (point-max)))
                  (name (or (buffer-file-name buf) (buffer-name buf))))
              (push (format "File: %s\n```%s\n%s\n```\n"
                            name lang content)
                    parts)))))
      (when parts
        (setq prompt (concat (string-join (nreverse parts) "\n") "\n" prompt))))
    ;; TODO: History
    ;; Copilot LSP remember conversation history.
    )

  ;; Apply create-req-fn if available
  (when add-frontend-prompt
    (if-let* ((create-req-fn
               (gh-copilot-chat-frontend-create-req-fn (gh-copilot-chat--get-frontend))))
        (setq prompt (funcall create-req-fn prompt no-context))
      ;; for git commit messages, add the prompt to the message
      (when  gh-copilot-chat-prompt
        (setq prompt (concat prompt "\n\n" gh-copilot-chat-prompt)))
      ))
  ;; (message "gh-copilot-chat: Sending prompt:\n%s" prompt)

  prompt
  )

;;
;; Backend: ask — error handling
;;

(defun gh-copilot-chat-lsp--handle-request-error (instance token callback err)
  "Handle an LSP request error for INSTANCE.
Cleans up TOKEN from active-tokens, stops the spinner,
and reports ERR via CALLBACK using the standard (instance content) protocol."
  (gh-copilot-chat--spinner-stop instance)
  (remhash token gh-copilot-chat-lsp--active-tokens)
  (let ((msg (cond
              ((and (listp err) (plist-get err :message))
               (plist-get err :message))
              ((stringp err) err)
              (t (format "%S" err)))))
    (funcall callback instance (format "**LSP Error:** %s" msg))
    (funcall callback instance gh-copilot-chat--magic)))

(define-advice copilot-chat--insert-error (:override (error-msg)  gh) 
  "Insert ERROR-MSG into the chat buffer with error styling."
  (gh-copilot-chat--callback (copilot-chat--format-error error-msg)))

;;
;; Backend: ask — main entry point
;;

(defun gh-copilot-chat-lsp--ask (instance prompt callback out-of-context &optional source)
  "Ask a question via the copilot.el LSP conversation API.

INSTANCE is the chat instance (struct with model, buffers, history, etc).
PROMPT is the user's message (string or structured).
CALLBACK receives (INSTANCE TEXT) for each streaming chunk and
  (INSTANCE `gh-copilot-chat--magic') to signal end-of-response.
OUT-OF-CONTEXT if non-nil means this is a transient request (e.g. git commit).

The model is read from `(gh-copilot-chat-model INSTANCE)' — each
instance can have its own model selection (see `gh-copilot-chat-set-model')."
  (unless (copilot--connection-alivep)
    (copilot--start-server))
  (gh-copilot-chat-lsp--install-handler)

  (let* ((backend (gh-copilot-chat--backend instance))
         (token (gh-copilot-chat-lsp--generate-token instance))
         (conversation-id (gh-copilot-chat-lsp-conversation-id backend))
         (message (if (stringp prompt)
                      (gh-copilot-chat-lsp--build-message instance prompt out-of-context
                                                          (not conversation-id))
                    (format "%s" prompt))))

    ;; Reset state for new request
    (setf (gh-copilot-chat-lsp-accumulated-text backend) "")
    (setf (gh-copilot-chat-lsp-work-done-token backend) token)

    (setq gh-copilot-chat-lsp--current-token token)

    ;; Register token for $/progress routing
    (puthash token (cons instance callback)
             gh-copilot-chat-lsp--active-tokens)

    ;; Record user message in history
    (unless out-of-context
      (push `(:content ,(if (stringp prompt) prompt (format "%s" prompt))
                       :role "user")
            (gh-copilot-chat-history instance)))

    ;; Start spinner (use gh-copilot-chat--get-buffer, not chat-buffer slot)
    (when (buffer-live-p (gh-copilot-chat--get-buffer instance))
      (gh-copilot-chat--spinner-start instance))

    ;; Dispatch: new conversation or follow-up turn
    (if conversation-id
        (gh-copilot-chat-lsp--send-turn instance message token callback source)
      (gh-copilot-chat-lsp--create-conversation
       instance message token callback source))))

;;
;; Backend: ask — conversation/create
;;

(defun gh-copilot-chat-lsp--create-conversation
    (instance message token callback &optional source)
  "Create a new conversation for INSTANCE with MESSAGE.
TOKEN is the workDoneToken for $/progress routing.
CALLBACK is the streaming callback.

Sends `conversation/create' to the Copilot Language Server,
matching the protocol used by VS Code's Copilot Chat panel."
  (let ((backend (gh-copilot-chat--backend instance))
        (model (gh-copilot-chat-model instance))
        (source (or source "panel")))
    (setf (gh-copilot-chat-lsp-request-id backend)
          (copilot--async-request
           'conversation/create
           (append
            (list :workDoneToken token
                  :turns (vector
                          (list :request message
                                :response ""
                                :turnId ""))
                  :capabilities (list :skills (vector "current-editor")
                                      :allSkills t)
                  :source source)
            ;; does not work.
            ;; (when gh-copilot-chat-prompt
            ;;   (list :systemPrompt gh-copilot-chat-prompt))
            ;; Per-instance model selection
            (when-let* ((model (copilot-chat--model)))
              (list :model model))
            ;; Workspace folders — use copilot--path-to-uri for Windows support
            (list :workspaceFolders
                  (vconcat
                   (when-let* ((root ;; (copilot--workspace-root)
                                (gh-copilot-chat-directory instance)))
                     (list (list :uri (copilot--path-to-uri root)
                                 :name (file-name-nondirectory
                                        (directory-file-name root)))))))
            (when copilot-chat-use-agent-mode
              (list :chatMode "Agent"
                    :needToolCallConfirmation t))
            )
           :success-fn ; it is not called in some cases, so also handle conversationId in progress handler
           (lambda (result)
             (gh-copilot-chat-lsp--handle-conversation-id backend result)
             (gh-copilot-chat-lsp--handle-model instance callback
                                                (plist-get result :modelName))
             )
           :error-fn
           (lambda (err)
             (gh-copilot-chat-lsp--handle-request-error
              instance token callback err))))
    (message "gh-copilot-chat: Sent conversation/create with source '%s'." source)))

;;
;; Backend: ask — conversation/turn
;;

(defun gh-copilot-chat-lsp--send-turn (instance message token callback &optional source)
  "Send a follow-up turn for INSTANCE with MESSAGE.
TOKEN is the workDoneToken.  CALLBACK is the streaming callback.

Sends `conversation/turn' to the Copilot Language Server."
  (let ((backend (gh-copilot-chat--backend instance))
        (model (gh-copilot-chat-model instance))
        (source (or source "panel")))
    (setf (gh-copilot-chat-lsp-request-id backend)
          (copilot--async-request
           'conversation/turn
           (list :workDoneToken token
                 :conversationId (gh-copilot-chat-lsp-conversation-id backend)
                 :model (copilot-chat--model) ; avoid error "[chat] Error processing turn Error: Model is not specified"
                 :message message
                 :source source)
           :success-fn
           (lambda (result)
             (when result
               (setf (gh-copilot-chat-lsp-current-turn-id backend)
                     (plist-get result :turnId))
               )
             (gh-copilot-chat-lsp--handle-model instance callback
                                                (plist-get result :modelName))
             )
           :error-fn
           (lambda (err)
             (gh-copilot-chat-lsp--handle-request-error
              instance token callback err))))))

(defun gh-copilot-chat-lsp--handle-model (instance callback modelName)
  (funcall callback instance
           (format "\n*-- Generated by: %s --*\n"
                   modelName))
  )

;;
;; Backend: cancel
;;

(defun gh-copilot-chat-lsp--cancel (instance)
  "Cancel the in-flight request for INSTANCE.
Sends $/cancelRequest (same pattern as `copilot--cancel-completion')."
  (gh-copilot-chat--spinner-stop instance)
  (when-let* ((backend (gh-copilot-chat--backend instance)))
    (let ((req-id (gh-copilot-chat-lsp-request-id backend))
          (token (gh-copilot-chat-lsp-work-done-token backend)))
      ;; Send $/cancelRequest to the LSP server
      (when (and req-id (copilot--connection-alivep))
        (condition-case nil
            (jsonrpc-notify copilot--connection
                            '$/cancelRequest
                            (list :id req-id))
          (error nil)))
      ;; Clean up token mapping
      (when token
        (remhash token gh-copilot-chat-lsp--active-tokens))
      (setq gh-copilot-chat-lsp--current-token nil)
      ;; Reset state
      (setf (gh-copilot-chat-lsp-request-id backend) nil)
      (setf (gh-copilot-chat-lsp-streaming-p backend) nil)
      (setf (gh-copilot-chat-lsp-accumulated-text backend) ""))))

;;
;; Backend: quotas
;;

(defun gh-copilot-chat-lsp--quotas ()
  "Get quotas — not available via LSP.
The Copilot Language Server does not expose rate limit info through
a dedicated endpoint.  Returns nil to indicate unsupported."
  nil)


;;
;; User command: select model
;;
(defun gh-copilot-chat-lsp-select-model ()
  "Interactively select a Copilot Chat model."
  (interactive)
  (let* ((models (copilot--request 'copilot/models nil))
         (chat-models
          (seq-filter (lambda (m)
                        (seq-contains-p (plist-get m :scopes) "chat-panel"))
                      models))
         (choices (mapcar (lambda (m)
                            (cons (format "%s (%s)" (plist-get m :modelName) (plist-get m :id))
                                  (plist-get m :id)))
                          chat-models))
         (choice (completing-read (format "Chat model (%s): " (gh-copilot-chat-lsp--get-model))
                                  (sort choices) nil t))
         (model-id (cdr (assoc choice choices))))

    (gh-copilot-chat-lsp--set-model model-id)))

(defun gh-copilot-chat-lsp--get-model ()
  (if-let* ((instance (gh-copilot-chat--current-instance)))
      (gh-copilot-chat-model instance)
    (copilot-chat--model)))

(defun gh-copilot-chat-lsp--set-model (model-id)
  (if-let* ((instance (gh-copilot-chat--current-instance)))
      ;; Set the model value only for current instance
      (progn (setf (gh-copilot-chat-model instance) model-id)
             (message "Copilot Chat model set to %s for current instance" model-id))
    ;; set global default
    (setq copilot-chat-model model-id)
    (message "LSP Chat model set to %s" model-id)))

(defun gh-copilot-chat-lsp--current-ask (msg)
  (let ((instance (gh-copilot-chat--current-instance))
        (callback (gh-copilot-chat-lsp--current-callback)))
    (gh-copilot-chat--display instance)
    (gh-copilot-chat-lsp--ask instance
                              msg
                              callback
                              nil)))

(define-advice copilot-chat-slash-command (:around (oldfun) gh)
  (cl-letf (((symbol-function 'copilot-chat) #'gh-copilot-chat-lsp--current-ask))
    (funcall oldfun)))

;;
;; Backend registration
;;

(cl-pushnew
 (make-gh-copilot-chat-backend
  :id 'lsp
  :select-model-fn #'gh-copilot-chat-lsp-select-model
  :init-fn #'gh-copilot-chat-lsp--init
  :clean-fn #'gh-copilot-chat-lsp--clean
  :login-fn #'gh-copilot-chat-lsp--login
  :renew-token-fn #'gh-copilot-chat-lsp--renew-token
  :ask-fn #'gh-copilot-chat-lsp--ask
  :cancel-fn #'gh-copilot-chat-lsp--cancel
  :quotas-fn #'gh-copilot-chat-lsp--quotas)
 gh-copilot-chat--backend-list
 :test (lambda (a b)
         (eq (gh-copilot-chat-backend-id a)
             (gh-copilot-chat-backend-id b))))

(provide 'gh-copilot-chat-lsp)
;;; gh-copilot-chat-lsp.el ends here
