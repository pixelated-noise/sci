(ns sci.vm.machine
  "Core VM data structures. The machine is always a plain serialisable map.")

;; ============================================================
;; Machine constructors
;; ============================================================

(defn make-machine
  "Create a fresh machine with default state."
  [{:keys [env ns-table heap permissions]}]
  {:stack   []          ; vector of frames, top = last
   :env     (or env {}) ; current lexical env: symbol -> value
   :ns      (or ns-table {}) ; namespace table
   :heap    (or heap {})     ; interned vars: qualified-sym -> {:val :meta :dynamic?}
   :heap-atom (atom (or heap {}))  ; shared mutable heap for closures
   :result  nil         ; most recently computed value
   :status  :running    ; :running | :done | :suspend | :effect
   :effect  nil         ; when :effect, describes the requested side effect
   :suspend-data nil    ; when :suspend, optional data from (suspend! data)
   :current-ns 'user    ; current namespace symbol
   :permissions permissions
   :bindings {}         ; dynamic binding stack
   :callstack []})      ; call tracking: [{:ns :name :line :column :file} ...]

;; ============================================================
;; Stack operations
;; ============================================================

(defn push-frame
  "Push a frame onto the stack."
  [machine frame]
  (update machine :stack conj frame))

(defn pop-frame
  "Pop the top frame from the stack."
  [machine]
  (update machine :stack pop))

(defn peek-frame
  "Look at the top frame without removing it."
  [machine]
  (peek (:stack machine)))

(defn replace-frame
  "Replace the top frame."
  [machine frame]
  (update machine :stack #(conj (pop %) frame)))

(defn set-result
  "Set the result value."
  [machine value]
  (assoc machine :result value))

(defn push-value
  "Pop top frame and set result to value."
  [machine value]
  (-> machine pop-frame (set-result value)))

;; ============================================================
;; Resume
;; ============================================================

(defn resume
  "Resume a suspended machine, optionally providing a value for (suspend!)."
  [machine & [value]]
  (-> machine
      (assoc :status :running
             :suspend-data nil)
      (set-result value)))
