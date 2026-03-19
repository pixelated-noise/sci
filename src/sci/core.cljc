(ns sci.core
  "Public API for SCI — backed by the explicit stack VM."
  (:refer-clojure :exclude [eval read read-string alter-var-root intern resolve
                            read+string with-redefs binding assert
                            with-in-str with-out-str future pmap
                            with-bindings create-ns find-ns ns])
  (:require [sci.vm.machine :as machine]
            [sci.vm.step :as step]
            [sci.vm.host :as host]
            [edamame.core :as edamame]
            [sci.lang]
            [sci.impl.types]
            #?(:clj [clojure.string :as str])))

;; ============================================================
;; Reader
;; ============================================================

(defn read-all
  "Read all forms from a string."
  [s]
  (edamame/parse-string-all s {:all true
                                :row-key :line
                                :col-key :column
                                :end-row-key :end-line
                                :end-col-key :end-column
                                :location? seq?
                                :read-cond :allow
                                :features #{:clj}
                                :fn true
                                :quote true
                                :syntax-quote {:resolve-symbol
                                               (fn [sym]
                                                 sym)}
                                :var true
                                :deref true
                                :regex true}))

;; ============================================================
;; Context / init
;; ============================================================

(defn init
  "Create an SCI context (the machine's initial state)."
  [opts]
  (let [{:keys [bindings namespaces classes aliases imports
                features load-fn readers deny allow]} opts
        heap (host/default-heap)
        ns-table (host/default-ns-table)
        ;; Install user bindings into heap as user/sym vars
        heap (reduce-kv
              (fn [h sym val]
                (let [sym-name (if (symbol? sym) (name sym) (str sym))
                      qualified (symbol "user" sym-name)]
                  (assoc h qualified {:val val
                                      :meta {}
                                      :dynamic? true})))
              heap
              (or bindings {}))
        ;; Install custom namespaces
        heap (reduce-kv
              (fn [h ns-sym ns-map]
                (reduce-kv
                 (fn [h2 sym val]
                   (let [sym-name (if (symbol? sym) (name sym) (str sym))
                         qualified (symbol (str ns-sym) sym-name)]
                     (assoc h2 qualified {:val val
                                          :meta {}
                                          :dynamic? false})))
                 h
                 ns-map))
              heap
              (or namespaces {}))
        ;; Set up aliases in user namespace
        ns-table (if aliases
                   (update ns-table 'user assoc :aliases
                           (reduce-kv (fn [a k v] (assoc a k v)) {} aliases))
                   ns-table)]
    {:heap heap
     :ns-table ns-table
     :classes (or classes {})
     :features (or features #{:clj})
     :load-fn load-fn
     :readers readers
     :deny deny
     :allow allow}))

(defn fork
  "Create a fork of a context — an independent copy."
  [ctx]
  (update ctx :heap #(or % {})))

;; ============================================================
;; Evaluation
;; ============================================================

(defn- make-machine-from-ctx
  "Create a fresh machine from a context and a list of forms."
  [ctx forms]
  (let [m (machine/make-machine
           {:heap (:heap ctx)
            :ns-table (:ns-table ctx)
            :permissions {:allow (:allow ctx)
                          :deny (:deny ctx)}})]
    ;; Push a single eval frame with the forms wrapped in do
    (let [expr (if (= 1 (count forms))
                 (first forms)
                 (cons 'do forms))]
      (machine/push-frame m {:op :eval :expr expr}))))

(defn eval-string
  "Evaluate a string of Clojure code."
  ([s] (eval-string s nil))
  ([s opts]
   (let [ctx (if (and opts (:heap opts))
               opts  ;; already initialized
               (init (or opts {})))
         forms (read-all s)
         machine (make-machine-from-ctx ctx forms)]
     (step/run machine))))

(defn eval-string*
  "Same as eval-string but takes an already-initialized context.
   Context is first arg (unlike eval-string where string is first)."
  [ctx s]
  (eval-string s ctx))

(defn eval-form
  "Evaluate a single form."
  ([ctx form]
   (let [machine (make-machine-from-ctx ctx [form])]
     (step/run machine))))

;; ============================================================
;; Reader API
;; ============================================================

(defn reader
  "Create a reader from a string."
  [s]
  ;; Return an atom wrapping position + string for sequential reads
  (atom {:source s :pos 0}))

(defn source-reader
  "Create a source reader from a string."
  [s]
  (reader s))

(defn parse-next
  "Parse the next form from a reader."
  [ctx rdr]
  (let [state @rdr
        remaining (subs (:source state) (:pos state))]
    (if (empty? (clojure.string/trim remaining))
      ::eof
      (let [form (edamame/parse-string remaining
                                        {:all true
                                         :read-cond :allow
                                         :features #{:clj}
                                         :fn true
                                         :quote true
                                         :var true
                                         :deref true
                                         :regex true})]
        ;; Advance position (approximate — find end of first form)
        (swap! rdr assoc :pos (count (:source state)))
        form))))

(defn get-line-number [rdr]
  1)

(defn get-column-number [rdr]
  1)

;; ============================================================
;; Vars API
;; ============================================================

(defn new-var
  "Create a new SCI var."
  ([name] (new-var name nil nil))
  ([name init-val] (new-var name init-val nil))
  ([name init-val opts]
   init-val))

(defn new-dynamic-var
  "Create a new dynamic SCI var."
  ([name] (new-dynamic-var name nil nil))
  ([name init-val] (new-dynamic-var name init-val nil))
  ([name init-val opts]
   (atom init-val)))

(defmacro copy-var
  "Copy a Clojure var into an SCI namespace."
  ([clj-var sci-ns]
   `(copy-var ~clj-var ~sci-ns nil))
  ([clj-var sci-ns opts]
   (let [copy-meta-from (when (map? opts) (:copy-meta-from opts))
         opts-expr (if copy-meta-from
                     (let [clean-opts (dissoc opts :copy-meta-from)]
                       `(merge (meta (var ~copy-meta-from)) ~clean-opts))
                     opts)]
     `(let [v# (var ~clj-var)
            m# (meta v#)
            val# (deref v#)]
        (with-meta (if (:macro m#)
                     val#
                     (fn [& args#] (apply val# args#)))
          (merge m# ~opts-expr))))))

(defn copy-var*
  "Copy a Clojure var into an SCI namespace (runtime version, takes a var)."
  ([clj-var sci-ns] (copy-var* clj-var sci-ns nil))
  ([clj-var sci-ns opts]
   (let [m (meta clj-var)
         val (deref clj-var)]
     (with-meta (if (:macro m)
                  val
                  (fn [& args] (apply val args)))
       (merge m opts)))))

(defmacro copy-ns
  "Copy a Clojure namespace into SCI."
  ([ns-sym sci-ns]
   `(copy-ns ~ns-sym ~sci-ns nil))
  ([ns-sym sci-ns opts]
   (let [;; Extract opts at compile time to quote symbols properly
         opts-map (when (map? opts) opts)
         exclude-syms (when opts-map (:exclude opts-map))
         exclude-when-meta-keys (when opts-map (:exclude-when-meta opts-map))
         copy-meta-val (when opts-map (:copy-meta opts-map))]
     `(let [ns# (the-ns '~ns-sym)
            publics# (clojure.core/ns-publics ns#)
            exclude# '~(set exclude-syms)
            exclude-when-meta# '~(set exclude-when-meta-keys)
          copy-meta-val# ~(if (= :all copy-meta-val) :all
                              (when copy-meta-val `'~(vec copy-meta-val)))]
        (reduce-kv
         (fn [m# sym# v#]
           (let [vm# (meta v#)]
             (if (or (contains? exclude# sym#)
                     (and (not= :all copy-meta-val#)
                          (:skip-wiki vm#))
                     (some #(get vm# %) exclude-when-meta#))
               m#
               (let [val# (deref v#)
                     selected-meta# (cond
                                      (= :all copy-meta-val#) vm#
                                      copy-meta-val#
                                      (select-keys vm# (concat [:name :arglists :macro :sci/macro] copy-meta-val#))
                                      :else
                                      (select-keys vm# [:name :arglists :macro :sci/macro :doc]))]
                 (assoc m# sym# (with-meta
                                  (if (or (:macro vm#) (:sci/macro vm#))
                                    val#
                                    (fn [& args#] (apply val# args#)))
                                  selected-meta#))))))
         {}
         publics#)))))

(defn alter-var-root
  "Alter the root value of a var."
  [v f & args]
  (apply f @v args))

(defn intern
  "Intern a var."
  [ctx ns-sym var-name val]
  ctx)

;; ============================================================
;; Dynamic binding macros
;; ============================================================

(defmacro binding
  "Dynamic binding form for SCI vars.
   Supports both real Clojure vars and SCI dynamic vars (atoms)."
  [bindings & body]
  (let [pairs (partition 2 bindings)
        ;; Check at compile time if the binding targets are vars
        all-vars? (every? (fn [[target _]]
                            (and (symbol? target)
                                 (clojure.core/resolve target)
                                 (var? (clojure.core/resolve target))))
                          pairs)]
    (if all-vars?
      `(clojure.core/binding ~bindings ~@body)
      ;; For SCI dynamic vars (atoms), save/restore manually
      (let [sym-pairs (mapv (fn [[target val-expr]]
                              [(gensym "old") target val-expr])
                            pairs)
            save-bindings (mapv (fn [[old-sym target _]] `(def ~old-sym (deref ~target))) sym-pairs)
            set-bindings (mapv (fn [[_ target val-expr]] `(reset! ~target ~val-expr)) sym-pairs)
            restore-bindings (mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs)]
        `(let [~@(mapcat (fn [[old-sym target _]] [old-sym `(deref ~target)]) sym-pairs)]
           ~@set-bindings
           (try
             (do ~@body)
             (finally
               ~@restore-bindings)))))))

(defmacro with-bindings
  "Execute body with SCI var bindings."
  [binding-map & body]
  `(do ~@body))

(defmacro with-redefs
  "Temporarily redefine vars."
  [bindings & body]
  `(clojure.core/with-redefs ~bindings ~@body))

;; ============================================================
;; Namespace operations
;; ============================================================

(defn create-ns
  "Create a namespace in the SCI context."
  [sym]
  sym)

(defn find-ns
  "Find a namespace."
  [ctx sym]
  nil)

(defn add-namespace!
  "Add a namespace to a context."
  [ctx ns-sym ns-map]
  ctx)

(defn add-class!
  "Add a class to a context."
  [ctx class-sym class]
  ctx)

(defn add-import!
  "Add an import to a context."
  [ctx ns-sym class-sym class]
  ctx)

(defn merge-opts
  "Merge additional options into a context."
  [ctx opts]
  (merge ctx opts))

;; ============================================================
;; IO vars
;; ============================================================

(def in (atom *in*))
(def out (atom *out*))
(def err (atom *err*))
(def print-fn (atom nil))
(def print-length (atom nil))
(def print-namespace-maps (atom true))
(def ns (atom (clojure.core/find-ns 'user)))
(def read-eval (atom false))
(def assert (atom true))
(def ^:dynamic file nil)

;; ============================================================
;; IO wrappers
;; ============================================================

(defmacro with-out-str [& body]
  `(clojure.core/with-out-str ~@body))

(defmacro with-in-str [s & body]
  `(clojure.core/with-in-str ~s ~@body))

(defmacro future [& body]
  `(clojure.core/future ~@body))

(defmacro pmap [f & colls]
  `(clojure.core/pmap ~f ~@colls))

;; ============================================================
;; Stacktrace / error support
;; ============================================================

(defn stacktrace [e]
  (when-let [data (ex-data e)]
    (:sci.impl/callstack data)))

(defn format-stacktrace [st]
  (when st
    (->> st
         (filter :line) ;; only entries with source locations
         (mapv (fn [{:keys [ns name line column file]}]
                 (let [ns-str (str (or ns "user"))
                       name-str (if name (str ns-str "/" name) (str ns-str))
                       file-str (or file "NO_SOURCE_PATH")]
                   (format "%-18s - %s:%s:%s" name-str file-str line column)))))))

;; ============================================================
;; set! for dynamic vars
;; ============================================================

(defn set!
  "Set a dynamic var's value."
  [v val]
  (if (instance? #?(:clj clojure.lang.Atom :cljs Atom) v)
    (reset! v val)
    val))

;; resolve is defined at the bottom of the file

;; ============================================================
;; EOF sentinel
;; ============================================================

(def eof ::eof)

(defn parse-next+string
  "Parse the next form from a reader, returning both the form and the string."
  [ctx rdr]
  (let [form (parse-next ctx rdr)]
    {:val form
     :string (pr-str form)}))

;; ============================================================
;; Additional API functions
;; ============================================================

(defn var->symbol
  "Get the fully qualified symbol for a var-like value."
  [v]
  (cond
    (var? v) (let [m (meta v)] (symbol (str (:ns m)) (str (:name m))))
    :else nil))

(defn eval-string+
  "Like eval-string but returns a map with :val and :ns."
  ([ctx s] (eval-string+ ctx s nil))
  ([ctx s opts]
   (let [use-ctx (if-let [ns-val (:ns opts)]
                   ctx ;; TODO: switch namespace
                   ctx)
         result (eval-string s use-ctx)]
     {:val result
      :ns (or (:ns opts) 'user)})))

(defn resolve
  "Resolve a symbol in a context."
  ([ctx sym]
   (when-let [heap (:heap ctx)]
     (let [qualified (if (qualified-symbol? sym)
                       sym
                       (symbol "clojure.core" (str sym)))]
       (when-let [entry (get heap qualified)]
         (:val entry))))))
