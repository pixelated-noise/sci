(ns sci.vm.host
  "Host function registry — wraps clojure.core and other namespaces
   so interpreted code can call them directly."
  (:require [clojure.string :as str]
            [clojure.set]
            [clojure.walk]
            [clojure.edn]
            [clojure.repl]
            [clojure.pprint]
            [sci.lang]))

(defn- make-ns-registry
  "Generate a registry of all public vars from a namespace."
  [ns-sym]
  #?(:clj
     (let [ns (the-ns ns-sym)
           publics (ns-publics ns)]
       (reduce-kv
        (fn [acc sym v]
          (let [qualified (symbol (str ns-sym) (str sym))
                m (meta v)
                is-macro? (:macro m)
                is-dynamic? (or (:dynamic m) (.isDynamic ^clojure.lang.Var v))]
            (assoc acc qualified {:val (if is-macro? v (deref v))
                                  :meta (select-keys m [:name :ns :macro :doc :arglists :file :line])
                                  :macro? is-macro?
                                  :dynamic? is-dynamic?})))
        {}
        publics))
     :cljs {}))

(def default-namespaces
  '[clojure.core clojure.string clojure.set clojure.walk clojure.edn clojure.repl clojure.pprint])

(defn- add-private-vars
  "Add specific private vars needed by host macro expansions."
  [heap]
  #?(:clj
     (let [privates [#'clojure.repl/print-doc
                     #'clojure.repl/special-doc
                     #'clojure.repl/namespace-doc]]
       (reduce (fn [h v]
                 (let [m (meta v)
                       qualified (symbol (str (:ns m)) (str (:name m)))]
                   (assoc h qualified {:val @v
                                       :meta (select-keys m [:name :ns :doc :arglists])
                                       :dynamic? (:dynamic m)})))
               heap
               privates))
     :cljs heap))

(defn default-heap
  "Build the default heap with all host functions."
  []
  (-> (reduce (fn [heap ns-sym] (merge heap (make-ns-registry ns-sym)))
              {}
              default-namespaces)
      (add-private-vars)
      #?(:clj
         ;; Add seq-to-map-for-destructuring behavior for Clojure 1.11 kwargs map support.
         ;; On Clojure 1.10, destructuring of [& {:keys [a]}] generates
         ;; (PersistentHashMap/create (seq args)). Clojure 1.11 uses
         ;; seq-to-map-for-destructuring which treats a single-map seq as the map directly.
         (assoc 'clojure.lang.PersistentHashMap/create
                {:val (fn [& args]
                        (if (and (= 1 (count args))
                                 (sequential? (first args))
                                 (= 1 (count (first args)))
                                 (map? (first (first args))))
                          (first (first args))
                          (clojure.lang.Reflector/invokeStaticMethod
                           clojure.lang.PersistentHashMap "create" (to-array args))))
                 :meta {:name 'create}}
                ;; Clojure 1.11 destructuring uses PersistentArrayMap/EMPTY and createAsIfByAssoc
                'clojure.lang.PersistentArrayMap/EMPTY
                {:val clojure.lang.PersistentArrayMap/EMPTY
                 :meta {:name 'EMPTY}}
                'clojure.lang.PersistentArrayMap/createAsIfByAssoc
                {:val (fn [& args]
                        (clojure.lang.Reflector/invokeStaticMethod
                         clojure.lang.PersistentArrayMap "createAsIfByAssoc" (to-array args)))
                 :meta {:name 'createAsIfByAssoc}})
         :cljs identity)
      ;; Override with-bindings* to handle sci.lang.Var objects.
      ;; The host clojure.core/with-bindings* expects clojure.lang.Var keys, but SCI
      ;; code produces sci.lang.Var objects from #'sym. Map SCI vars to real CLJ vars
      ;; where possible (e.g. #'*out* -> #'clojure.core/*out*), then push JVM thread bindings.
      ;; Override push-thread-bindings to handle sci.lang.Var keys.
      ;; The host clojure.core/binding macro expands to (push-thread-bindings {#'var val}).
      ;; In SCI, #'var evaluates to a sci.lang.Var, not a clojure.lang.Var.
      ;; We map SCI vars to their real CLJ vars before pushing JVM bindings.
      #?(:clj
         (assoc 'clojure.core/push-thread-bindings
                {:val (fn sci-push-thread-bindings [binding-map]
                        (let [clj-bindings
                              (reduce (fn [acc [k v]]
                                        (cond
                                          (instance? clojure.lang.Var k)
                                          (assoc acc k v)
                                          (instance? sci.lang.Var k)
                                          (let [m (.-meta-map ^sci.lang.Var k)
                                                qsym (or (:sci.impl/var-sym m)
                                                         (when (and (:ns m) (:name m))
                                                           (symbol (str (:ns m)) (str (:name m)))))
                                                real-var (when qsym
                                                           (try (let [rv (clojure.core/resolve qsym)]
                                                                  (when (and rv (var? rv) (.isDynamic ^clojure.lang.Var rv)) rv))
                                                                (catch Exception _ nil)))]
                                            (if real-var (assoc acc real-var v) acc))
                                          :else acc))
                                      {} binding-map)]
                          (when (seq clj-bindings)
                            (clojure.core/push-thread-bindings clj-bindings))))
                 :meta {:name 'push-thread-bindings :doc (:doc (meta #'clojure.core/push-thread-bindings))}})
         :cljs identity)
      #?(:clj
         (assoc 'clojure.core/with-bindings*
                {:val (fn [binding-map f & args]
                        (let [clj-bindings
                              (reduce (fn [acc [k v]]
                                        (cond
                                          ;; Real CLJ var — use as-is
                                          (instance? clojure.lang.Var k)
                                          (assoc acc k v)
                                          ;; SCI var — look up the real CLJ var via meta
                                          (instance? sci.lang.Var k)
                                          (let [m (.-meta-map ^sci.lang.Var k)
                                                qsym (or (:sci.impl/var-sym m)
                                                         (when (and (:ns m) (:name m))
                                                           (symbol (str (:ns m)) (str (:name m)))))
                                                real-var (when qsym
                                                           (try (let [rv (clojure.core/resolve qsym)]
                                                                  (when (and rv (var? rv) (.isDynamic ^clojure.lang.Var rv)) rv))
                                                                (catch Exception _ nil)))]
                                            (if real-var (assoc acc real-var v) acc))
                                          :else acc))
                                      {} binding-map)]
                          (if (seq clj-bindings)
                            (clojure.core/with-bindings* clj-bindings f)
                            (apply f args))))
                 :meta {:name 'with-bindings* :doc #?(:clj (:doc (meta #'clojure.core/with-bindings*)) :cljs nil)}})
         :cljs identity)
      ;; Override comp and partial so their results carry reconstruction metadata,
      ;; enabling freeze/thaw to serialize and reconstruct composed/partial fns.
      #?(:clj
         (assoc 'clojure.core/comp
                {:val (fn sci-comp
                        ([] identity)
                        ([f] f)
                        ([f g]
                         (let [result (fn
                                        ([] (f (g)))
                                        ([x] (f (g x)))
                                        ([x y] (f (g x y)))
                                        ([x y & args] (f (apply g x y args))))]
                           (with-meta result {:sci/comp-fns [f g]})))
                        ([f g & more]
                         (reduce sci-comp (list* f g more))))
                 :meta {:name 'comp :doc (:doc (meta #'clojure.core/comp))}})
         :cljs identity)
      #?(:clj
         (assoc 'clojure.core/partial
                {:val (fn sci-partial
                        ([f] f)
                        ([f arg1]
                         (with-meta
                           (fn
                             ([] (f arg1))
                             ([x] (f arg1 x))
                             ([x y] (f arg1 x y))
                             ([x y z] (f arg1 x y z))
                             ([x y z & args] (apply f arg1 x y z args)))
                           {:sci/partial-f f :sci/partial-args [arg1]}))
                        ([f arg1 arg2]
                         (with-meta
                           (fn
                             ([] (f arg1 arg2))
                             ([x] (f arg1 arg2 x))
                             ([x y] (f arg1 arg2 x y))
                             ([x y z] (f arg1 arg2 x y z))
                             ([x y z & args] (apply f arg1 arg2 x y z args)))
                           {:sci/partial-f f :sci/partial-args [arg1 arg2]}))
                        ([f arg1 arg2 arg3]
                         (with-meta
                           (fn
                             ([] (f arg1 arg2 arg3))
                             ([x] (f arg1 arg2 arg3 x))
                             ([x y] (f arg1 arg2 arg3 x y))
                             ([x y z & args] (apply f arg1 arg2 arg3 x y z args)))
                           {:sci/partial-f f :sci/partial-args [arg1 arg2 arg3]}))
                        ([f arg1 arg2 arg3 & more]
                         (with-meta
                           (fn [& args] (apply f arg1 arg2 arg3 (concat more args)))
                           {:sci/partial-f f :sci/partial-args (into [arg1 arg2 arg3] more)})))
                 :meta {:name 'partial :doc (:doc (meta #'clojure.core/partial))}})
         :cljs identity)
      ;; Override assert with a runtime check so (set! *assert* false) takes effect.
      ;; The host clojure.core/assert macro checks *assert* at expansion time, not runtime.
      ;; Our override always emits (when *assert* ...), letting the VM evaluate *assert*
      ;; from the heap at runtime.
      #?(:clj
         (assoc 'clojure.core/assert
                {:val (fn [form _env & _]
                        (let [args (rest form)
                              expr (first args)
                              msg (second args)]
                          (if msg
                            `(when *assert*
                               (when-not ~expr
                                 (throw (new AssertionError (str "Assert failed: " ~msg "\n" (pr-str '~expr))))))
                            `(when *assert*
                               (when-not ~expr
                                 (throw (new AssertionError (str "Assert failed: " (pr-str '~expr)))))))))
                 :meta {:name 'assert :macro true :doc #?(:clj (:doc (meta #'clojure.core/assert)) :cljs nil)}
                 :macro? true
                 :host-macro? true})
         :cljs identity)))

#?(:clj
   (defn inverse-registry
     "Build an identity-based lookup from fn/var objects to qualified symbols.
      Returns a java.util.IdentityHashMap for O(1) identity-based lookups."
     [heap]
     (let [m (java.util.IdentityHashMap.)]
       (doseq [[qualified-sym entry] heap]
         (let [v (:val entry)]
           (if (:macro? entry)
             ;; For macros, map the var object
             (when (var? v) (.put m v qualified-sym))
             ;; For regular fns, map the fn value
             (when (fn? v) (.put m v qualified-sym)))))
       m)))

(def ^:private default-imports
  "Default Java imports (java.lang classes) available in all namespaces."
  #?(:clj
     (let [common-classes [String Long Integer Double Float Short Byte Character Boolean
                           Object Class Number Comparable Iterable
                           Thread Runnable Exception RuntimeException Error
                           Throwable ArithmeticException ArrayIndexOutOfBoundsException
                           ClassCastException ClassNotFoundException
                           IllegalArgumentException IllegalStateException
                           IndexOutOfBoundsException NullPointerException
                           NumberFormatException StringIndexOutOfBoundsException
                           UnsupportedOperationException
                           Math System Runtime Process ProcessBuilder
                           StackTraceElement StringBuilder StringBuffer
                           clojure.lang.ExceptionInfo]]
       (reduce (fn [m ^Class c]
                 (assoc m (symbol (.getSimpleName c)) c))
               {} common-classes))
     :cljs {}))

(defn default-ns-table
  "Build the default namespace table."
  []
  (reduce (fn [t ns-sym]
            (assoc t ns-sym {:aliases {} :refers {} :imports default-imports}))
          {'user {:aliases {} :refers {} :imports default-imports}}
          default-namespaces))
