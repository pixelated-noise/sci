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
      ;; Override juxt so freeze/thaw can reconstruct the composed fn.
      #?(:clj
         (assoc 'clojure.core/juxt
                {:val (fn sci-juxt
                        ([f]
                         (with-meta
                           (fn
                             ([] [(f)])
                             ([x] [(f x)])
                             ([x y] [(f x y)])
                             ([x y z] [(f x y z)])
                             ([x y z & args] [(apply f x y z args)]))
                           {:sci/juxt-fns [f]}))
                        ([f g]
                         (with-meta
                           (fn
                             ([] [(f) (g)])
                             ([x] [(f x) (g x)])
                             ([x y] [(f x y) (g x y)])
                             ([x y z] [(f x y z) (g x y z)])
                             ([x y z & args] [(apply f x y z args) (apply g x y z args)]))
                           {:sci/juxt-fns [f g]}))
                        ([f g h]
                         (with-meta
                           (fn
                             ([] [(f) (g) (h)])
                             ([x] [(f x) (g x) (h x)])
                             ([x y] [(f x y) (g x y) (h x y)])
                             ([x y z] [(f x y z) (g x y z) (h x y z)])
                             ([x y z & args] [(apply f x y z args) (apply g x y z args) (apply h x y z args)]))
                           {:sci/juxt-fns [f g h]}))
                        ([f g h & fs]
                         (let [all (list* f g h fs)]
                           (with-meta
                             (fn [& args] (vec (map #(apply % args) all)))
                             {:sci/juxt-fns (vec all)}))))
                 :meta {:name 'juxt :doc (:doc (meta #'clojure.core/juxt))}})
         :cljs identity)
      ;; Override complement so freeze/thaw can reconstruct it.
      #?(:clj
         (assoc 'clojure.core/complement
                {:val (fn sci-complement [f]
                        (with-meta
                          (fn
                            ([] (not (f)))
                            ([x] (not (f x)))
                            ([x y] (not (f x y)))
                            ([x y & zs] (not (apply f x y zs))))
                          {:sci/complement-f f}))
                 :meta {:name 'complement :doc (:doc (meta #'clojure.core/complement))}})
         :cljs identity)
      ;; Override every-pred so freeze/thaw can reconstruct it.
      #?(:clj
         (assoc 'clojure.core/every-pred
                {:val (fn sci-every-pred
                        ([p] (with-meta
                               (fn ep1
                                 ([] true)
                                 ([x] (boolean (p x)))
                                 ([x y] (boolean (and (p x) (p y))))
                                 ([x y z] (boolean (and (p x) (p y) (p z))))
                                 ([x y z & args] (boolean (and (ep1 x y z) (every? p args)))))
                               {:sci/every-pred-fns [p]}))
                        ([p1 p2]
                         (with-meta
                           (fn ep2
                             ([] true)
                             ([x] (boolean (and (p1 x) (p2 x))))
                             ([x y] (boolean (and (p1 x) (p2 x) (p1 y) (p2 y))))
                             ([x y z] (boolean (and (p1 x) (p2 x) (p1 y) (p2 y) (p1 z) (p2 z))))
                             ([x y z & args] (boolean (and (ep2 x y z)
                                                           (every? #(and (p1 %) (p2 %)) args)))))
                           {:sci/every-pred-fns [p1 p2]}))
                        ([p1 p2 p3]
                         (with-meta
                           (fn ep3
                             ([] true)
                             ([x] (boolean (and (p1 x) (p2 x) (p3 x))))
                             ([x y] (boolean (and (p1 x) (p2 x) (p3 x) (p1 y) (p2 y) (p3 y))))
                             ([x y z] (boolean (and (p1 x) (p2 x) (p3 x) (p1 y) (p2 y) (p3 y)
                                                    (p1 z) (p2 z) (p3 z))))
                             ([x y z & args] (boolean (and (ep3 x y z)
                                                           (every? #(and (p1 %) (p2 %) (p3 %)) args)))))
                           {:sci/every-pred-fns [p1 p2 p3]}))
                        ([p1 p2 p3 & ps]
                         (let [all (list* p1 p2 p3 ps)]
                           (with-meta
                             (fn epn
                               ([] true)
                               ([x] (every? #(% x) all))
                               ([x y] (and (every? #(% x) all) (every? #(% y) all)))
                               ([x y z] (and (every? #(% x) all) (every? #(% y) all) (every? #(% z) all)))
                               ([x y z & args] (boolean (and (epn x y z)
                                                              (every? (fn [a] (every? #(% a) all)) args)))))
                             {:sci/every-pred-fns (vec all)}))))
                 :meta {:name 'every-pred :doc (:doc (meta #'clojure.core/every-pred))}})
         :cljs identity)
      ;; Override some-fn so freeze/thaw can reconstruct it.
      #?(:clj
         (assoc 'clojure.core/some-fn
                {:val (fn sci-some-fn
                        ([p] (with-meta
                               (fn sp1
                                 ([] nil)
                                 ([x] (p x))
                                 ([x y] (or (p x) (p y)))
                                 ([x y z] (or (p x) (p y) (p z)))
                                 ([x y z & args] (or (sp1 x y z) (some p args))))
                               {:sci/some-fn-fns [p]}))
                        ([p1 p2]
                         (with-meta
                           (fn sp2
                             ([] nil)
                             ([x] (or (p1 x) (p2 x)))
                             ([x y] (or (p1 x) (p2 x) (p1 y) (p2 y)))
                             ([x y z] (or (p1 x) (p2 x) (p1 y) (p2 y) (p1 z) (p2 z)))
                             ([x y z & args] (or (sp2 x y z) (some #(or (p1 %) (p2 %)) args))))
                           {:sci/some-fn-fns [p1 p2]}))
                        ([p1 p2 p3]
                         (with-meta
                           (fn sp3
                             ([] nil)
                             ([x] (or (p1 x) (p2 x) (p3 x)))
                             ([x y] (or (p1 x) (p2 x) (p3 x) (p1 y) (p2 y) (p3 y)))
                             ([x y z] (or (p1 x) (p2 x) (p3 x) (p1 y) (p2 y) (p3 y)
                                          (p1 z) (p2 z) (p3 z)))
                             ([x y z & args] (or (sp3 x y z) (some #(or (p1 %) (p2 %) (p3 %)) args))))
                           {:sci/some-fn-fns [p1 p2 p3]}))
                        ([p1 p2 p3 & ps]
                         (let [all (list* p1 p2 p3 ps)]
                           (with-meta
                             (fn spn
                               ([] nil)
                               ([x] (some #(% x) all))
                               ([x y] (or (some #(% x) all) (some #(% y) all)))
                               ([x y z] (or (some #(% x) all) (some #(% y) all) (some #(% z) all)))
                               ([x y z & args] (or (spn x y z)
                                                    (some (fn [a] (some #(% a) all)) args))))
                             {:sci/some-fn-fns (vec all)}))))
                 :meta {:name 'some-fn :doc (:doc (meta #'clojure.core/some-fn))}})
         :cljs identity)
      ;; Override memoize so freeze/thaw can reconstruct it.
      #?(:clj
         (assoc 'clojure.core/memoize
                {:val (fn sci-memoize [f]
                        (let [mem (atom {})]
                          (with-meta
                            (fn [& args]
                              (if-let [e (find @mem args)]
                                (val e)
                                (let [ret (apply f args)]
                                  (swap! mem assoc args ret)
                                  ret)))
                            {:sci/memoize-f f})))
                 :meta {:name 'memoize :doc (:doc (meta #'clojure.core/memoize))}})
         :cljs identity)
      ;; Override fnil so freeze/thaw can reconstruct it.
      #?(:clj
         (assoc 'clojure.core/fnil
                {:val (fn sci-fnil
                        ([f x]
                         (with-meta
                           (fn
                             ([a] (f (if (nil? a) x a)))
                             ([a b] (f (if (nil? a) x a) b))
                             ([a b c] (f (if (nil? a) x a) b c))
                             ([a b c & ds] (apply f (if (nil? a) x a) b c ds)))
                           {:sci/fnil-f f :sci/fnil-defaults [x]}))
                        ([f x y]
                         (with-meta
                           (fn
                             ([a b] (f (if (nil? a) x a) (if (nil? b) y b)))
                             ([a b c] (f (if (nil? a) x a) (if (nil? b) y b) c))
                             ([a b c & ds] (apply f (if (nil? a) x a) (if (nil? b) y b) c ds)))
                           {:sci/fnil-f f :sci/fnil-defaults [x y]}))
                        ([f x y z]
                         (with-meta
                           (fn
                             ([a b] (f (if (nil? a) x a) (if (nil? b) y b)))
                             ([a b c] (f (if (nil? a) x a) (if (nil? b) y b) (if (nil? c) z c)))
                             ([a b c & ds] (apply f (if (nil? a) x a) (if (nil? b) y b) (if (nil? c) z c) ds)))
                           {:sci/fnil-f f :sci/fnil-defaults [x y z]})))
                 :meta {:name 'fnil :doc (:doc (meta #'clojure.core/fnil))}})
         :cljs identity)
      ;; Override delay so the inner fn is an SCI closure (serializable for freeze/thaw).
      ;; The host delay macro expands to (new Delay (fn* [] body)) — fn* produces a JVM
      ;; closure that freeze can't serialize. Using fn instead creates an SCI closure.
      #?(:clj
         (assoc 'clojure.core/delay
                {:val (fn [form _env & _]
                        (let [body (rest form)]
                          `(new clojure.lang.Delay (fn [] ~@body))))
                 :meta {:name 'delay :macro true :doc (:doc (meta #'clojure.core/delay))}
                 :macro? true
                 :host-macro? true})
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
