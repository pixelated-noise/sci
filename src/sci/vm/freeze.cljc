(ns sci.vm.freeze
  "Freeze (serialize) and thaw (deserialize) suspended VM machines."
  (:require [clojure.walk :as walk]
            #?(:clj [clojure.edn :as edn] :cljs [cljs.reader :as edn])
            [sci.lang]
            [sci.vm.host :as host]
            [sci.vm.machine :as m]
            [sci.vm.step :as step]))

;; ============================================================
;; Identity-map helpers — IdentityHashMap (JVM) / js/Map (CLJS)
;; ============================================================

(defn- id-map-new []
  #?(:clj (java.util.IdentityHashMap.)
     :cljs (js/Map.)))

(defn- id-map-put! [m k v]
  #?(:clj (.put ^java.util.IdentityHashMap m k v)
     :cljs (.set m k v)))

(defn- id-map-get [m k]
  #?(:clj (.get ^java.util.IdentityHashMap m k)
     :cljs (.get m k)))

(defn- id-map-has? [m k]
  #?(:clj (.containsKey ^java.util.IdentityHashMap m k)
     :cljs (.has m k)))

(defn- id-map-empty? [m]
  #?(:clj (.isEmpty ^java.util.IdentityHashMap m)
     :cljs (zero? (.-size m))))

;; ============================================================
;; Freeze — machine → EDN string
;; ============================================================

(def ^:private extra-namespaces
  "Namespaces injected by make-machine-from-ctx (not user-defined, not resolvable by thaw).
   Includes cljs.* mirrors of default namespaces for CLJS."
  #{"sci.core" "clojure.lang" "sci.lang"
    "cljs.core" "cljs.string" "cljs.set" "cljs.walk" "cljs.edn" "cljs.repl" "cljs.pprint"})

(defn- host-ns?
  "True if the qualified symbol belongs to a default (host) or extra namespace."
  [qualified-sym]
  (let [ns-str (namespace qualified-sym)]
    (or (some #(= ns-str (str %)) host/default-namespaces)
        (contains? extra-namespaces ns-str))))

(defn- user-heap
  "Extract only user-defined entries from the heap (not host namespaces)."
  [heap]
  (reduce-kv (fn [acc k v]
               (if (host-ns? k)
                 acc
                 (assoc acc k v)))
             {} heap))

(defn- replace-unserializable
  "Walk a data structure, replacing fn objects, vars, classes, and atoms
   with serializable tagged maps. The `seen` identity map tracks already-visited
   fn objects to break cycles (e.g. multimethod methods that capture the multimethod in env)."
  ([data inverse-reg]
   (replace-unserializable data inverse-reg (id-map-new)))
  ([data inverse-reg seen]
   (walk/postwalk
    (fn [x]
      (cond
        ;; Cycle detection — fn already serialized in an outer call
        (and (fn? x) (id-map-has? seen x))
        (id-map-get seen x)

        ;; SCI closure (IFn with :sci/closure metadata)
        (and (fn? x) (:sci/closure (meta x)))
        (let [closure-map (meta x)]
          ;; Recursively process the closure map (env may contain fns, atoms, etc.)
          (replace-unserializable (dissoc closure-map :sci/closure) inverse-reg seen))

        ;; comp result — carries :sci/comp-fns metadata
        (and (fn? x) (:sci/comp-fns (meta x)))
        {:type :comp-fn
         :fns (mapv #(replace-unserializable % inverse-reg seen)
                    (:sci/comp-fns (meta x)))}

        ;; partial result — carries :sci/partial-f and :sci/partial-args metadata
        (and (fn? x) (:sci/partial-f (meta x)))
        (let [m (meta x)]
          {:type :partial-fn
           :f (replace-unserializable (:sci/partial-f m) inverse-reg seen)
           :args (mapv #(replace-unserializable % inverse-reg seen)
                       (:sci/partial-args m))})

        ;; juxt result — carries :sci/juxt-fns metadata
        (and (fn? x) (:sci/juxt-fns (meta x)))
        {:type :juxt-fn
         :fns (mapv #(replace-unserializable % inverse-reg seen)
                    (:sci/juxt-fns (meta x)))}

        ;; complement result
        (and (fn? x) (:sci/complement-f (meta x)))
        {:type :complement-fn
         :f (replace-unserializable (:sci/complement-f (meta x)) inverse-reg seen)}

        ;; every-pred result
        (and (fn? x) (:sci/every-pred-fns (meta x)))
        {:type :every-pred-fn
         :fns (mapv #(replace-unserializable % inverse-reg seen)
                    (:sci/every-pred-fns (meta x)))}

        ;; some-fn result
        (and (fn? x) (:sci/some-fn-fns (meta x)))
        {:type :some-fn-fn
         :fns (mapv #(replace-unserializable % inverse-reg seen)
                    (:sci/some-fn-fns (meta x)))}

        ;; memoize result
        (and (fn? x) (:sci/memoize-f (meta x)))
        {:type :memoize-fn
         :f (replace-unserializable (:sci/memoize-f (meta x)) inverse-reg seen)}

        ;; fnil result
        (and (fn? x) (:sci/fnil-f (meta x)))
        (let [m (meta x)]
          {:type :fnil-fn
           :f (replace-unserializable (:sci/fnil-f m) inverse-reg seen)
           :defaults (:sci/fnil-defaults m)})

        ;; Multimethod — carries :sci/multimethod type in metadata
        (and (fn? x) (= :sci/multimethod (:type (meta x))))
        (let [m (meta x)
              mm-name (str (:name m))
              ;; Register a self-ref placeholder BEFORE recursing to break cycles
              self-ref {:type :multimethod-self-ref :name mm-name}
              _ (id-map-put! seen x self-ref)]
          {:type :multimethod
           :name mm-name
           :dispatch-fn (replace-unserializable (:dispatch-fn m) inverse-reg seen)
           :methods (reduce-kv (fn [acc k v]
                                 (assoc acc k (replace-unserializable v inverse-reg seen)))
                               {} @(:methods m))
           :prefer-table @(:prefer-table m)})

        ;; Protocol dispatch fn — carries :sci/protocol-dispatch metadata
        (and (fn? x) (:sci/protocol-dispatch (meta x)))
        (let [m (meta x)]
          {:type :protocol-dispatch-ref
           :protocol (str (:sci/protocol-name m))
           :method (str (:sci/method-name m))})

        ;; Type constructor (->Name) — tagged with reconstruction metadata
        (and (fn? x) (:sci/type-ctor (meta x)))
        (let [m (meta x)]
          {:type :type-ctor
           :type-name (:sci/type-name m)
           :fields (:sci/fields m)
           :record? (:sci/record? m)
           :mutable-fields (vec (:sci/mutable-fields m))})

        ;; Map constructor (map->Name) — tagged with reconstruction metadata
        (and (fn? x) (:sci/map-type-ctor (meta x)))
        (let [m (meta x)]
          {:type :map-type-ctor
           :type-name (:sci/type-name m)
           :fields (:sci/fields m)})

        ;; Deftype method fn — carries reconstruction metadata
        (and (fn? x) (:sci/deftype-method (meta x)))
        (let [m (meta x)]
          {:type :deftype-method
           :ns-sym (str (:sci/ns-sym m))
           :fields (mapv str (:sci/fields m))
           :params (mapv str (:sci/params m))
           :body (:sci/body m)
           :mutable-fields (mapv str (:sci/mutable-fields m))
           :env (replace-unserializable (:sci/env m) inverse-reg seen)})

        ;; Multi-arity deftype method dispatch fn
        (and (fn? x) (:sci/deftype-multi-method (meta x)))
        (let [fns (:sci/method-fns (meta x))]
          {:type :deftype-multi-method
           :fns (mapv (fn [{:keys [fn arity]}]
                        {:fn (replace-unserializable fn inverse-reg seen)
                         :arity arity})
                      fns)})

        ;; Host fn — look up in inverse registry
        (fn? x)
        (if-let [sym (id-map-get inverse-reg x)]
          {:type :host-fn-ref :id (str sym)}
          ;; Unknown fn — try to preserve as best we can
          {:type :unknown-fn :class (str #?(:clj (class x) :cljs (type x)))})

        ;; SCI Var — serialize inline (val, meta, dynamic?) so user-heap self-refs work
        (instance? sci.lang.Var x)
        (let [qsym (or (:sci.impl/var-sym (.-meta-map ^sci.lang.Var x))
                       (.-sym ^sci.lang.Var x))]
          {:type :sci-var
           :sym (str qsym)
           :val (replace-unserializable (.-val ^sci.lang.Var x) inverse-reg seen)
           :meta (replace-unserializable (.-meta-map ^sci.lang.Var x) inverse-reg seen)
           :dynamic? (.-dynamic? ^sci.lang.Var x)})

        ;; Var (host Clojure var) — only on JVM
        #?(:clj (var? x) :cljs false)
        #?(:clj (if-let [sym (id-map-get inverse-reg x)]
                  {:type :var-ref :id (str sym)}
                  {:type :var-ref :id (str (symbol x))})
           :cljs nil)

        ;; Class reference — JVM only
        #?(:clj (class? x) :cljs false)
        #?(:clj {:type :class-ref :name (.getName ^Class x)} :cljs nil)

        ;; Atom — assign unique ID for identity preservation across references.
        ;; If already seen, emit a back-reference to the same ID.
        (and (instance? #?(:clj clojure.lang.Atom :cljs cljs.core/Atom) x) (id-map-has? seen x))
        (id-map-get seen x)

        (instance? #?(:clj clojure.lang.Atom :cljs cljs.core/Atom) x)
        (let [id (str #?(:clj (java.util.UUID/randomUUID) :cljs (random-uuid)))
              back-ref {:type :atom-back-ref :id id}]
          ;; Register back-ref BEFORE recursing to break cycles
          (id-map-put! seen x back-ref)
          {:type :atom-ref :id id :val (replace-unserializable @x inverse-reg seen)})

        ;; Namespace object — serialize as symbol (JVM only)
        #?(:clj (instance? clojure.lang.Namespace x) :cljs false)
        #?(:clj {:type :ns-ref :name (str (.getName ^clojure.lang.Namespace x))} :cljs nil)

        ;; SCI Type (deftype/defrecord) — serialize with full info
        (instance? sci.lang.Type x)
        (let [methods #?(:clj (.-methods ^sci.lang.Type x)
                         :cljs (unchecked-get x "methods$"))
              opts #?(:clj (.-opts ^sci.lang.Type x)
                      :cljs (unchecked-get x "opts$"))]
          (merge {:type :sci-type-ref
                  :name (str x)
                  :fields (mapv str #?(:clj (.-fields ^sci.lang.Type x)
                                       :cljs (unchecked-get x "fields$")))}
                 (when (seq methods)
                   {:methods (reduce-kv (fn [acc k v]
                                          (assoc acc (str k) (replace-unserializable v inverse-reg seen)))
                                        {} methods)})
                 (when (seq opts)
                   {:opts (select-keys opts [:record? :mutable-fields])})))

        ;; Sorted set — preserve ordering by serializing as sorted vector
        (sorted? x)
        (cond
          (set? x) {:type :sorted-set :items (vec x)}
          (map? x) {:type :sorted-map :items (vec (mapcat identity x))}
          :else x)

        ;; Delay — serialize the realized value or the inner fn (for unrealized delays)
        (delay? x)
        (if (realized? x)
          {:type :delay-ref :realized? true
           :val (replace-unserializable @x inverse-reg seen)}
          (let [inner-fn #?(:clj (let [fld (doto (.getDeclaredField clojure.lang.Delay "fn")
                                             (.setAccessible true))]
                                   (.get fld x))
                            :cljs (.-f x))]
            {:type :delay-ref :realized? false
             :fn (replace-unserializable inner-fn inverse-reg seen)}))

        ;; Volatile — serialize current value
        (volatile? x)
        {:type :volatile-ref :val (replace-unserializable @x inverse-reg seen)}

        ;; Any other non-serializable object — store class name for reconstruction
        #?(:clj
           (and (not (or (string? x) (number? x) (keyword? x) (symbol? x)
                         (nil? x) (boolean? x) (map? x) (vector? x)
                         (set? x) (seq? x) (list? x)))
                (not (instance? java.io.Serializable x)))
           ;; In CLJS everything is serializable via pr-str, skip this check
           :cljs false)
        #?(:clj {:type :unserializable :class (str (class x))} :cljs nil)

        ;; Collection/symbol with metadata — wrap so metadata survives serialization.
        ;; postwalk doesn't descend into metadata, and pr-str doesn't print it by default.
        (and #?(:clj (instance? clojure.lang.IObj x)
                :cljs (satisfies? #?(:cljs cljs.core/IMeta) x))
             (some? (meta x))
             (not (fn? x))
             (not #?(:clj (var? x) :cljs false))
             (not (instance? sci.lang.Var x))
             (not (instance? #?(:clj clojure.lang.Atom :cljs cljs.core/Atom) x))
             #?(:clj (not (instance? clojure.lang.Namespace x)) :cljs true))
        {:type :with-meta
         :value (with-meta x nil)
         :meta (replace-unserializable (meta x) inverse-reg seen)}

        :else x))
    data)))

(defn freeze
  "Serialize a suspended or running machine to an EDN string.
   The machine must have :status :suspend or :running."
  [machine]
  (assert (contains? #{:suspend :running} (:status machine))
          (str "Can only freeze a suspended or running machine, got status: " (:status machine)))
  (let [heap (:heap machine)
        inverse-reg (host/inverse-registry heap)
        u-heap (user-heap heap)
        ;; Shared seen map so atoms/fns in user-heap and state get the same IDs
        seen (id-map-new)
        ;; Build the serializable state
        state (-> machine
                  (dissoc :heap-atom :heap :inverse-registry :ctx :ns-atom :current-ns-atom :hierarchy-atom)
                  (assoc :user-heap (replace-unserializable u-heap inverse-reg seen)))
        state (replace-unserializable state inverse-reg seen)]
    (pr-str (assoc state :version 1))))

;; ============================================================
;; Thaw — EDN string → live machine
;; ============================================================

(defn- restore-serialized
  "Walk a data structure, replacing tagged maps back to live objects.
   type-registry is an atom mapping type-name strings to shared sci.lang.Type objects.
   atom-registry is an atom mapping atom IDs to shared atom objects (identity preservation)."
  [data full-heap type-registry atom-registry]
  (walk/postwalk
   (fn [x]
     (if-not (map? x)
       x
       (case (:type x)
         :host-fn-ref
         (let [sym (symbol (:id x))]
           (if-let [entry (get full-heap sym)]
             (:val entry)
             (throw (ex-info (str "Cannot resolve host fn: " (:id x))
                             {:type :sci/error}))))

         :var-ref
         (let [sym (symbol (:id x))]
           (if-let [entry (get full-heap sym)]
             (:val entry)
             (throw (ex-info (str "Cannot resolve var: " (:id x))
                             {:type :sci/error}))))

         ;; Legacy ref format — resolve from heap
         :sci-var-ref
         (let [sym (symbol (:sym x))
               entry (get full-heap sym)]
           (sci.lang/->Var sym
                           (:val entry)
                           (:meta entry)
                           (:dynamic? entry)))

         ;; Inline format — deferred to second pass (val may contain closures)
         :sci-var
         x

         ;; Type constructors — deferred to second pass (need type-obj from heap)
         :type-ctor x
         :map-type-ctor x

         :class-ref
         #?(:clj (Class/forName (:name x))
            :cljs (symbol (:name x)))

         :atom-ref
         (let [a (atom (:val x))]
           (when-let [id (:id x)]
             (swap! atom-registry assoc id a))
           a)

         :atom-back-ref
         (let [id (:id x)]
           (or (get @atom-registry id)
               (let [a (atom nil)]
                 (swap! atom-registry assoc id a)
                 a)))

         :ns-ref
         (let [ns-sym (symbol (:name x))]
           #?(:clj (or (clojure.core/find-ns ns-sym) ns-sym)
              :cljs ns-sym))

         :sorted-set
         (apply sorted-set (:items x))

         :sorted-map
         (apply sorted-map (:items x))

         :delay-ref
         (if (:realized? x)
           (let [v (:val x)] (delay v))
           x) ;; unrealized delay — deferred to wrap-closures (inner fn may be closure map)

         :volatile-ref
         (volatile! (:val x))

         ;; HOF results — deferred to second pass (inner fns may be closure maps)
         :comp-fn x
         :partial-fn x
         :juxt-fn x
         :complement-fn x
         :every-pred-fn x
         :some-fn-fn x
         :memoize-fn x
         :fnil-fn x

         ;; Multimethod — deferred to second pass (methods may contain closures)
         :multimethod
         x

         ;; Self-reference from cycle detection (e.g. multimethod in its own method env)
         :multimethod-self-ref
         x ;; deferred — resolved in wrap-closures pass after heap is assembled

         ;; Protocol dispatch fn — deferred to second pass (needs protocol from heap)
         :protocol-dispatch-ref
         x

         ;; Deftype method fns — deferred to second pass (need machine context)
         :deftype-method x
         :deftype-multi-method x

         ;; SCI Type — create with fields/opts, store raw methods for later wrapping
         :sci-type-ref
         (let [type-name (:name x)
               fields (mapv symbol (or (:fields x) []))
               opts (or (:opts x) {})
               ;; Store raw method maps (still tagged, will be wrapped later)
               methods (reduce-kv (fn [acc k v]
                                    (assoc acc (symbol k) v))
                                  {} (or (:methods x) {}))]
           (if-let [existing (get @type-registry type-name)]
             existing
             (let [t (sci.lang/->Type (symbol type-name) fields {} methods opts)]
               (swap! type-registry assoc type-name t)
               t)))

         :unknown-fn
         (fn [& _args]
           (throw (ex-info (str "Cannot call deserialized unknown fn: " (:class x))
                           {:type :sci/error})))

         ;; Closure — rebuild into callable IFn
         :closure
         (let [closure-map x]
           ;; We need a minimal machine context for make-callable-closure.
           ;; The full heap will be set on the machine after thaw.
           ;; For now, return the plain map — we'll wrap closures in a second pass.
           closure-map)

         ;; Collection/symbol with preserved metadata
         :with-meta
         (with-meta (:value x) (:meta x))

         ;; Not a tagged map, return as-is
         x)))
   data))

(defn- wrap-closures
  "Second pass: walk the data and wrap any remaining :closure maps into callable IFns,
   and reconstruct protocol dispatch fns from their references."
  [data machine]
  (walk/postwalk
   (fn [x]
     (if-not (map? x)
       x
       (case (:type x)
         :closure
         (step/make-callable-closure x machine)

         :comp-fn
         (let [fns (:fns x)
               sci-comp (:val (get (:heap machine) 'clojure.core/comp))]
           (apply sci-comp fns))

         :partial-fn
         (let [f (:f x)
               args (:args x)
               sci-partial (:val (get (:heap machine) 'clojure.core/partial))]
           (apply sci-partial f args))

         :juxt-fn
         (let [fns (:fns x)
               sci-juxt (:val (get (:heap machine) 'clojure.core/juxt))]
           (apply sci-juxt fns))

         :complement-fn
         (let [sci-complement (:val (get (:heap machine) 'clojure.core/complement))]
           (sci-complement (:f x)))

         :every-pred-fn
         (let [fns (:fns x)
               sci-every-pred (:val (get (:heap machine) 'clojure.core/every-pred))]
           (apply sci-every-pred fns))

         :some-fn-fn
         (let [fns (:fns x)
               sci-some-fn (:val (get (:heap machine) 'clojure.core/some-fn))]
           (apply sci-some-fn fns))

         :memoize-fn
         (let [sci-memoize (:val (get (:heap machine) 'clojure.core/memoize))]
           (sci-memoize (:f x)))

         :fnil-fn
         (let [sci-fnil (:val (get (:heap machine) 'clojure.core/fnil))]
           (apply sci-fnil (:f x) (:defaults x)))

         :delay-ref
         ;; Unrealized delay — inner fn is now a wrapped closure
         (let [inner-fn (:fn x)]
           #?(:clj (clojure.lang.Delay. ^clojure.lang.IFn inner-fn)
              :cljs (cljs.core/Delay. inner-fn nil)))

         :multimethod
         (let [mm-name (symbol (:name x))
               dispatch-fn (:dispatch-fn x)
               mm (step/make-multimethod mm-name dispatch-fn nil)]
           ;; Methods may still contain closure maps — wrap them first
           (let [wrapped-methods (reduce-kv
                                  (fn [acc k v]
                                    (assoc acc k
                                           (if (and (map? v) (= :closure (:type v)))
                                             (step/make-callable-closure v machine)
                                             v)))
                                  {} (:methods x))]
             (reset! (:methods (meta mm)) wrapped-methods)
             (reset! (:prefer-table (meta mm)) (:prefer-table x)))
           mm)

         :protocol-dispatch-ref
         (let [proto-sym (symbol (:protocol x))
               method-sym (symbol (:method x))
               heap (:heap machine)
               proto-entry (get heap proto-sym)
               proto (:val proto-entry)
               ns-sym (:ns proto)
               proto-name (:name proto)]
           (step/make-protocol-dispatch-fn proto method-sym ns-sym proto-name))

         :deftype-method
         (let [ns-sym (symbol (:ns-sym x))
               fields (mapv symbol (:fields x))
               params (mapv symbol (:params x))
               body (:body x)
               mutable-fields (mapv symbol (:mutable-fields x))]
           (step/make-deftype-method-fn machine ns-sym fields params body mutable-fields))

         :deftype-multi-method
         (let [fns (mapv (fn [entry]
                           {:fn (:fn entry) :arity (:arity entry)})
                         (:fns x))]
           (if (= 1 (count fns))
             (:fn (first fns))
             (with-meta
               (fn [& args]
                 (let [n (count args)
                       match (first (filter #(= n (:arity %)) fns))]
                   (if match
                     (apply (:fn match) args)
                     (throw (ex-info (str "No matching arity for deftype method, got " n " args")
                                     {:type :sci/error})))))
               {:sci/deftype-multi-method true
                :sci/method-fns fns})))

         :multimethod-self-ref
         (let [mm-name (symbol (:name x))
               heap (:heap machine)
               ;; Find the multimethod in the heap by name
               entry (some (fn [[k v]]
                             (when (= (name k) (name mm-name))
                               v))
                           heap)]
           (if entry
             (:val entry)
             (throw (ex-info (str "Cannot resolve multimethod self-ref: " mm-name)
                             {:type :sci/error}))))

         :type-ctor
         (let [type-name (:type-name x)
               type-obj (get @(:type-registry machine) type-name)
               fields (:fields x)
               mutable-kws (set (:mutable-fields x))]
           (with-meta
             (if (:record? x)
               (fn [& args]
                 (with-meta (zipmap fields args)
                   {:type type-obj :sci.impl/record true}))
               (fn [& args]
                 (with-meta (zipmap fields
                                    (map-indexed (fn [i val]
                                                   (if (contains? mutable-kws (nth fields i))
                                                     (atom val)
                                                     val))
                                                 args))
                   {:type type-obj})))
             {:sci/type-ctor true :sci/type-name type-name
              :sci/fields fields :sci/record? (:record? x)
              :sci/mutable-fields mutable-kws}))

         :map-type-ctor
         (let [type-name (:type-name x)
               type-obj (get @(:type-registry machine) type-name)
               fields (:fields x)]
           (with-meta
             (fn [m]
               (with-meta (merge (zipmap fields (repeat nil)) m)
                 {:type type-obj :sci.impl/record true}))
             {:sci/map-type-ctor true :sci/type-name type-name :sci/fields fields}))

         ;; SCI Var — val may contain a closure or deferred type that needs wrapping
         :sci-var
         (let [v (:val x)
               wrapped-val (cond
                             (and (map? v) (= :closure (:type v)))
                             (step/make-callable-closure v machine)

                             (and (map? v) (#{:type-ctor :map-type-ctor} (:type v)))
                             (let [type-name (:type-name v)
                                   type-obj (get @(:type-registry machine) type-name)
                                   fields (:fields v)]
                               (if (= :type-ctor (:type v))
                                 (let [mutable-kws (set (:mutable-fields v))]
                                   (with-meta
                                     (if (:record? v)
                                       (fn [& args]
                                         (with-meta (zipmap fields args)
                                           {:type type-obj :sci.impl/record true}))
                                       (fn [& args]
                                         (with-meta (zipmap fields
                                                            (map-indexed (fn [i val]
                                                                           (if (contains? mutable-kws (nth fields i))
                                                                             (atom val)
                                                                             val))
                                                                         args))
                                           {:type type-obj})))
                                     {:sci/type-ctor true
                                      :sci/type-name type-name
                                      :sci/fields fields
                                      :sci/record? (:record? v)
                                      :sci/mutable-fields mutable-kws}))
                                 ;; map->ctor
                                 (with-meta
                                   (fn [m]
                                     (with-meta (merge (zipmap fields (repeat nil)) m)
                                       {:type type-obj :sci.impl/record true}))
                                   {:sci/map-type-ctor true
                                    :sci/type-name type-name
                                    :sci/fields fields})))

                             :else v)]
           (sci.lang/->Var (symbol (:sym x))
                           wrapped-val
                           (:meta x)
                           (:dynamic? x)))

         ;; Protocol map — wrap closures inside :impls atom (postwalk can't reach into atoms)
         (if (= :sci/protocol (:type x))
           (let [impls-atom (:impls x)]
             (when (instance? #?(:clj clojure.lang.Atom :cljs cljs.core/Atom) impls-atom)
               (let [impls @impls-atom
                     wrapped (reduce-kv
                              (fn [acc type-key methods]
                                (assoc acc type-key
                                       (reduce-kv
                                        (fn [macc mname mfn]
                                          (assoc macc mname
                                                 (cond
                                                   (and (map? mfn) (= :closure (:type mfn)))
                                                   (step/make-callable-closure mfn machine)
                                                   (and (map? mfn) (= :deftype-method (:type mfn)))
                                                   (step/make-deftype-method-fn
                                                    machine (symbol (:ns-sym mfn))
                                                    (mapv symbol (:fields mfn))
                                                    (mapv symbol (:params mfn))
                                                    (:body mfn)
                                                    (mapv symbol (:mutable-fields mfn)))
                                                   (and (map? mfn) (= :deftype-multi-method (:type mfn)))
                                                   (let [fns (mapv (fn [entry]
                                                                     (let [f (:fn entry)]
                                                                       {:fn (if (and (map? f) (= :deftype-method (:type f)))
                                                                              (step/make-deftype-method-fn
                                                                               machine (symbol (:ns-sym f))
                                                                               (mapv symbol (:fields f))
                                                                               (mapv symbol (:params f))
                                                                               (:body f)
                                                                               (mapv symbol (:mutable-fields f)))
                                                                              f)
                                                                        :arity (:arity entry)}))
                                                                   (:fns mfn))]
                                                     (if (= 1 (count fns))
                                                       (:fn (first fns))
                                                       (fn [& args]
                                                         (let [n (count args)
                                                               match (first (filter #(= n (:arity %)) fns))]
                                                           (if match
                                                             (apply (:fn match) args)
                                                             (throw (ex-info (str "No matching arity, got " n " args")
                                                                             {:type :sci/error})))))))
                                                   :else mfn)))
                                        {} methods)))
                              {} impls)]
                 (reset! impls-atom wrapped)))
             x)
           x))))
   data))

(defn- fixup-type-methods
  "Wrap raw deftype method maps in type-registry into callable fns.
   Returns an identity map of old-Type → new-Type for replacement."
  [type-registry machine]
  (let [replacements (id-map-new)]
    (doseq [[type-name old-type] @type-registry]
      (let [methods #?(:clj (.-methods ^sci.lang.Type old-type)
                       :cljs (unchecked-get old-type "methods$"))]
        (when (some (fn [[_ v]] (and (map? v) (#{:deftype-method :deftype-multi-method} (:type v))))
                    methods)
          (let [wrapped-methods
                (reduce-kv
                 (fn [acc k v]
                   (assoc acc k
                          (cond
                            (and (map? v) (= :deftype-method (:type v)))
                            (step/make-deftype-method-fn
                             machine (symbol (:ns-sym v))
                             (mapv symbol (:fields v))
                             (mapv symbol (:params v))
                             (:body v)
                             (mapv symbol (:mutable-fields v)))

                            (and (map? v) (= :deftype-multi-method (:type v)))
                            (let [fns (mapv (fn [entry]
                                              (let [f (:fn entry)]
                                                {:fn (if (and (map? f) (= :deftype-method (:type f)))
                                                       (step/make-deftype-method-fn
                                                        machine (symbol (:ns-sym f))
                                                        (mapv symbol (:fields f))
                                                        (mapv symbol (:params f))
                                                        (:body f)
                                                        (mapv symbol (:mutable-fields f)))
                                                       f)
                                                 :arity (:arity entry)}))
                                            (:fns v))]
                              (if (= 1 (count fns))
                                (:fn (first fns))
                                (fn [& args]
                                  (let [n (count args)
                                        match (first (filter #(= n (:arity %)) fns))]
                                    (if match
                                      (apply (:fn match) args)
                                      (throw (ex-info (str "No matching arity, got " n " args")
                                                      {:type :sci/error})))))))

                            :else v)))
                 {} methods)
                new-type (sci.lang/->Type
                          #?(:clj (.-name ^sci.lang.Type old-type)
                             :cljs (unchecked-get old-type "name$"))
                          #?(:clj (.-fields ^sci.lang.Type old-type)
                             :cljs (unchecked-get old-type "fields$"))
                          #?(:clj (.-protocols ^sci.lang.Type old-type)
                             :cljs (unchecked-get old-type "protocols$"))
                          wrapped-methods
                          #?(:clj (.-opts ^sci.lang.Type old-type)
                             :cljs (unchecked-get old-type "opts$")))]
            (id-map-put! replacements old-type new-type)
            (swap! type-registry assoc type-name new-type)))))
    replacements))

(defn- replace-types
  "Walk data replacing old Type objects with new ones (both as values, in metadata,
   and in protocol impls atom keys)."
  [data replacements]
  (if (id-map-empty? replacements)
    data
    (walk/postwalk
     (fn [x]
       (cond
         ;; Direct Type reference (e.g. in :types map)
         (and (instance? sci.lang.Type x) (id-map-has? replacements x))
         (id-map-get replacements x)

         ;; Type reference in metadata (e.g. deftype instances)
         (and #?(:clj (instance? clojure.lang.IObj x)
                 :cljs (satisfies? #?(:cljs cljs.core/IMeta) x))
              (some? (clojure.core/meta x)))
         (let [m (clojure.core/meta x)
               t (:type m)]
           (if (and (instance? sci.lang.Type t) (id-map-has? replacements t))
             (with-meta x (assoc m :type (id-map-get replacements t)))
             x))

         ;; Protocol impls atom — update Type keys
         (and (map? x) (= :sci/protocol (:type x)))
         (when-let [impls-atom (:impls x)]
           (when (instance? #?(:clj clojure.lang.Atom :cljs cljs.core/Atom) impls-atom)
             (let [impls @impls-atom
                   needs-update? (some #(id-map-has? replacements %) (keys impls))]
               (when needs-update?
                 (reset! impls-atom
                         (reduce-kv (fn [acc k v]
                                      (let [new-k (if (id-map-has? replacements k)
                                                    (id-map-get replacements k) k)]
                                        (assoc acc new-k v)))
                                    {} impls)))))
           x)

         :else x))
     data)))

(defn thaw
  "Deserialize an EDN string back into a live (suspended) machine."
  [edn-str]
  (let [state (edn/read-string edn-str)
        ;; Shared registries — ensure identity preservation across references
        type-registry (atom {})
        atom-registry (atom {})
        ;; Rebuild the full heap: host defaults + user heap
        host-heap (host/default-heap)
        raw-user-heap (:user-heap state)
        ;; ---- First pass on both user-heap and state ----
        restored-user-heap (restore-serialized raw-user-heap host-heap type-registry atom-registry)
        full-heap (merge host-heap restored-user-heap)
        heap-atom (atom full-heap)
        restored-state (-> state
                           (dissoc :user-heap :version)
                           (restore-serialized full-heap type-registry atom-registry))
        ;; Build a minimal machine for closure wrapping
        minimal-machine {:heap full-heap
                         :heap-atom heap-atom
                         :ns (or (:ns state) {})
                         :current-ns (or (:current-ns state) 'user)
                         :permissions (:permissions state)
                         :type-registry type-registry}
        ;; Fix up type methods (registry now populated from both passes)
        type-replacements (fixup-type-methods type-registry minimal-machine)
        ;; ---- Second pass on both ----
        wrapped-user-heap (wrap-closures restored-user-heap minimal-machine)
        full-heap (merge host-heap wrapped-user-heap)
        _ (reset! heap-atom full-heap)
        minimal-machine (assoc minimal-machine :heap full-heap)
        restored-state (wrap-closures restored-state minimal-machine)
        ;; Replace old Type refs with method-populated Types in metadata and values
        restored-state (replace-types restored-state type-replacements)
        full-heap (replace-types full-heap type-replacements)
        _ (reset! heap-atom full-heap)]
    (-> restored-state
        (assoc :heap full-heap
               :heap-atom heap-atom))))
