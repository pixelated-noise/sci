(ns sci.vm.freeze
  "Freeze (serialize) and thaw (deserialize) suspended VM machines."
  (:require [clojure.walk :as walk]
            [clojure.edn :as edn]
            [sci.lang]
            [sci.vm.host :as host]
            [sci.vm.machine :as m]
            #?(:clj [sci.vm.step :as step])))

;; ============================================================
;; Freeze — machine → EDN string
;; ============================================================

(def ^:private extra-namespaces
  "Namespaces injected by make-machine-from-ctx (not user-defined, not resolvable by thaw)."
  #{"sci.core" "clojure.lang"})

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

#?(:clj
   (defn- replace-unserializable
     "Walk a data structure, replacing fn objects, vars, classes, and atoms
      with serializable tagged maps. The `seen` IdentityHashMap tracks already-visited
      fn objects to break cycles (e.g. multimethod methods that capture the multimethod in env)."
     ([data inverse-reg]
      (replace-unserializable data inverse-reg (java.util.IdentityHashMap.)))
     ([data inverse-reg ^java.util.IdentityHashMap seen]
      (walk/postwalk
       (fn [x]
         (cond
           ;; Cycle detection — fn already serialized in an outer call
           (and (fn? x) (.containsKey seen x))
           (.get seen x)

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

           ;; Multimethod — carries :sci/multimethod type in metadata
           (and (fn? x) (= :sci/multimethod (:type (meta x))))
           (let [m (meta x)
                 mm-name (str (:name m))
                 ;; Register a self-ref placeholder BEFORE recursing to break cycles
                 self-ref {:type :multimethod-self-ref :name mm-name}
                 _ (.put seen x self-ref)]
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

           ;; Host fn — look up in inverse registry
           (fn? x)
           (if-let [sym (.get ^java.util.IdentityHashMap inverse-reg x)]
             {:type :host-fn-ref :id (str sym)}
             ;; Unknown fn — try to preserve as best we can
             {:type :unknown-fn :class (str (class x))})

           ;; SCI Var — serialize inline (val, meta, dynamic?) so user-heap self-refs work
           (instance? sci.lang.Var x)
           (let [qsym (or (:sci.impl/var-sym (.-meta-map ^sci.lang.Var x))
                          (.-sym ^sci.lang.Var x))]
             {:type :sci-var
              :sym (str qsym)
              :val (replace-unserializable (.-val ^sci.lang.Var x) inverse-reg seen)
              :meta (replace-unserializable (.-meta-map ^sci.lang.Var x) inverse-reg seen)
              :dynamic? (.-dynamic? ^sci.lang.Var x)})

           ;; Var (host Clojure var)
           (var? x)
           (if-let [sym (.get ^java.util.IdentityHashMap inverse-reg x)]
             {:type :var-ref :id (str sym)}
             {:type :var-ref :id (str (symbol x))})

           ;; Class reference
           (class? x)
           {:type :class-ref :name (.getName ^Class x)}

           ;; Atom (from multimethods, protocols, etc.)
           ;; Atom — assign unique ID for identity preservation across references.
           ;; If already seen, emit a back-reference to the same ID.
           (and (instance? clojure.lang.Atom x) (.containsKey seen x))
           (.get seen x)

           (instance? clojure.lang.Atom x)
           (let [id (str (java.util.UUID/randomUUID))
                 back-ref {:type :atom-back-ref :id id}]
             ;; Register back-ref BEFORE recursing to break cycles
             (.put seen x back-ref)
             {:type :atom-ref :id id :val (replace-unserializable @x inverse-reg seen)})

           ;; Namespace object — serialize as symbol
           (instance? clojure.lang.Namespace x)
           {:type :ns-ref :name (str (.getName ^clojure.lang.Namespace x))}

           ;; SCI Type (deftype/defrecord) — serialize by name for heap lookup
           (instance? sci.lang.Type x)
           {:type :sci-type-ref :name (str x)}

           ;; Any other non-serializable object — store class name for reconstruction
           (and (not (or (string? x) (number? x) (keyword? x) (symbol? x)
                         (nil? x) (boolean? x) (map? x) (vector? x)
                         (set? x) (seq? x) (list? x)))
                (not (instance? java.io.Serializable x)))
           {:type :unserializable :class (str (class x))}

           ;; Collection/symbol with metadata — wrap so metadata survives serialization.
           ;; postwalk doesn't descend into metadata, and pr-str doesn't print it by default.
           (and (instance? clojure.lang.IObj x)
                (some? (meta x))
                (not (fn? x))
                (not (var? x))
                (not (instance? sci.lang.Var x))
                (not (class? x))
                (not (instance? clojure.lang.Atom x))
                (not (instance? clojure.lang.Namespace x)))
           {:type :with-meta
            :value (with-meta x nil)
            :meta (replace-unserializable (meta x) inverse-reg seen)}

           :else x))
       data))))

(defn freeze
  "Serialize a suspended machine to an EDN string.
   The machine must have :status :suspend (or :effect)."
  [machine]
  (assert (contains? #{:suspend :effect} (:status machine))
          (str "Can only freeze a suspended machine, got status: " (:status machine)))
  #?(:clj
     (let [heap (:heap machine)
           inverse-reg (host/inverse-registry heap)
           u-heap (user-heap heap)
           ;; Shared seen map so atoms/fns in user-heap and state get the same IDs
           seen (java.util.IdentityHashMap.)
           ;; Build the serializable state
           state (-> machine
                     (dissoc :heap-atom :heap :inverse-registry :ctx :ns-atom :current-ns-atom :hierarchy-atom)
                     (assoc :user-heap (replace-unserializable u-heap inverse-reg seen)))
           state (replace-unserializable state inverse-reg seen)]
       (pr-str (assoc state :version 1)))
     :cljs
     (throw (ex-info "freeze is not yet supported in ClojureScript" {}))))

;; ============================================================
;; Thaw — EDN string → live machine
;; ============================================================

#?(:clj
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
            (Class/forName (:name x))

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
              (or (clojure.core/find-ns ns-sym) ns-sym))

            ;; comp/partial — deferred to second pass (fns may be closure maps)
            :comp-fn x
            :partial-fn x

            ;; Multimethod — deferred to second pass (methods may contain closures)
            :multimethod
            x

            ;; Self-reference from cycle detection (e.g. multimethod in its own method env)
            :multimethod-self-ref
            x ;; deferred — resolved in wrap-closures pass after heap is assembled

            ;; Protocol dispatch fn — deferred to second pass (needs protocol from heap)
            :protocol-dispatch-ref
            x

            ;; SCI Type — create or reuse from type registry
            :sci-type-ref
            (let [type-name (:name x)]
              (if-let [existing (get @type-registry type-name)]
                existing
                (let [t (sci.lang/->Type (symbol type-name) [] {} {} {})]
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
      data)))

#?(:clj
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
                (when (instance? clojure.lang.Atom impls-atom)
                  (let [impls @impls-atom
                        wrapped (reduce-kv
                                 (fn [acc type-key methods]
                                   (assoc acc type-key
                                          (reduce-kv
                                           (fn [macc mname mfn]
                                             (assoc macc mname
                                                    (if (and (map? mfn) (= :closure (:type mfn)))
                                                      (step/make-callable-closure mfn machine)
                                                      mfn)))
                                           {} methods)))
                                 {} impls)]
                    (reset! impls-atom wrapped)))
                x)
              x))))
      data)))

(defn thaw
  "Deserialize an EDN string back into a live (suspended) machine."
  [edn-str]
  #?(:clj
     (let [state (edn/read-string edn-str)
           ;; Shared registries — ensure identity preservation across references
           type-registry (atom {})
           atom-registry (atom {})
           ;; Rebuild the full heap: host defaults + user heap
           host-heap (host/default-heap)
           raw-user-heap (:user-heap state)
           ;; First pass: restore host-fn-refs, var-refs, class-refs, atoms in user heap
           restored-user-heap (restore-serialized raw-user-heap host-heap type-registry atom-registry)
           full-heap (merge host-heap restored-user-heap)
           heap-atom (atom full-heap)
           ;; Build a minimal machine for closure wrapping
           minimal-machine {:heap full-heap
                            :heap-atom heap-atom
                            :ns (or (:ns state) {})
                            :current-ns (or (:current-ns state) 'user)
                            :permissions (:permissions state)
                            :type-registry type-registry}
           ;; Second pass on user-heap: wrap closures and protocol dispatch refs
           wrapped-user-heap (wrap-closures restored-user-heap minimal-machine)
           full-heap (merge host-heap wrapped-user-heap)
           _ (reset! heap-atom full-heap)
           minimal-machine (assoc minimal-machine :heap full-heap)
           ;; Restore the rest of the machine state (stack, env, bindings, etc.)
           restored-state (-> state
                              (dissoc :user-heap :version)
                              (restore-serialized full-heap type-registry atom-registry))
           ;; Second pass on state: wrap closures and protocol dispatch refs
           restored-state (wrap-closures restored-state minimal-machine)]
       (-> restored-state
           (assoc :heap full-heap
                  :heap-atom heap-atom)))
     :cljs
     (throw (ex-info "thaw is not yet supported in ClojureScript" {}))))
