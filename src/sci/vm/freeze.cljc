(ns sci.vm.freeze
  "Freeze (serialize) and thaw (deserialize) suspended VM machines."
  (:require [clojure.walk :as walk]
            [clojure.edn :as edn]
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
      with serializable tagged maps."
     [data inverse-reg]
     (walk/postwalk
      (fn [x]
        (cond
          ;; SCI closure (IFn with :sci/closure metadata)
          (and (fn? x) (:sci/closure (meta x)))
          (let [closure-map (meta x)]
            ;; Return the plain closure map (already data), minus :sci/closure marker
            (dissoc closure-map :sci/closure))

          ;; comp result — carries :sci/comp-fns metadata
          (and (fn? x) (:sci/comp-fns (meta x)))
          {:type :comp-fn
           :fns (mapv #(replace-unserializable % inverse-reg)
                      (:sci/comp-fns (meta x)))}

          ;; partial result — carries :sci/partial-f and :sci/partial-args metadata
          (and (fn? x) (:sci/partial-f (meta x)))
          (let [m (meta x)]
            {:type :partial-fn
             :f (replace-unserializable (:sci/partial-f m) inverse-reg)
             :args (mapv #(replace-unserializable % inverse-reg)
                         (:sci/partial-args m))})

          ;; Host fn — look up in inverse registry
          (fn? x)
          (if-let [sym (.get ^java.util.IdentityHashMap inverse-reg x)]
            {:type :host-fn-ref :id (str sym)}
            ;; Unknown fn — try to preserve as best we can
            {:type :unknown-fn :class (str (class x))})

          ;; SCI Var
          (instance? sci.lang.Var x)
          {:type :sci-var-ref :sym (str (.-sym ^sci.lang.Var x))}

          ;; Var (host Clojure var)
          (var? x)
          (if-let [sym (.get ^java.util.IdentityHashMap inverse-reg x)]
            {:type :var-ref :id (str sym)}
            {:type :var-ref :id (str (symbol x))})

          ;; Class reference
          (class? x)
          {:type :class-ref :name (.getName ^Class x)}

          ;; Atom (from multimethods, protocols, etc.)
          (instance? clojure.lang.Atom x)
          {:type :atom-ref :val (replace-unserializable @x inverse-reg)}

          ;; Namespace object — serialize as symbol
          (instance? clojure.lang.Namespace x)
          {:type :ns-ref :name (str (.getName ^clojure.lang.Namespace x))}

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
           :meta (replace-unserializable (meta x) inverse-reg)}

          :else x))
      data)))

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
           ;; Build the serializable state
           state (-> machine
                     (dissoc :heap-atom :heap :inverse-registry :ctx :ns-atom :current-ns-atom :hierarchy-atom)
                     (assoc :user-heap (replace-unserializable u-heap inverse-reg)))
           state (replace-unserializable state inverse-reg)]
       (pr-str (assoc state :version 1)))
     :cljs
     (throw (ex-info "freeze is not yet supported in ClojureScript" {}))))

;; ============================================================
;; Thaw — EDN string → live machine
;; ============================================================

#?(:clj
   (defn- restore-serialized
     "Walk a data structure, replacing tagged maps back to live objects."
     [data full-heap]
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

            :sci-var-ref
            (let [sym (symbol (:sym x))
                  entry (get full-heap sym)]
              (sci.lang/->Var sym
                              (:val entry)
                              (:meta entry)
                              (:dynamic? entry)))

            :class-ref
            (Class/forName (:name x))

            :atom-ref
            (atom (:val x))

            :ns-ref
            (let [ns-sym (symbol (:name x))]
              (or (clojure.core/find-ns ns-sym) ns-sym))

            :comp-fn
            (let [fns (:fns x)
                  sci-comp (:val (get full-heap 'clojure.core/comp))]
              (apply sci-comp fns))

            :partial-fn
            (let [f (:f x)
                  args (:args x)
                  sci-partial (:val (get full-heap 'clojure.core/partial))]
              (apply sci-partial f args))

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
     "Second pass: walk the data and wrap any remaining :closure maps into callable IFns."
     [data machine]
     (walk/postwalk
      (fn [x]
        (if (and (map? x) (= :closure (:type x)))
          (step/make-callable-closure x machine)
          x))
      data)))

(defn thaw
  "Deserialize an EDN string back into a live (suspended) machine."
  [edn-str]
  #?(:clj
     (let [state (edn/read-string edn-str)
           ;; Rebuild the full heap: host defaults + user heap
           host-heap (host/default-heap)
           raw-user-heap (:user-heap state)
           ;; First pass: restore host-fn-refs, var-refs, class-refs, atoms in user heap
           restored-user-heap (restore-serialized raw-user-heap host-heap)
           full-heap (merge host-heap restored-user-heap)
           heap-atom (atom full-heap)
           ;; Build a minimal machine for closure wrapping
           minimal-machine {:heap full-heap
                            :heap-atom heap-atom
                            :ns (or (:ns state) {})
                            :current-ns (or (:current-ns state) 'user)
                            :permissions (:permissions state)}
           ;; Restore the rest of the machine state (stack, env, bindings, etc.)
           restored-state (-> state
                              (dissoc :user-heap :version)
                              (restore-serialized full-heap))
           ;; Second pass: wrap closures (they need the machine context)
           restored-state (wrap-closures restored-state minimal-machine)]
       (-> restored-state
           (assoc :heap full-heap
                  :heap-atom heap-atom)))
     :cljs
     (throw (ex-info "thaw is not yet supported in ClojureScript" {}))))
