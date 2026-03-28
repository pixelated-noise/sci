(ns sci.vm.host
  "Host function registry — wraps clojure.core and other namespaces
   so interpreted code can call them directly."
  (:require [clojure.string :as str]
            [clojure.set]
            [clojure.walk]
            [clojure.edn]
            [clojure.repl]))

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
                is-macro? (:macro m)]
            (assoc acc qualified {:val (if is-macro? v (deref v))
                                  :meta (select-keys m [:name :ns :macro :doc :arglists])
                                  :macro? is-macro?
                                  :dynamic? (:dynamic m)})))
        {}
        publics))
     :cljs {}))

(def default-namespaces
  '[clojure.core clojure.string clojure.set clojure.walk clojure.edn clojure.repl])

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
      (add-private-vars)))

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

(defn default-ns-table
  "Build the default namespace table."
  []
  (reduce (fn [t ns-sym]
            (assoc t ns-sym {:aliases {} :refers {} :imports {}}))
          {'user {:aliases {} :refers {} :imports {}}}
          default-namespaces))
