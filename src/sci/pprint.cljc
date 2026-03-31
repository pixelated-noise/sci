(ns sci.pprint
  "Pretty-printing support for SCI."
  #?(:clj (:require [clojure.pprint :as pp]
                     [sci.lang])))

;; Register pprint simple-dispatch for SCI Var — print as #'ns/name
#?(:clj
   (.addMethod ^clojure.lang.MultiFn pp/simple-dispatch sci.lang.Var
     (fn [^sci.lang.Var v]
       (print (str "#'" (or (:sci.impl/var-sym (.-meta-map v)) (.-sym v)))))))

;; Register pprint simple-dispatch for IPersistentMap to handle SCI type instances
;; SCI types are maps with {:type <sci.lang.Type>} metadata
;; This lets (defmethod simple-dispatch Foo ...) work for SCI types
#?(:clj
   (let [original-map-dispatch (get (.getMethodTable ^clojure.lang.MultiFn pp/simple-dispatch)
                                    clojure.lang.IPersistentMap)]
     (.addMethod ^clojure.lang.MultiFn pp/simple-dispatch clojure.lang.IPersistentMap
       (fn [m]
         (if-let [type-obj (when-let [md (clojure.core/meta m)]
                             (when (instance? sci.lang.Type (:type md))
                               (:type md)))]
           ;; Check if there's a custom dispatch registered for this SCI type
           (let [method-table (.getMethodTable ^clojure.lang.MultiFn pp/simple-dispatch)
                 custom-fn (get method-table type-obj)]
             (if custom-fn
               (custom-fn m)
               ;; No custom dispatch — use original map dispatch
               (if original-map-dispatch
                 (original-map-dispatch m)
                 (pr m))))
           ;; Not a SCI type — use original dispatch
           (if original-map-dispatch
             (original-map-dispatch m)
             (pr m)))))))

(defn pprint
  "Pretty-print a value."
  [x]
  #?(:clj (pp/pprint x)
     :cljs (println x)))

(defn cl-format
  "Common Lisp-style format."
  [writer fmt & args]
  #?(:clj (apply pp/cl-format writer fmt args)
     :cljs (apply println fmt args)))
