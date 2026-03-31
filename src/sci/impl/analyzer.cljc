(ns sci.impl.analyzer
  "Analyzer — detects constant forms and wraps them in ConstantNode."
  (:require [sci.impl.types :as types]))

(defn- constant-form?
  "Returns true if the form is a compile-time constant (literal or collection of literals)."
  [ctx form]
  (cond
    ;; Symbols might be constant if they resolve to a constant binding
    (symbol? form)
    (let [heap-atom (:heap-atom ctx)
          heap (when heap-atom @heap-atom)
          ;; Try user namespace first, then clojure.core
          qualified (symbol "user" (name form))
          entry (get heap qualified)]
      (when entry
        (let [v (:val entry)]
          (and (some? v)
               (or (number? v) (string? v) (keyword? v) (boolean? v)
                   (nil? v))))))

    ;; Literals are always constant
    (or (number? form) (string? form) (keyword? form) (boolean? form)
        (nil? form))
    true

    ;; Vectors, sets, maps of constants are constant
    (vector? form)
    (every? #(constant-form? ctx %) form)

    (set? form)
    (every? #(constant-form? ctx %) form)

    (map? form)
    (and (every? #(constant-form? ctx %) (keys form))
         (every? #(constant-form? ctx %) (vals form)))

    ;; Everything else (lists/seqs = function calls, etc.) is not constant
    :else false))

(defn- eval-constant
  "Evaluate a constant form by resolving any symbol references."
  [ctx form]
  (cond
    (symbol? form)
    (let [heap @(:heap-atom ctx)
          qualified (symbol "user" (name form))]
      (:val (get heap qualified)))

    (vector? form)
    (mapv #(eval-constant ctx %) form)

    (set? form)
    (set (map #(eval-constant ctx %) form))

    (map? form)
    (into {} (map (fn [[k v]] [(eval-constant ctx k) (eval-constant ctx v)])) form)

    :else form))

(defn analyze
  "Analyze a form. Wraps constant forms in ConstantNode for optimization."
  [ctx form]
  (let [m (meta form)
        meta-constant? (or (nil? m) (constant-form? ctx m))]
    (if (and meta-constant? (constant-form? ctx form))
      (let [v (eval-constant ctx form)]
        (types/->ConstantNode v))
      form)))
