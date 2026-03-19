(ns sci.impl.vars
  "SCI var implementation.")

(defn unqualify-symbol
  "Remove namespace qualification from a symbol."
  [sym]
  (if (qualified-symbol? sym)
    (symbol (name sym))
    sym))
