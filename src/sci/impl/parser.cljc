(ns sci.impl.parser
  "Parser — wraps edamame."
  (:require [edamame.core :as edamame]))

(defn parse-string
  "Parse a string into a Clojure form."
  ([ctx s]
   (edamame/parse-string s {:all true
                             :read-cond :allow
                             :features #{:clj}
                             :fn true
                             :quote true
                             :var true
                             :deref true
                             :regex true})))
