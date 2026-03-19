(ns sci.pprint
  "Pretty-printing support for SCI."
  #?(:clj (:require [clojure.pprint :as pp])))

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
