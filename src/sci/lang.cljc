(ns sci.lang
  "Core SCI types: Var, Namespace, Type."
  (:require [sci.impl.types :as types]))

;; Type — represents deftype/defrecord types in SCI
(deftype Type [name fields protocols methods opts]
  types/HasName
  (getName [_] (str name))
  #?@(:clj [Object
             (toString [_] (str name))]
      :cljs [IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str name)))]))

;; Namespace — represents an SCI namespace
(defrecord Namespace [name aliases refers imports types])

;; Var — represents an SCI var
(deftype Var [sym val meta-map dynamic?]
  #?@(:clj [clojure.lang.IDeref
             (deref [_] val)
             clojure.lang.IMeta
             (meta [_] meta-map)
             Object
             (toString [_] (str "#'" sym))]
      :cljs [IDeref
             (-deref [_] val)
             IMeta
             (-meta [_] meta-map)
             IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str "#'" sym)))]))

#?(:clj
   (defn ^:static cloneThreadBindings
     "Clone the current thread bindings."
     []
     {}))
