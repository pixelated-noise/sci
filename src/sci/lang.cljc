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
             clojure.lang.IFn
             (invoke [_] (val))
             (invoke [_ a] (val a))
             (invoke [_ a b] (val a b))
             (invoke [_ a b c] (val a b c))
             (invoke [_ a b c d] (val a b c d))
             (invoke [_ a b c d e] (val a b c d e))
             (invoke [_ a b c d e f] (val a b c d e f))
             (invoke [_ a b c d e f g] (val a b c d e f g))
             (applyTo [_ args] (clojure.lang.AFn/applyToHelper val args))
             Object
             (toString [_] (str "#'" (or (:sci.impl/var-sym meta-map) sym)))]
      :cljs [IDeref
             (-deref [_] val)
             IMeta
             (-meta [_] meta-map)
             IFn
             (-invoke [_] (val))
             (-invoke [_ a] (val a))
             (-invoke [_ a b] (val a b))
             (-invoke [_ a b c] (val a b c))
             IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str "#'" sym)))]))

#?(:clj
   (defmethod print-method Var [^Var v ^java.io.Writer w]
     (.write w (str "#'" (or (:sci.impl/var-sym (.-meta-map v)) (.-sym v))))))

;; Unbound — represents an unbound SCI var
(deftype Unbound [sym]
  #?@(:clj [Object
             (toString [_] (str "Unbound: #'" sym))]
      :cljs [IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str "Unbound: #'" sym)))]))

#?(:clj
   (defn ^:static cloneThreadBindings
     "Clone the current thread bindings."
     []
     {}))
