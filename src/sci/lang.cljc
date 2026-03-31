(ns sci.lang
  "Core SCI types: Var, Namespace, Type."
  #?(:cljs (:refer-clojure :exclude [Namespace Var ->Namespace ->Var]))
  (:require [sci.impl.types :as types]))

;; Type — represents deftype/defrecord types in SCI
(deftype Type [name fields protocols methods opts]
  types/HasName
  (getName [_] (str name))
  #?@(:clj [Object
             (toString [_] (str name))]
      :cljs [Object
             (toString [_] (str name))
             IPrintWithWriter
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
             (toString [_] (str "#'" (or (:sci.impl/var-sym meta-map) sym)))
             (equals [_ other]
               (and (instance? Var other)
                    (= (or (:sci.impl/var-sym meta-map) sym)
                       (or (:sci.impl/var-sym (.-meta-map ^Var other))
                           (.-sym ^Var other)))))
             (hashCode [_]
               (.hashCode (or (:sci.impl/var-sym meta-map) sym)))]
      :cljs [IDeref
             (-deref [_] val)
             IMeta
             (-meta [_] meta-map)
             IFn
             (-invoke [_] (val))
             (-invoke [_ a] (val a))
             (-invoke [_ a b] (val a b))
             (-invoke [_ a b c] (val a b c))
             (-invoke [_ a b c d] (val a b c d))
             (-invoke [_ a b c d e] (val a b c d e))
             (-invoke [_ a b c d e f] (val a b c d e f))
             (-invoke [_ a b c d e f g] (val a b c d e f g))
             Object
             (toString [_] (str "#'" (or (:sci.impl/var-sym meta-map) sym)))
             IEquiv
             (-equiv [_ other]
               (and (instance? Var other)
                    (= (or (:sci.impl/var-sym meta-map) sym)
                       (or (:sci.impl/var-sym (.-meta-map ^Var other))
                           (.-sym ^Var other)))))
             IHash
             (-hash [_] (hash (or (:sci.impl/var-sym meta-map) sym)))
             IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str "#'" (or (:sci.impl/var-sym meta-map) sym))))]))

#?(:clj
   (defmethod print-method Var [^Var v ^java.io.Writer w]
     (.write w (str "#'" (or (:sci.impl/var-sym (.-meta-map v)) (.-sym v))))))

;; DynamicVar — wraps an atom as thread-local storage for a dynamic SCI var.
;; Distinct from plain atoms so resolve-symbol can deref it automatically.
;; meta-map stores optional metadata (e.g. {:sci/built-in true}).
(deftype DynamicVar [atom-ref meta-map]
  #?@(:clj [clojure.lang.IDeref
             (deref [_] @atom-ref)
             clojure.lang.IMeta
             (meta [_] meta-map)
             clojure.lang.IAtom
             (reset [_ v] (reset! atom-ref v))
             (swap [_ f] (swap! atom-ref f))
             (swap [_ f a] (swap! atom-ref f a))
             (swap [_ f a b] (swap! atom-ref f a b))
             (swap [_ f a b args] (apply swap! atom-ref f a b args))
             (compareAndSet [_ ov nv] (compare-and-set! atom-ref ov nv))]
      :cljs [IDeref
             (-deref [_] @atom-ref)
             IMeta
             (-meta [_] meta-map)
             IReset
             (-reset! [_ v] (reset! atom-ref v))
             ISwap
             (-swap! [_ f] (swap! atom-ref f))
             (-swap! [_ f a] (swap! atom-ref f a))
             (-swap! [_ f a b] (swap! atom-ref f a b))
             (-swap! [_ f a b xs] (apply swap! atom-ref f a b xs))]))

;; Unbound — represents an unbound SCI var
(deftype Unbound [sym]
  #?@(:clj [Object
             (toString [_] (str "Unbound: #'" sym))]
      :cljs [Object
             (toString [_] (str "Unbound: #'" sym))
             IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str "Unbound: #'" sym)))]))

#?(:clj
   (defn ^:static cloneThreadBindings
     "Clone the current thread bindings."
     []
     {}))
