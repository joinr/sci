(ns sci.impl.fns
  {:no-doc true}
  (:require [sci.impl.types :as t]))

(defn throw-arity [fn-name macro? args]
  (throw (new #?(:clj Exception
                 :cljs js/Error)
              (let [actual-count (if macro? (- (count args) 2)
                                     (count args))]
                (str "Cannot call " fn-name " with " actual-count " arguments")))))

(deftype Recur #?(:clj [val]
                  :cljs [val])
  t/IBox
  (getVal [this] val))


(defn fast-second [xs]
  (some-> ^clojure.lang.ISeq xs
          ^clojure.lang.ISeq (.next)
          (.first)))

(defn parse-fn-args+body
  [^clojure.lang.Associative ctx interpret eval-do*
   {:sci.impl/keys [fixed-arity var-arg-name params body] :as _m}
   fn-name macro? with-meta?]
  (let [min-var-args-arity (when var-arg-name fixed-arity)
        ;;lifted out, probably minor, but on repeat invocations it'll
        ;;add up...
        return (if (= 1 (count body))
                 (let [x (first body)]
                   #(interpret % x)
                   #(eval-do* % body)))
        ;;lift out of the function body in case of
        ;;recur...
        init-params (seq params) ;;should be able to unfold this.....
        f (fn run-fn [& args]
            (let [;; tried making bindings a transient, but saw no perf improvement (see #246)
                  bindings (.get ^java.util.Map ctx :bindings)
                  bindings
                  (loop [^clojure.lang.ISeq args* (seq args) ;;seems avoidable...
                         ^clojure.lang.ISeq params init-params
                         ^clojure.lang.Associative ret bindings]
                    (if params
                      (let [fp (.first params)]
                        (if (identical? #_= '& fp) ;;should be faster
                          (.assoc ret (fast-second #_second params) args*)
                          (do
                            (when-not args*
                              (throw-arity fn-name macro? args))
                            (recur (.next args*) (.next params)
                                   (.assoc ret fp (.first args*))))))
                      (do
                        (when args*
                          (throw-arity fn-name macro? args))
                        ret)))

                  ctx (.assoc ctx :bindings bindings)
                  ;;Doesn't need to be in here does it?
                  ret (return ctx)
                  ;; m (meta ret)
                  recur? (instance? Recur ret)]
              (if recur?
                (let [recur-val (t/getVal ret)]
                  (if min-var-args-arity
                    (let [[fixed-args [rest-args]]
                          [(subvec recur-val 0 min-var-args-arity)
                           (subvec recur-val min-var-args-arity)]]
                      (recur (into fixed-args rest-args)))
                    (recur recur-val)))
                ret)))]
    (if with-meta?
      (with-meta
        f
        (if min-var-args-arity
          {:sci.impl/min-var-args-arity min-var-args-arity}
          {:sci.impl/fixed-arity fixed-arity}))
      f)))

(defn lookup-by-arity [arities arity]
  (some (fn [f]
          (let [{:sci.impl/keys [fixed-arity min-var-args-arity]} (meta f)]
            (when (or (= arity fixed-arity )
                      (and min-var-args-arity
                           (>= arity min-var-args-arity)))
              f))) arities))

(defn eval-fn [ctx interpret eval-do* {:sci.impl/keys [fn-bodies fn-name
                                                       var] :as f}]
  (let [macro? (:sci/macro f)
        self-ref (atom nil)
        ctx (if (and (not var)
                     fn-name)
              (assoc-in ctx [:bindings fn-name]
                        (fn call-self [& args]
                          (apply @self-ref args)))
              ctx)
        single-arity? (= 1 (count fn-bodies))
        f (if single-arity?
            (parse-fn-args+body ctx interpret eval-do* (first fn-bodies) fn-name macro? false)
            (let [arities (map #(parse-fn-args+body ctx interpret eval-do* % fn-name macro? true) fn-bodies)]
              (fn [& args]
                (let [arg-count (count args)]
                  (if-let [f (lookup-by-arity arities arg-count)]
                    (apply f args)
                    (throw (new #?(:clj Exception
                                   :cljs js/Error)
                                (let [actual-count (if macro? (- arg-count 2)
                                                       arg-count)]
                                  (str "Cannot call " fn-name " with " actual-count " arguments")))))))))
        f (if macro?
            (vary-meta
             f
             #(assoc % :sci/macro macro?))
            f)]
    (reset! self-ref f)
    f))

;;;; Scratch

(comment
  )
