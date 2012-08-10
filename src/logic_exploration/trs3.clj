(ns logic_exploration.trs3
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic))


(run* [q]
  (membero q [1 2 3 4])
  (membero q (range 2 10))
  (!= q 3))

; core.logic's conde is condi, so can't depend on order, so the following doesn't work like it does in TRS page 44
(defn memberrevo [x l]
  (conde
    [s# (fresh [d] (resto l d) (memberrevo x d))]
    [s# (firsto l x)]
  ))

(run* [q]
  (membero q '(pasta e fagioli)))
