(ns logic_exploration.sherlock
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic)
  (:require [clojure.tools.macro :as macro]
            [clojure.core.logic.arithmetic :as arithmetic]))

(def zebra-map
  (apply hash-map (flatten (map (fn [[n & r]] (map vector r (repeat n)))
    [[0 :norwegian :englishman :spaniard :ukranian :japanese]
    [1 :kools :chesterfields :oldgolds :parliaments :lucky-strikes]
    [2 :milk :tea :oj :coffee]
    [3 :dog :horse :fox :snails]
    [4 :blue :ivory :green :red :yellow]]))))

(def sherlock-map
  (apply hash-map (flatten (map (fn [[n & r]] (map vector r (repeat n)))
                             [[0 :bill :mary :devil ]
                              [1 :red :blue :yellow ]
                              [2 1 2 3]
                              ]))))

(def col-map sherlock-map)

(def game-rows (inc (apply max (vals col-map))))
; FIXME
(def game-cols 3)

(defn make-col
  ([x] (let [xp (col-map x)]
       (println x xp)
      (vec (for [i (range game-rows)] (if (= i xp) x (lvar))))))
  ([x y] (let [xp (col-map x) yp (col-map y)]
       (println x xp y yp)
      (vec (for [i (range game-rows)] (condp = i xp x yp y (lvar))))))
  ([x y z] (let [xp (col-map x) yp (col-map y) zp (col-map z)]
       (println x xp y yp z zp)
      (vec (for [i (range game-rows)] (condp = i xp x yp y zp z (lvar)))))))

(defn memo [x l out]
  (conda
    [(emptyo l) s#]
    [(firsto l x) (== l out)]
    [s# (fresh [d] (resto l d) (memo x d out))]))

(defn nonmembero
  "A relation where l is a collection, such that x is not an element of l"
  [x l]
  (fresh [m]
    (memo x l m)
    (emptyo m)))

(run* [q]
  (fresh [m] (memo :spoo [:bar :foo :baz] q))
  )

(run* [q]
  (nonmembero :spoo [:foo :bar :spoo])
  (== q true))

(run* [q]
  (== q ()))
(defn ntho
  "A relation where l is a collection, such that a is the nth element of l"
  ([l a n] (ntho l a n 0))
  ([l a n i]
    (conde
      [(== n i) (firsto l a)]
      [(fresh [r]
         (resto l r)
         (ntho r a n (inc i)))])))

(run* [q]
  (fresh [l x]
    (== l (vec (range 5 10)))
    (conde
      [(ntho l q 2)]
      [(ntho l 8 q)])
    ))

(defne lasto
  "A relation where l is a collection, such that a is the last element of l"
  [l a]
  ([[a] _])
  ([[_ . ?r] _] (lasto ?r a)))

(run* [q]
  (fresh [l x]
    (== l (vec (range 5)))
    (lasto l x)
    (membero q l)
    (!= q x))
  )

(defn not-first-lasto [x l]
  (fresh [first last]
    (firsto l first)
    (lasto l last)
    (membero x l)
    (!= x first)
    (!= x last)))

(run* [q]
  (fresh [l f]
    (== l (vec (range 1 8)))
    (not-first-lasto q l)
    ))

(run* [q]
  (fresh [l f]
    (== l (llist 1 2 3 4 5 6 7))
    (not-first-lasto q l)
    ))

(defne colrighto [x y l]
  ([_ _ [x y . ?r]])
  ([_ _ [_ . ?r]] (colrighto x y ?r)))

(defn colnexto [x y l]
  (conde
    ((colrighto x y l))
    ((colrighto y x l))))

(defne colbetweeno [a b c l]
  ([_ _ _ [a b c . ?r]])
  ([_ _ _ [c b a . ?r]])
  ([_ _ _ [_ . ?r]] (colbetweeno a b c ?r)))

(run* [q]
  (fresh [l]
    (== l (llist 1 2 3 4 5 6))
    (conde
      ((colbetweeno 1 q 3 l))
      ((colbetweeno 5 q 3 l))
      )))

(defne col-not-betweeno [ac b cc l]
  ([_ _ _ [ac ?x cc . ?r]] (nonmembero b ?x))
  ([_ _ _ [cc ?x ac . ?r]] (nonmembero b ?x))
  ([_ _ _ [_ . ?r]] (col-not-betweeno ac b cc ?r)))

(run* [q]
  (fresh [l]
    (== l  [[:mary :red 1] [:devil :blue 2] [:bill :yellow 3]])
      (col-not-betweeno (make-col :mary) :green (make-col :bill) l)
      (== q true)
      ))

(defmacro righto [x y g]
  (let [xc (make-col x)
        yc (make-col y)]
    (println x xc y yc)
    `(colrighto ~xc ~yc ~g)))

(macro/mexpand-all `(righto ~'ivory ~'green g))

(defmacro nexto [x y l]
  (let [xc (make-col x)
        yc (make-col y)]
  `(conde
    ((colrighto ~xc ~yc ~l))
    ((colrighto ~yc ~xc ~l)))))

(defmacro betweeno [a b c g]
  (let [ac (make-col a)
        bc (make-col b)
        cc (make-col c)]
  `(all
;    (trace-lvars (str :betweeno ~a ~b ~c) ~g)
    ;(not-first-lasto ~bc ~g)
    (colbetweeno ~ac ~bc ~cc ~g))
    ))

(defmacro not-betweeno [a b c g]
  (let [ac (make-col a)
        cc (make-col c)]
    `(all
;       (trace-lvars (str :not-betweeno " " ~a " " ~b " " ~c) ~g)
       (col-not-betweeno ~ac ~b ~cc ~g))))

(defn col-left-righto [left right l]
  (fresh [nl nr]
    (ntho l left nl)
    (ntho l right nr)
    (arithmetic/< nl nr)))

(run* [q]
  (fresh [l a b]
    (== l (range 5))
    (col-left-righto a b l)
    (== q [a b])))

(defmacro left-righto [left right l]
  (let [lc (make-col left)
        rc (make-col right)]
    `(col-left-righto ~lc ~rc ~l)))

(defmacro samecolo [cols & items]
  (let [col (apply make-col items)]
    (println :samecolo items col cols)
    `(all
;      (trace-lvars (str :samecolo ~col ~items) ~cols)
      (membero ~col ~cols))
    ))

(defmacro in-colo [g x n]
  (let [xc (make-col x)]
    `(all
;      (trace-lvars (str :in-colo ~xc) ~n ~g)
      (== ~g [~@(for [i (range game-cols)] (if (= i n) `~xc `~(lvar)))]))))

(macro/mexpand-1 '(in-colo g :milk 2))

(defmacro diffcolo [cols x y]
  (let [xc (make-col x)
        yc (make-col y)]
    `(fresh [xcp# ycp#]
;      (trace-lvars (str :diffcolo ~x ~xc ~y ~yc) xcp# ycp# ~cols)
      (ntho ~cols ~xc xcp#)
      (ntho ~cols ~yc ycp#)
      (!= xcp# ycp#))))

(defn grid [rows cols]
  (vec (for [c (range cols)] (vec (for [r (range rows)] (lvar))))))

(defn zebrao [hs]
  (macro/symbol-macrolet [_ (lvar)]
    (all
      (== [_ _ [_ _ :milk _ _] _ _] hs)
      (firsto hs [:norwegian _ _ _ _])
      (colnexto [:norwegian _ _ _ _] [_ _ _ _ :blue] hs)
      (colrighto [_ _ _ _ :ivory] [_ _ _ _ :green] hs)
      (membero [:englishman _ _ _ :red] hs)
      (membero [_ :kools _ _ :yellow] hs)
      (membero [:spaniard _ _ :dog _] hs)
      (membero [_ _ :coffee _ :green] hs)
      (membero [:ukrainian _ :tea _ _] hs)
      (membero [_ :lucky-strikes :oj _ _] hs)
      (membero [:japanese :parliaments _ _ _] hs)
      (membero [_ :oldgolds _ :snails _] hs)
      (colnexto [_ _ _ :horse _] [_ :kools _ _ _] hs)
      (colnexto [_ _ _ :fox _] [_ :chesterfields _ _ _] hs))))

;(println (run 1 [q] (zebrao q)))

(defmacro setup
  ([g p a ] `(membero ~(make-col a) ~g))
  ([g p a & rest]
    `(all
       (setup ~g ~p ~a)
       (setup ~g ~p ~@rest))))

(macroexpand-1 `(setup g 0 ~'norwegian))

(defn zo [g]
  (all
;    (== (grid 5 5) g)
;    (setup g 0 :norwegian :englishman :spaniard :ukranian :japanese)
;    (setup g 1 :kools :chesterfields :oldgolds :parliaments :lucky-strikes)
;    (setup g 2 :milk :tea :oj :coffee)
;    (setup g 3 :dog :horse :fox :snails)
;    (setup g 4 :blue :ivory :green :red :yellow)
    (in-colo g :milk 2)
    (in-colo g :norwegian 0)
    (nexto :norwegian :blue g)
    (righto :ivory :green g)
    (samecolo g :englishman :red)
    (samecolo g :kools :yellow)
    (samecolo g :spaniard :dog)
    (samecolo g :coffee :green)
    (samecolo g :ukranian :tea)
    (samecolo g :lucky-strikes :oj)
    (samecolo g :japanese :parliaments)
    (samecolo g :oldgolds :snails)
    (nexto :horse :kools g)
    (nexto :fox :chesterfields g)

    ))


;(run 1 [q] (zo q))


(macro/mexpand-all '(setup g 0 :mary :bill :devil))
(macroexpand-1 '(setup g 0 :mary :bill :devil))

(macro/mexpand-all '(all (diffcolo :mary :bill g) (diffcolo :mary :devil g) (diffcolo :bill :devil g)))

(defn s3x3-1 [g]
  (all
    (== (grid 3 3) g)
    (setup g 0 :mary :devil :bill)
    (setup g 1 :red :yellow :blue)
    (setup g 2 1 2 3)
;    (setup g 1 :blue)
;    (setup g 2 2 3)
    (in-colo g :mary 0)
    (samecolo g :red 1)
    (betweeno :mary :yellow :bill g)
    (left-righto :devil :bill g)
    (not-betweeno :bill 2 :blue g)
    ))

(defn s3x3-2 [g]
  (all
    (== (grid 3 3) g)
    (setup g 0 :mary :devil :bill)
    (setup g 1 :red :yellow :blue)
    (setup g 2 1 2 3)
    (in-colo g :devil 2)
    (samecolo g :blue 2)
    (diffcolo g :bill 1)
    (nexto :red 2 g)
    (nexto 1 3 g)
    (left-righto :bill 2 g)
    (not-betweeno 3 :blue :devil g)
    ))


(defn s3x3-3 [g]
  (all
    (== (grid 3 3) g)
    (setup g 0 :mary :devil :bill)
    (setup g 1 :red :yellow :blue)
    (setup g 2 1 2 3)
    (in-colo g :yellow 2)
    (samecolo g :bill :blue 3)
    (samecolo g :mary 1)
    (nexto :yellow 3 g)
    (left-righto 3 :mary g)
    (left-righto :red :yellow g)
    ))

(defn s3x3-4 [g]
  (all
    (== (grid 3 3) g)
    (setup g 0 :mary :devil :bill)
    (setup g 1 :red :yellow :blue)
    (setup g 2 1 2 3)
    (samecolo g :blue :bill)
    (diffcolo g :yellow 2)
    (betweeno :blue :yellow :red g)
    (not-betweeno 3 :blue :red g)
    (left-righto 1 2 g)
    (nexto :bill :mary g)
    ))

(defn s3x3-5 [g]
  (all
    (== (grid 3 3) g)
    (setup g 0 :mary :devil :bill)
    (setup g 1 :red :yellow :blue)
    (setup g 2 1 2 3)
    (samecolo g :devil 1)
    (diffcolo g :bill :red)
    (betweeno :blue :mary :red g)
    (nexto :mary 2 g)
    (left-righto 2 :devil g)
    ))


; (in-ns 'logic_exploration.sherlock)
; (run 1 [q] (s3x3-1 q))

