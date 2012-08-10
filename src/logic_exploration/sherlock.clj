(ns logic_exploration.sherlock
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic)
  (:require [clojure.tools.macro :as macro]
            [clojure.core.logic.arithmetic :as arithmetic]))

(def zebra-map
  (apply hash-map (flatten (map (fn [[n & r]] (map vector r (repeat n)))
                             [[0 :norwegian :englishman :spaniard :ukranian :japanese ]
                              [1 :kools :chesterfields :oldgolds :parliaments :lucky-strikes ]
                              [2 :milk :tea :oj :coffee ]
                              [3 :dog :horse :fox :snails ]
                              [4 :blue :ivory :green :red :yellow ]]))))

(defn sherlock-map [cols rows]
  (let [cols (take cols [[:bill :mary :devil :ugly :beardy :baby :clown :bignose]
                         [:red :blue :yellow :green :white :pink :brown :cyan]
                         [1 2 3 4 5 6 7 8]
                         [:orange :apple :bananna :pear :cherry :grape :strawberry :lemon]
                         [:stop :hospital :speed :one-way :rr :dead-end :no-p :yield]
                         ["s" "h" "e" "r" "l" "o" "c" "k"]
                         [:america :uk :japan :canada :france :isreal :oz :germany]
                         [:hammer :screwdriver :square :roller :level :drill :tape :brush]
                        ])
        rows (map #(take rows %) cols)]
  (apply hash-map (flatten (map-indexed (fn [n r] (map vector r (repeat n))) rows)))))

(def ^{:dynamic true} *col-map* (sherlock-map 3 3))
(def ^{:dynamic true} *game-rows* 3)
(def ^{:dynamic true} *game-cols* 3)


(defn make-col
  ([x] (let [xp (*col-map* x)]
;         (println x xp)
         (vec (for [i (range *game-rows*)] (if (= i xp) x (lvar))))))
  ([x y] (let [xp (*col-map* x) yp (*col-map* y)]
;           (println x xp y yp)
           (vec (for [i (range *game-rows*)] (condp = i xp x yp y (lvar))))))
  ([x y z] (let [xp (*col-map* x) yp (*col-map* y) zp (*col-map* z)]
;             (println x xp y yp z zp)
             (vec (for [i (range *game-rows*)] (condp = i xp x yp y zp z (lvar)))))))

(def ^{:dynamic true} *make-col* make-col)

(defn nonmembero
  "A relation where l is a collection, such that x is not an element of l"
  [x l]
  (all
;    (trace-lvars :nonmembero x l)
;    (trace-s)
    (conda
      [(emptyo l) s#]
      [(firsto l x) u#]
      [s# (fresh [d] (resto l d) (nonmembero x d))])))

(run* [q]
  (fresh [m] (memo :f [:bar :foo :baz ] q))
  )

(run* [q]
  (nonmembero :spoo [:foo :bar :spoo ])
  (== q true))

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
    (== q x))
  )

(defn not-in-firsto [l x]
  (fresh [first]
    (firsto l first)
    (nonmembero x first)))

(defn not-in-lasto [l x]
  (fresh [last]
    (lasto l last)
;    (trace-s)
;    (trace-lvars :not-in-lasto l x last)
    (nonmembero x last)))

(run* [q]
  (fresh [l f o]
    (== l [(range 3) (range 3 6) (range 6 9)])
;    (not-in-firsto l 5)
    (not-in-lasto l 5)
    (== o (vec (range 9)))
;    (== q true)
    (membero q o)
    ))

(defne colrighto [l x y]
  ([[x y . ?r] _ _])
  ([[_ . ?r] _ _] (colrighto ?r x y)))

(defn colnexto [l x y]
  (conde
    ((colrighto l x y))
    ((colrighto l y x))))

(defne colbetweeno [l a b c]
  ([[a b c . ?r] _ _ _])
  ([[c b a . ?r] _ _ _])
  ([[_ . ?r] _ _ _] (colbetweeno ?r a b c)))

(run* [q]
  (fresh [l]
    (== l (llist 1 2 3 4 5 6))
    (conde
      ((colbetweeno l 1 q 3))
      ((colbetweeno l 5 q 3))
      )))

(defne col-not-betweeno [l ac b cc]
  ([[ac ?x cc . ?r] _ _ _] (nonmembero b ?x))
  ([[cc ?x ac . ?r] _ _ _] (nonmembero b ?x))
  ([[_ . ?r] _ _ _] (col-not-betweeno ?r ac b cc)))

(run* [q]
  (fresh [l]
    (== l [[:mary :red 1] [:devil :blue 2] [:bill :yellow 3]])
    (col-not-betweeno l (*make-col* :mary ) :green (*make-col* :bill ))
    (== q true)
    ))

(defmacro righto [g x y]
  (let [xc (*make-col* x)
        yc (*make-col* y)]
    ;(println x xc y yc)
    `(colrighto ~g ~xc ~yc)))

(macro/mexpand-all `(righto g ~'ivory ~'green))

(defmacro nexto [l x y]
  (let [xc (*make-col* x)
        yc (*make-col* y)]
    `(conde
       ((colrighto ~l ~xc ~yc))
       ((colrighto ~l ~yc ~xc)))))

(defmacro betweeno [g a b c]
  (let [ac (*make-col* a)
        bc (*make-col* b)
        cc (*make-col* c)]
    `(all
;           (trace-lvars (str :betweeno ~a ~b ~c) ~g)
       (not-in-firsto ~g ~b)
       (not-in-lasto ~g ~b)
       (colbetweeno ~g ~ac ~bc ~cc))
    ))

(defmacro not-betweeno [g a b c]
  (let [ac (*make-col* a)
        cc (*make-col* c)]
    `(all
;              (trace-lvars (str :not-betweeno " " ~a " " ~b " " ~c) ~g)
       (col-not-betweeno ~g ~ac ~b ~cc))))

(defn col-left-righto [l left right]
  (fresh [nl nr]
    (ntho l left nl)
    (ntho l right nr)
    (arithmetic/< nl nr)))

(run* [q]
  (fresh [l a b]
    (== l (range 5))
    (col-left-righto l a b)
    (== q [a b])))

(defmacro left-righto [l left right]
  (let [lc (*make-col* left)
        rc (*make-col* right)]
    `(all
       (not-in-lasto ~l ~left)
       (not-in-firsto ~l ~right)
       (col-left-righto ~l ~lc ~rc))))

(defmacro samecolo [g & items]
  (let [col (apply *make-col* items)]
    ; (println :samecolo items col g)
    `(all
;             (trace-lvars (str :samecolo ~col ~items) ~g)
       (membero ~col ~g))
    ))

(defmacro in-colo [g x n]
  (let [xc (*make-col* x)]
    `(all
;             (trace-lvars (str :in-colo ~xc) ~n ~g)
       (== ~g [~@(for [i (range *game-cols*)] (if (= i n) `~xc `~(lvar)))]))))

(macro/mexpand-1 '(in-colo g :milk 2))

(defmacro diffcolo [g x y]
  (let [xc (*make-col* x)
        yc (*make-col* y)]
    `(fresh [xcp# ycp#]
       ;      (trace-lvars (str :diffcolo ~x ~xc ~y ~yc) xcp# ycp# ~g)
       (ntho ~g ~xc xcp#)
       (ntho ~g ~yc ycp#)
       (!= xcp# ycp#))))

(defn altcolo [g x a b]
  (all
    (diffcolo g a b)
    (conda
      [(samecolo g x a)]
      [(samecolo g x b)])))

(defn grid [cols rows]
  (vec (for [c (range cols)] (vec (for [r (range rows)] (lvar))))))

(defn zebrao [hs]
  (macro/symbol-macrolet [_ (lvar)]
    (all
      (== [_ _ [_ _ :milk _ _] _ _] hs)
      (firsto hs [:norwegian _ _ _ _])
      (colnexto hs [:norwegian _ _ _ _] [_ _ _ _ :blue ])
      (colrighto hs [_ _ _ _ :ivory ] [_ _ _ _ :green ])
      (membero [:englishman _ _ _ :red ] hs)
      (membero [_ :kools _ _ :yellow ] hs)
      (membero [:spaniard _ _ :dog _] hs)
      (membero [_ _ :coffee _ :green ] hs)
      (membero [:ukrainian _ :tea _ _] hs)
      (membero [_ :lucky-strikes :oj _ _] hs)
      (membero [:japanese :parliaments _ _ _] hs)
      (membero [_ :oldgolds _ :snails _] hs)
      (colnexto hs [_ _ _ :horse _] [_ :kools _ _ _])
      (colnexto hs [_ _ _ :fox _] [_ :chesterfields _ _ _]))))

;(println (run 1 [q] (zebrao q)))

(defmacro setup
  ([g a] `(membero ~(*make-col* a) ~g))
  ([g a & rest]
    `(all
       (setup ~g ~a)
       (setup ~g ~@rest))))

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
    (nexto g :norwegian :blue)
    (righto g :ivory :green)
    (samecolo g :englishman :red )
    (samecolo g :kools :yellow )
    (samecolo g :spaniard :dog )
    (samecolo g :coffee :green )
    (samecolo g :ukranian :tea )
    (samecolo g :lucky-strikes :oj )
    (samecolo g :japanese :parliaments )
    (samecolo g :oldgolds :snails )
    (nexto g :horse :kools)
    (nexto g :fox :chesterfields)

    ))


;(run 1 [q] (zo q))


(macro/mexpand-1 '(setup g 1 2 3))

(macro/mexpand-all '(setup g 0 :mary :bill :devil ))
(macroexpand-1 '(setup g 0 :mary :bill :devil ))

(macro/mexpand-all '(all (diffcolo :mary :bill g) (diffcolo :mary :devil g) (diffcolo :bill :devil g)))

(defmacro defgame [name & body]
  (let [[_ t cs rs] (first (re-seq #"([sz])(\d)x(\d)-\d+" (str name)))
        cols (read-string cs)
        rows (read-string rs)
        g (gensym "game_")
        pieces (keys (sherlock-map cols rows))
        ]
  `(defn ~name []
    (binding [*col-map* (sherlock-map ~cols ~rows)
              *game-rows* ~rows
              *game-cols* ~cols
              *make-col* (memoize make-col)]
     (run 1 [~g]
        (== ~g (grid ~cols ~rows))
       (setup ~g ~@pieces)
       ~@(map (fn [f] `(~(first f) ~g ~@(next f))) body)
       )))))

(macro/mexpand '(doto g   (in-colo :mary 0)
                  (samecolo :red 1)
                  (betweeno :mary :yellow :bill )
                  (left-righto :devil :bill )
                  (not-betweeno :bill 2 :blue )))

(macro/mexpand-1

'(defgame s3x3-1
  (in-colo :mary 0)
  (samecolo :red 1)
  (betweeno :mary :yellow :bill )
  (left-righto :devil :bill )
  (println :boo)
  (not-betweeno :bill 2 :blue ))
)

(defgame s3x3-1
  (setup :mary :devil :bill )
  (setup :red :yellow :blue )
  (in-colo :mary 0)
  (samecolo :red 1)
  (betweeno :mary :yellow :bill )
  (left-righto :devil :bill )
  (println :boo)
  (not-betweeno :bill 2 :blue ))

(defn s3x3-1a [g]
  (all
    (== (grid 3 3) g)
    (setup g :mary :devil :bill )
    (setup g :red :yellow :blue )
    (setup g 1 2 3)
    (in-colo g :mary 0)
    (samecolo g :red 1)
    (betweeno g :mary :yellow :bill )
    (left-righto g :devil :bill )
    (println g :boo )
    (not-betweeno g :bill 2 :blue )))

(defgame s3x3-2
    (in-colo :devil 2)
    (samecolo :blue 2)
    (diffcolo :bill 1)
    (nexto :red 2)
    (nexto 1 3)
    (left-righto :bill 2)
    (not-betweeno 3 :blue :devil)
    )

(defn s3x3-2a [g]
  (all
    (== (grid 3 3) g)
    (setup g :mary :devil :bill )
    (setup g :red :yellow :blue )
    (setup g 1 2 3)
    (in-colo g :devil 2)
    (samecolo g :blue 2)
    (diffcolo g :bill 1)
    (nexto g :red 2)
    (nexto g 1 3)
    (left-righto g :bill 2)
    (not-betweeno g 3 :blue :devil)
    ))


(defn s3x3-3 [g]
  (all
    (== (grid 3 3) g)
    (setup g :mary :devil :bill )
    (setup g :red :yellow :blue )
    (setup g 1 2 3)
    (in-colo g :yellow 2)
    (samecolo g :bill :blue 3)
    (samecolo g :mary 1)
    (nexto g :yellow 3)
    (left-righto g 3 :mary)
    (left-righto g :red :yellow)
    ))

(defn s3x3-4 [g]
  (all
    (== (grid 3 3) g)
    (setup g :mary :devil :bill )
    (setup g :red :yellow :blue )
    (setup g 1 2 3)
    (samecolo g :blue :bill )
    (diffcolo g :yellow 2)
    (betweeno g :blue :yellow :red)
    (not-betweeno g 3 :blue :red)
    (left-righto g 1 2)
    (nexto g :bill :mary)
    ))

(defn s3x3-5 [g]
  (all
    (== (grid 3 3) g)
    (setup g :mary :devil :bill )
    (setup g :red :yellow :blue )
    (setup g 1 2 3)
    (samecolo g :devil 1)
    (diffcolo g :bill :red)
    (betweeno g :blue :mary :red)
    (nexto g :mary 2)
    (left-righto g 2 :devil)
    ))


; (in-ns 'logic_exploration.sherlock)
; (run 1 [q] (s3x3-5 q))

(defgame s5x5-1
  (samecolo :green 3 :orange)
  (samecolo 3 :one-way)
  (samecolo :devil 1 :cherry)
  (samecolo 4 :bananna)
  (samecolo 5 :speed)
  (nexto :beardy :one-way)
  (not-betweeno :pear :rr 5)
  (left-righto :rr :speed)
  (not-betweeno :mary :bananna :blue)
  (not-betweeno :brown :stop :devil)
  (not-betweeno :orange :hospital :speed)
  (betweeno :yellow :mary 4)
  (nexto :baby :hospital)
  (betweeno 2 :devil 5)
  (nexto :bananna :one-way)
  (left-righto 1 :orange))
