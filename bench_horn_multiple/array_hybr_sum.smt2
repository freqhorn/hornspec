(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var N Int)

(declare-rel inv1 ((Array Int Int) Int Int Int))
(declare-rel inv2 ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (> N 0) (inv2 a 0 N)))

(rule (=> (and (inv2 a i N) (< i N) (= (store a i i) a1) (= i1 (+ i 1))) (inv2 a1 i1 N)))

(rule (=> (and (inv2 a i N) (>= i N)) (inv1 a 0 0 N)))

(rule (=> (and (inv1 a i j N) (< i N) (= j1 (+ j (select a i))) (= i1 (+ i 1))) (inv1 a i1 j1 N)))

(rule (=> (and (inv1 a i j N) (>= i N) (not (>= j 0))) fail))

(query fail)
