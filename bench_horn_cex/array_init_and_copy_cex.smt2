(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var N Int)

(declare-rel inv1 ((Array Int Int) Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv1 a 0 N))

(rule (=> (and (inv1 a i N) (< i N) (= (store a i 1) a1) (= i1 (+ i 1))) (inv1 a1 i1 N)))

(rule (=> (and (inv1 a i N) (>= i N)) (inv2 a b 0 N)))

(rule (=> (and (inv2 a b i N) (< i N) (= (store b i (- 1 (select a i))) b1) (= i1 (+ i 1))) (inv2 a b1 i1 N)))

(rule (=> (and (inv2 a b i N) (>= i N) (< 0 i1) (< i1 N) (not (>= (select b i1) 1))) fail))

(query fail)
