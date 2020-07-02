(declare-var p (Array Int Int))
(declare-var g (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv p g 0 N))

(rule (=> (and (inv p g i N) (< i N) (= (select p i) (select g i)) (= i1 (+ i 1))) (inv p g i1 N)))

(rule (=> (and (inv p g i N) (= (select p i) (select g i)) (<= 0 i1) (< i1 i) (not (= (select p i1) (select g i1)))) fail))

(query fail)
