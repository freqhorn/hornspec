(declare-rel inv4 (Int))
(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> false (inv4 x)))

(rule (=> (and (inv4 x) (inv4 y) (= x (+ 1 y))) fail))

(query fail)
