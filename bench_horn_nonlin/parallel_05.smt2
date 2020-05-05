(declare-rel inv2 (Int))
(declare-rel inv3 (Int))
(declare-rel inv4 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (= x 12) (inv2 x)))
(rule (=> (= x 7) (inv3 x)))

(rule (=> (and (inv2 x) (= x1 (+ x 2))) (inv2 x1)))
(rule (=> (and (inv3 y) (= y1 (- y 3))) (inv3 y1)))

(rule (=> (and (inv2 x) (inv3 y)) (inv4 x y)))

(rule (=> (and (inv4 x y) (not (> x y))) fail))

(query fail)
