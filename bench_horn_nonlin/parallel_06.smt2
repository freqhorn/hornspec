(declare-rel inv2 (Int))
(declare-rel inv3 (Int))
(declare-rel inv4 (Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var v Int)
(declare-var w Int)

(declare-rel fail ())

(rule (=> (= x 1) (inv2 x)))
(rule (=> (= x 1) (inv3 x)))

(rule (=> (and (inv2 x) (= x1 (+ x 2))) (inv2 x1)))
(rule (=> (and (inv3 y) (= y1 (+ y 3))) (inv3 y1)))

(rule (=> (and (inv2 x) (inv3 y)) (inv4 (+ x y))))

(rule (=> (and (inv2 v) (inv4 x) (inv3 y) (inv4 z) (inv2 w) (not (> (+ x y z v w) 0))) fail))

(query fail)
