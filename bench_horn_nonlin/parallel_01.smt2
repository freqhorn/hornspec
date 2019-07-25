(declare-rel inv1 (Int))
(declare-rel inv2 (Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (= x 0) (inv1 x)))
(rule (=> (= x 0) (inv2 x)))

(rule (=> (and (inv1 x) (= x1 (+ x 1))) (inv1 x1)))
(rule (=> (and (inv2 x) (= x1 (+ x 1))) (inv2 x1)))

(rule (=> (and (inv1 x) (inv2 y) (not (>= (+ x y) 0))) fail))

(query fail)
