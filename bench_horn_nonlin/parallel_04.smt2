(declare-rel inv1 (Int))
(declare-rel inv2 (Int))
(declare-rel inv3 (Int))
(declare-rel inv4 (Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)

(declare-rel fail ())

(rule (=> (= x 1) (inv1 x)))
(rule (=> (= x 4) (inv4 x)))

(rule (=> (and (inv1 x) (= x1 (+ x 1))) (inv2 x1)))
(rule (=> (and (inv2 x) (= x1 (+ x 2))) (inv3 x1)))
(rule (=> (and (inv3 x) (= x1 (+ x 3))) (inv1 x1)))
(rule (=> (and (inv4 x) (= x1 (+ x 4))) (inv4 x1)))

(rule (=> (and (inv1 x) (inv4 z) (not (>= (+ x z) 0))) fail))

(query fail)
