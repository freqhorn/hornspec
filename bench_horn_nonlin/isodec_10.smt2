(declare-rel inv1 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> false (inv1 x y)))

(rule (=> (and (inv1 x y) (inv1 x1 y1) (not (= (+ x x1) (+ y y1)))) fail))

(query fail)
