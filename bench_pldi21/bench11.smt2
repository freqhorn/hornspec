(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (= x 14) (h x)))
(rule (=> (and (f x) (= x1 (+ x 1))) (g x1)))
(rule (=> (and (g x) (= x1 (- x 1))) (f x1)))
(rule (=> (and (g x) (h y) (= x y)) fail))

(query fail)
