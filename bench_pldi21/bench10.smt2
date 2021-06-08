(declare-rel f (Int))
(declare-rel g (Int Int))
(declare-rel h (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (< x 0) (h x)))
(rule (=> (and (f x) (= x1 (+ x 1))) (f x1)))
(rule (=> (and (f x) (h y)) (g x y)))
(rule (=> (and (g x y) (= x y)) fail))

(query fail)
