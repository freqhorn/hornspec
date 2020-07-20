(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (=> (= x -10) (g x)))
(rule (=> (and (f x) (= x1 (+ x 1))) (f x1)))
(rule (=> (and (f x) (g y) (= x y)) fail))
(query fail)
