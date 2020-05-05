(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (f x) (= x1 (+ x 1))) (f x1)))
(rule (=> (and (g x) (= x1 (- x 1))) (g x1)))
(rule (=> (and (g x) (g y) (f z) (f w) (not (< (+ x y) (+ z w)))) fail))

(query fail)
