(declare-rel f (Int Int))
(declare-rel g (Int))
(declare-rel h (Int Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (g z) (g (* 2 z))))
(rule (=> (and (f x y) (h x1 x) (= y1 (+ y x))) (f x1 y1)))
(rule (=> (and (f x y) (g z) (not (>= y (* 2 z)))) fail))

(query fail)
