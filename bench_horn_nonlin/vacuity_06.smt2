(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-rel k (Int))
(declare-rel l (Int))

(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (= x -1) (k x)))
(rule (=> (and (k x) (h y)) (f (+ x y))))
(rule (=> (and (l x) (h y)) (g (+ x y))))
(rule (=> (and (f x) (g y) (not (= x y))) fail))

(query fail)
