(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (and (h x) (h y)) (f (+ x y))))
(rule (=> (and (h x) (h y)) (g (+ x y))))
(rule (=> (and (f x) (g y) (not (>= (+ x y) -100))) fail))

(query fail)
