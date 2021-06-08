(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-rel k (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (=> (and (f x) (k y) (= x1 (+ x y))) (f x1)))
(rule (=> (and (g x) (f y) (= x1 (+ x y 2))) (g x1)))
(rule (=> (and (h x) (f y) (= x1 (- (- x y) 3))) (h x1)))
(rule (=> (and (g x) (h y) (not (< x y))) fail))

(query fail)
