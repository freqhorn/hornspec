(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)

(declare-rel fail ())

(assert (forall ((x Int)) (=> (= x -10) (g x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (f x1))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (not (= x y)) )))

(assert (exists ((x Int)) (f x)))
(assert (exists ((x Int) (y Int)) (and (f x) (g y))))

(check-sat)
(get-model)
