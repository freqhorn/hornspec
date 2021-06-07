(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))


(assert (forall ((x Int)) (=> (= x 14) (h x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (g x1))))
(assert (forall ((x Int) (x1 Int)) (=> (and (g x) (= x1 (- x 1))) (f x1))))
(assert (forall ((x Int) (y Int)) (=> (and (g x) (h y)) (not (= x y)))))


(assert (exists ((x Int)) (g x)))
(assert (exists ((x Int)) (f x)))

(check-sat)
(get-model)

