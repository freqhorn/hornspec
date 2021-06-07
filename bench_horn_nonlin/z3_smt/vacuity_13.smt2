(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-rel k (Int))


(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (f x) (k y) (= x1 (+ x y))) (f x1))))
(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (g x) (f y) (= x1 (+ x y 2))) (g x1))))
(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (h x) (f y) (= x1 (- (- x y) 3))) (h x1))))
(assert (forall ((x Int) (y Int)) (=> (and (g x) (h y)) (< x y))))

(assert (exists ((x Int) (y Int)) (and (f x) (k y))))
(assert (exists ((x Int) (y Int)) (and (g x) (f y))))
(assert (exists ((x Int) (y Int)) (and (h x) (f y))))
(assert (exists ((x Int) (y Int)) (and (g x) (h y))))


(check-sat)
(get-model)

