(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-rel k (Int))


(assert (forall ((x Int)) (=> (= x -1) (k x))))
(assert (forall ((x Int) (y Int)) (=> (and (k x) (h y)) (f (+ x y)))))
(assert (forall ((x Int)) (=> (g x) (g (- x)))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (= x y))))

(assert (exists ((x Int) (y Int)) (and (k x) (h y))))
(assert (exists ((x Int) (y Int)) (and (f x) (g y))))

(check-sat)
(get-model)

