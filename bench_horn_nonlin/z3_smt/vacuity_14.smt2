(declare-rel f (Int))


(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 2))) (f x1))))
(assert (forall ((x Int)) (=> (f x) (not (f (+ x 1))))))

(assert (exists ((x Int)) (f x)))

(check-sat)
(get-model)

