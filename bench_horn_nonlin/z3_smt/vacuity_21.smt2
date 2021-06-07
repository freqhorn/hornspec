(declare-rel f (Int Int))
(declare-rel g (Int ))
(declare-rel h (Int ))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (f x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (f x y) (h x) (= x1 (+ x 1)) (= y1 (+ y 1))) (f x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (f x y) (g x) (= y 200)))))
(assert (forall ((x Int) (y Int)) (=> (and (f x y) (g x)) (not (h x)))))

(assert (exists ((x Int) (y Int)) (and (f x y) (h x))))
(assert (exists ((x Int) (y Int)) (and (f x y) (g x))))


(check-sat)
(get-model)
