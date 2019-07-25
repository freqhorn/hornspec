(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 0) (= y -10)) (inv x y)))

(rule (=> (and (= x 0) (= y -8)) (inv x y)))

(rule (=> (and (= x 0) (= y -6)) (inv x y)))

(rule (=> (and (= x 0) (= y -4)) (inv x y)))

(rule (=> (and (= x 0) (= y -2)) (inv x y)))

(rule (=> (and (= x 0) (= y 0)) (inv x y)))

(rule (=> 
    (and 
	      (inv x y)
        (> x1 0)
        (= x1 (+ x 1))
        (= y1 (+ y 2)))
    (inv x1 y1)))

(rule (=> (and (inv 5 y) (= y 7)) fail))

(query fail)
