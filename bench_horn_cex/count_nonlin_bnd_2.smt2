(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (<= x 0) (or (= y 0) (= y 2))) (inv x y)))

(rule (=> 
    (and 
	      (inv x y)
        (> x1 0)
        (= x1 (+ x 1))
        (= y1 (+ y 1)))
    (inv x1 y1)))

(rule (=> (and (inv 100 y) (inv 100 y1) (not (= y y1))) fail))

(query fail)
