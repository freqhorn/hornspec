(declare-rel inv (Int Int Int Int))
(declare-rel inv1 (Int ))
(declare-rel inv2 (Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var len Int)
(declare-var C Int)

(declare-rel fail ())

(rule (=> (and (= x 1) true) (inv1 x)))
(rule (=> (inv1 x) (inv2 x)))
(rule (=> (and (inv2 x) (= C 50) (= y 51) (> len 0)) (inv x y C len)))

(rule (=> 
    (and 
      (inv x y C len)
      (< x len)
      (= x1 (+ x 1))
      (= y1 (+ y 1))
    )
    (inv x1 y1 C len)))

(rule (=> (and (inv x y C  len) (not (< x len)) (not (= y C))) fail))

(query fail)

