(declare-rel inv (Int Int ))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(declare-rel fail ())

(rule (=> (and (= (- x1 878) (+ x3 602))) 
          (inv x1 x3)))

(rule (=> 
    (and 
	(inv x1 x3)
        (< x3 x1)
        (> x4 x2)
    )
    (inv x2 x4)
  )
)

(rule (=> (and (inv x1 x3) 
    (not (or 
        (< x1 0)
        (> x3 0)
    ))) fail))

(query fail :print-certificate true)