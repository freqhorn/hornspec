(declare-rel itp (Int Int ))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= x3 0)) (itp x1 x3)))

(rule (=> 
    (and 
        (itp x1 x3 )
        (= x2 (+ x1 1))
        (= x4 (- x3 1))
    )
    (itp x2 x4)
  )
)


(rule (=> (and (itp x1 x3) 
   (not 
     (and 
       (<= x1 100)
       (>= x3 -100)
     )
   )) fail))


(query fail :print-certificate true)