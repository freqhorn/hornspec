(declare-rel itp1 (Int Int))
(declare-rel itp (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x9 Int)

(declare-rel fail ())

(rule (=> (> x0 0) (itp1 x0 x0)))

(rule (=> (and (itp1 x0 x9) (< x0 (* 2 x9)) (= x5 (+ x0 1))) (itp1 x5 x9)))

(rule (=> (and (itp1 x5 x9) (= x1 0) (= x3 0) (not (< x5 (* 2 x9)))) (itp x1 x3 x5)))

(rule (=> 
    (and 
        (itp x1 x3 x5)
        (or (and (= x2 (+ x1 1)) (= x4 (+ x3 1))) 
            (and (= x2 (- x1 1)) (= x4 (- x3 1))))
        (= x6 (+ x5 x2 x4))
    )
    (itp x2 x4 x6)
  )
)

(rule (=> (and (itp x1 x3 x5) (= x5 77)) fail))

(query fail :print-certificate true)
