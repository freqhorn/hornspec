(declare-rel FUN (Int Int Int ))
(declare-rel SAD (Int Int Int Int ))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var d1 Int)
(declare-var d2 Int)
(declare-var d3 Int)
(declare-var c1 Int)
(declare-var c2 Int)
(declare-var c3 Int)
(declare-var c4 Int)
(declare-var f1 Int)
(declare-var f2 Int)

; inspired by trex3_m.smt2 but with nonlinear arithm in the query

(declare-rel fail ())

(rule (FUN x1 x2 c1 ))

(rule (=> (and (FUN x1 x2 c1)
               (= x4 (+ x1 1)) (= x5 (+ x2 1)))
      (SAD x4 x5 c1 0)))

(rule (=> 
    (and 
        (SAD x1 x2 c1 f1)
        (> x1 0)
        (> x2 0)
        (= x4 (ite (= c1 1) (- x1 1) x1))
        (= x5 (ite (and (not (= c1 1)) (= c2 1)) (- x2 1) x2))
    )
    (SAD x4 x5 c3 1)
  )
)

(rule (=> (and (SAD x1 x2 c1  f1)
        (= f1 0) (not (and (> x1 0) (> x2 0))))
    (FUN x1 x2 c1)))

(rule (=> (and (SAD x1 x2 c1 f1)
               (= f1 1) (not (and (> x1 0) (> x2 0) ))
          (not (= (* x1 x2) 0))) fail))

(query fail)
