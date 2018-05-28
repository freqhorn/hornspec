(declare-rel inv (Int Int Int Int Int))
(declare-rel inv1 (Int Int))
(declare-var a Int)
(declare-var b Int)
(declare-var c1 Int)
(declare-var c2 Int)
(declare-var d1 Int)
(declare-var d2 Int)
(declare-var e1 Int)
(declare-var e2 Int)

(declare-rel fail ())

(rule (=> (and (> a 0) (>= b a) (= c1 0) (= e1 0) (= d1 0)) (inv a b c1 d1 e1)))

(rule (=> 
    (and 
        (inv a b c1 d1 e1)
        (= c2 (+ c1 1))
        (= d2 (+ d1 a))
        (= e2 (+ e1 b))
    )
    (inv a b c2 d2 e2)
  )
)

(rule (=> (and (inv a b c1 d1 e1) (= e1 (* b c1)) (= e2 (* a c1))) (inv1 e1 e2)))

(rule (=> (and (inv1 e1 e2) (= c1 (+ e1 1)) (= c2 (+ e2 1))) (inv1 c1 c2)))

(rule (=> (and (inv1 c1 c2) (not (>= c1 c2))) fail))

(query fail)

