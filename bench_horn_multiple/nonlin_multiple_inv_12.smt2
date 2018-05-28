(declare-rel inv (Int Int))
(declare-rel inv1 (Int Int))
(declare-var a Int)
(declare-var a2 Int)
(declare-var b Int)
(declare-var b2 Int)

(declare-rel fail ())

(rule (=> (and (= a 2) (= b 2)) (inv a b)))

(rule (=> 
    (and 
	      (inv a b)
        (= a2 (* a a))
    )
    (inv a2 b)
  )
)

(rule (=> (inv a b) (inv1 a b)))

(rule (=>
    (and
        (inv1 a b)
        (= a2 (+ a a))
        (= b2 (* b a))
    )
    (inv1 a2 b2)
  )
)

(rule (=> (and (inv1 a b) (not (> b 1))) fail))
