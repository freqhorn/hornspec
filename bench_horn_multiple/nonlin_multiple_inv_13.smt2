(declare-rel inv (Int Int Int))
(declare-rel inv1 (Int Int Int))
(declare-var a Int)
(declare-var b Int)
(declare-var b1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=> (and (< a 0) (= b a) (= i -1)) (inv a b i)))

(rule (=> (inv a b i) (inv1 a b i)))

(rule (=> 
    (and 
	      (inv1 a b i)
        (= b1 (* a b))
	      (= i1 (- i))
    )
    (inv1 a b1 i1)
  )
)

(rule (=> (and (inv1 a b i) (= b1 (- b)) (= i1 (- i))) (inv a b1 i1)))

(rule (=> (and (inv a b i) (not (> (* b i) 0))) fail))

(query fail)
