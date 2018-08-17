(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var i2 Int)

; very tricky query

(declare-rel inv ((Array Int Int) Int))
(declare-rel fail ())

(rule (=> (= a1 (store (store a 0 0) 1 1)) (inv a1 2)))

(rule (=> (and (inv a i) (= (store a i i) a1) (= i1 (+ i 1))) (inv a1 i1)))

(rule (=> (and (inv a i) (< 0 i1) (< i1 i) (not (< (select a (- i1 1)) (select a i1)))) fail))

(query fail)
