(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a b 0 n))

(rule (=> (and (inv a b i n) (< i n) (= (store b i (select a i)) b1) (= i1 (+ i 1))) (inv a b1 i1 n)))

(rule (=> (and (inv a b i n) (not (< i n))
  (not (forall ((j1 Int)) (=> (and (>= j1 0) (< j1 i))   ; TBD: support full ranges
    (exists ((i2 Int)) (= (select b j1) (select a i2))))))) fail))

(query fail)
