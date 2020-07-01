(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var j Int)

(declare-rel inv ((Array Int Int) (Array Int Int)))
(declare-rel fail ())

(rule (inv a a))

(rule (=> (and (inv a b) (= a1 (store (store a j (select a i)) i (select a j)))) (inv a1 b)))

(rule (=> (and (inv a b)
  (not (forall ((j2 Int)) (exists ((i2 Int)) (= (select a i2) (select b j2)))))) fail))

(query fail)
