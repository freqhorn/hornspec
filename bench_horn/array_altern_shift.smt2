(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var j Int)

(declare-rel inv ((Array Int Int) Int))
(declare-rel fail ())

(rule (=> (and (forall ((j Int)) (> (select a j) 0)) (> i 0)) (inv a i)))

(rule (=> (and (inv a i)
  (forall ((j Int)) (= (select a1 j) (+ i (select a j))))) (inv a1 i)))

(rule (=> (and (inv a i) (not (> (select a j) 0))) fail))

(query fail)
