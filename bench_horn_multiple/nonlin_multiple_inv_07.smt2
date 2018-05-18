(declare-rel MLT1 (Int Int Int))
(declare-rel MLT2 (Int Int Int Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)
(declare-var c Int)
(declare-var c1 Int)
(declare-var d Int)
(declare-var d1 Int)
(declare-var e Int)
(declare-var e1 Int)

(declare-rel fail ())

(rule (MLT1 0 b 0))

(rule (=> (and (MLT1 a b c) (= a1 (+ a 1)) (= c1 (+ c b)))
          (MLT1 a1 b c1)))

(rule (=> (MLT1 a b c) (MLT2 a b 0 c 0)))

(rule (=> (and (MLT2 a b c d e) (= c1 (+ c 1)) (= e1 (+ e d)))
          (MLT2 a b c1 d e1)))

(rule (=> (and (MLT2 a b c d e) (not (= e (* c (* a b))))) fail))

(query fail)
