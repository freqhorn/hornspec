(declare-rel MLT1 (Int Int Int))
(declare-rel MLT2 (Int Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var c Int)
(declare-var c1 Int)
(declare-var e Int)
(declare-var e1 Int)

(declare-rel fail ())

(rule (MLT1 0 c 0))

(rule (=> (and (MLT1 a c e) (= a1 (+ a 1)) (= e1 (+ e c)))
          (MLT1 a1 c e1)))

(rule (=> (MLT1 a c e) (MLT2 a c e)))

(rule (=> (and (MLT2 a c e) (= a1 (- a 1)) (= e1 (- e c)))
          (MLT2 a1 c e1)))

(rule (=> (and (MLT2 a c e) (not (= e (* a c)))) fail))

(query fail)
