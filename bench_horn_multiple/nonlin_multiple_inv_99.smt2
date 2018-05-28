(declare-rel MLT1 (Int Int Int))
(declare-rel MLT2 (Int Int Int Int Int Int))
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
(declare-var f Int)
(declare-var f1 Int)

(declare-rel fail ())

; everything is linear, but non-linear invariants are required

(rule (MLT1 0 c 0))

(rule (=> (and (MLT1 a c e) (= a1 (+ a 1)) (= e1 (+ e c)))
          (MLT1 a1 c e1)))

(rule (=> (MLT1 a c e) (MLT2 a 0 c c e 0)))

(rule (=> (and (MLT2 a b c d e f) (= b1 (+ b 1)) (= f1 (+ f d)))
          (MLT2 a b1 c d e f1)))

(rule (=> (and (MLT2 a b c d e f) (= b a) (not (= e f))) fail))

(query fail)
