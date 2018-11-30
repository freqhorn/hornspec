(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int Int))
(declare-rel fail ())
(declare-var x Int)
(declare-var r0 Int)
(declare-var r1 Int)

(rule (=> (= r0 (+ x 1)) (h x r0)))
(rule (g 3))
(rule (=> (and (g r0) (h r0 r1)) (f r1)))
(rule (=> (and (f r1) (> r1 4)) fail))

(query fail)
