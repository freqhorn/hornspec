(declare-rel f (Int Int))
(declare-rel g (Int ))
(declare-rel h (Int ))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 0) (= y 0)) (f x y)))
(rule (=> (and (f x y) (h x) (= x1 (+ x 1)) (= y1 (+ y 1))) (f x1 y1)))
(rule (=> (and (f x y) (g x) (not (= y 200)))  fail))
(rule (=> (and (f x y) (g x) (h x))  fail))
(query fail)
