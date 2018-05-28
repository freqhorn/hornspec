(declare-rel PLUS (Int Int))
(declare-rel MULT (Int Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)
(declare-var k Int)
(declare-var k1 Int)

(declare-rel fail ())

(rule (=> (< n 0) (PLUS 0 n)))

(rule (=> (and (PLUS m n) (< n1 0)) (MULT m n1 1)))

(rule (=> (and (MULT m n k) (= k1 (* k n)) (= n1 (+ n 1))) (MULT m n1 k1)))

(rule (=> (and (MULT m n k) (> n 0) (= m1 (+ m k))) (PLUS m1 n1)))

(rule (=> (and (PLUS m n) (not (= m 0))) fail))

(query fail)
