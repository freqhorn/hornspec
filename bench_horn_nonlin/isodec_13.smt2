(declare-rel pre (Int))
(declare-var x Int)

(declare-rel fail ())

(rule (=> false (pre x)))

(rule (=> (and (pre (+ x 1)) (pre (- x 1))
    (not (and
        (< (- 2) (* 2 x))
        (< (* 2 x) 4)))) fail))

(query fail)
