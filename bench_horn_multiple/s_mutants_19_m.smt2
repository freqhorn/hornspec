(declare-rel inv (Int))
(declare-rel inv1 (Int Int Int Int Int))
(declare-var k0 Int)
(declare-var k1 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var j0 Int)
(declare-var j1 Int)
(declare-var n0 Int)
(declare-var n1 Int)
(declare-var b0 Int)
(declare-var b1 Int)

(declare-rel fail ())

(rule (inv 25465))

(rule (=> (and (inv k0) (not (> k0 1000)) (= k1 (- k0 1))) (inv k1)))

(rule (=> (and (inv k0) (<= k0 1000)
          (= i1 j1) (= n1 0) (= i1 0) (or (= b1 0) (= b1 1))) (inv1 k0 i1 j1 n1 b1)))

(rule (=> 
    (and 
        (inv1 k0 i0 j0 n0 b0)
        (< n0 (* 2 k0))
        (= i1 (ite (= b0 0) (+ i0 1) i0))
        (= j1 (ite (= b0 0) j0 (+ j0 1)))
        (= b1 (ite (= b0 0) 1 0))
        (= n1 (+ n0 1))
    )
    (inv1 k0 i1 j1 n1 b1)
  )
)

(rule (=> (and (inv1 k1 i1 j1 n1 b1) (>= n1 (* 2 k1)) (not (= 0 (mod n1 2)))) fail))

(query fail)
