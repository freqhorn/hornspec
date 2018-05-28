(declare-rel OUT_MLT (Int Int Int Int))
(declare-rel INN_MLT (Int Int Int Int))
(declare-var k Int)
(declare-var k1 Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (=> (and (= k 0) (= j 0) (= i 0) (> N 0)) (OUT_MLT k i j N)))

(rule (=> (OUT_MLT k i j N) (INN_MLT k i 0 N)))

(rule (=> 
    (and 
        (INN_MLT k i j N)
        (< j N)
        (= k1 (+ k 1))
        (= j1 (+ j 1))
    )
    (INN_MLT k1 i j1 N)
  )
)

(rule (=> (and (INN_MLT k i j N) (>= j N) (= i1 (+ i 1))) (OUT_MLT k i1 j N)))

(rule (=> (and (OUT_MLT k i j N) (not (= k (* i N)))) fail))

(query fail)
