(declare-var p (Array Int Int))
(declare-var g (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var res Int)
(declare-var res1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv p g 0 1 N))

(rule (=> (and (inv p g i res N) (< i N)
  (= res1 (ite (= (select p i) (select g i)) res 0))
  (= i1 (+ i 1))) (inv p g i1 res1 N)))

(rule (=> (and (inv p g i res N) (not (< i N)) (= res 1)
  (<= 0 i1) (< i1 N) (not (= (select p i1) (select g i1)))) fail))

(query fail)
