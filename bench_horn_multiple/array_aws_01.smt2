(declare-rel f (Int Int Int (Array Int Int)))
(declare-rel g (Int Int Int (Array Int Int)))

(declare-var json (Array Int Int))
(declare-var end Int)
(declare-var end1 Int)
(declare-var start Int)
(declare-var len Int)

(declare-rel fail ())

(rule (=> (and (> len 0)
  (and (= (select json start) 1)
  (or (= start 0) (not (= (select json (- start 1)) 2))))
  (= end (+ start 1)))
    (f end start len json)))

(rule (=> (and (f end start len json)
    (< end len)
    (not (and (= (select json end) 1)
        (or (= end 0) (not (= (select json (- end 1)) 2)))))
    (= end1 (+ end 1))) (f end1 start len json)))

(rule (=> (and
    (f end start len json)
    (not (and (< end len)
          (not (and (= (select json end) 1)
              (or (= end 0) (not (= (select json (- end 1)) 2)))))))
    (= end1 (ite (and (< end len)
      (and (= (select json end) 1)
      (or (= end 0) (not (= (select json (- end 1)) 2))))) (+ end 1) (+ len 1))))
  (g end1 start len json)))

(rule (=> (and (g end start len json) (not
    (or (= end (+ len 1))
        (and (< start len) (<= (+ start 2) end) (<= end len)
        (and (= (select json (- end 1)) 1)
        (or (= (- end 1) 0) (not (= (select json (- (- end 1) 1)) 2))))))))
    fail))

(query fail)
