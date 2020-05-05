;; Original file: adr_132.smt2
(set-logic HORN)
(declare-fun |repeat$unknown:2| (Int Int) Bool)
(declare-fun |succ$unknown:7| (Int Int) Bool)
(declare-fun |repeat$unknown:5| (Int Int Int) Bool)


(assert (forall ((|$knormal:3| Int)
         (|$alpha-3:n| Int)
         (|$knormal:1| Int)
         (|$V-reftype:6| Int)
         (|$alpha-2:f| Int))
  (let ((a!1 (and (= |$knormal:3| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  true
                  (|repeat$unknown:2| |$V-reftype:6| |$alpha-2:f|)
                  true)))
    (=> a!1 (|repeat$unknown:2| |$V-reftype:6| |$alpha-2:f|)))))
(assert (forall ((|$knormal:13| Int) (|$V-reftype:15| Int) (succ Int))
  (=> (and (= |$knormal:13| 0)
           (|succ$unknown:7| |$V-reftype:15| succ)
           true)
      (|repeat$unknown:2| |$V-reftype:15| succ))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-3:n| Int)
         (|$knormal:1| Int)
         (|$V-reftype:20| Int)
         (|$knormal:9| Int)
         (|$knormal:7| Int)
         (|$alpha-4:s| Int))
  (let ((a!1 (and (= |$knormal:3| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (= |$V-reftype:20| |$knormal:9|)
                  (not (not (= 0 |$knormal:1|)))
                  (|repeat$unknown:5|
                    |$knormal:7|
                    |$alpha-4:s|
                    |$knormal:3|)
                  true
                  true
                  (|repeat$unknown:2| |$knormal:9| |$knormal:7|))))
    (=> a!1
        (|repeat$unknown:5|
          |$V-reftype:20|
          |$alpha-4:s|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-3:n| Int)
         (|$knormal:1| Int)
         (|$knormal:7| Int)
         (|$alpha-4:s| Int))
  (let ((a!1 (and (= |$knormal:3| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (not (not (= 0 |$knormal:1|)))
                  (|repeat$unknown:5|
                    |$knormal:7|
                    |$alpha-4:s|
                    |$knormal:3|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:18| Int)
         (|$alpha-4:s| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (= |$V-reftype:18| |$alpha-4:s|)
                  (not (= 0 |$knormal:1|))
                  true
                  true)))
    (=> a!1
        (|repeat$unknown:5|
          |$V-reftype:18|
          |$alpha-4:s|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:17| Int)
         (|$knormal:15| Int)
         (|$alpha-5:n| Int)
         (|$knormal:13| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:17|))
                     (>= |$knormal:15| |$alpha-5:n|))
                  (= |$knormal:13| 0)
                  (not (not (= 0 |$knormal:17|)))
                  (|repeat$unknown:5|
                    |$knormal:15|
                    |$knormal:13|
                    |$alpha-5:n|))))
    (=> a!1 false))))
(assert (forall ((|$V-reftype:16| Int) (|$alpha-1:x| Int))
  (=> (and (= |$V-reftype:16| (+ |$alpha-1:x| 1)) true)
      (|succ$unknown:7| |$V-reftype:16| |$alpha-1:x|))))
(check-sat)
