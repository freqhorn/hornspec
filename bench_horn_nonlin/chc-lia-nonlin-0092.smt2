;; Original file: adr_91.smt2
(set-logic HORN)
(declare-fun |gib$unknown:4| (Int Int Int Int) Bool)


(assert (forall ((|$knormal:6| Int)
         (|$alpha-3:n| Int)
         (|$knormal:2| Int)
         (|$knormal:13| Int)
         (|$knormal:1| Int)
         (|$V-reftype:21| Int)
         (|$knormal:8| Int)
         (|$knormal:15| Int)
         (|$alpha-2:b| Int)
         (|$alpha-1:a| Int))
  (let ((a!1 (and (= |$knormal:6| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-3:n| 1))
                  (= |$knormal:13| (- |$alpha-3:n| 2))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (= |$V-reftype:21| (+ |$knormal:8| |$knormal:15|))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|gib$unknown:4| |$knormal:8|
                                   |$knormal:6|
                                   |$alpha-2:b|
                                   |$alpha-1:a|)
                  (|gib$unknown:4| |$knormal:15|
                                   |$knormal:13|
                                   |$alpha-2:b|
                                   |$alpha-1:a|)
                  true
                  true
                  true)))
    (=> a!1
        (|gib$unknown:4| |$V-reftype:21|
                         |$alpha-3:n|
                         |$alpha-2:b|
                         |$alpha-1:a|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-3:n| Int)
         (|$knormal:2| Int)
         (|$knormal:13| Int)
         (|$knormal:1| Int)
         (|$knormal:8| Int)
         (|$alpha-2:b| Int)
         (|$alpha-1:a| Int))
  (let ((a!1 (and (= |$knormal:6| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-3:n| 1))
                  (= |$knormal:13| (- |$alpha-3:n| 2))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|gib$unknown:4| |$knormal:8|
                                   |$knormal:6|
                                   |$alpha-2:b|
                                   |$alpha-1:a|)
                  true
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-3:n| Int)
         (|$knormal:2| Int)
         (|$knormal:13| Int)
         (|$knormal:1| Int)
         (|$knormal:8| Int)
         (|$alpha-2:b| Int)
         (|$alpha-1:a| Int))
  (let ((a!1 (and (= |$knormal:6| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-3:n| 1))
                  (= |$knormal:13| (- |$alpha-3:n| 2))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|gib$unknown:4| |$knormal:8|
                                   |$knormal:6|
                                   |$alpha-2:b|
                                   |$alpha-1:a|)
                  true
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-3:n| Int)
         (|$knormal:2| Int)
         (|$knormal:13| Int)
         (|$knormal:1| Int)
         (|$knormal:8| Int)
         (|$alpha-2:b| Int)
         (|$alpha-1:a| Int))
  (let ((a!1 (and (= |$knormal:6| (- |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-3:n| 1))
                  (= |$knormal:13| (- |$alpha-3:n| 2))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|gib$unknown:4| |$knormal:8|
                                   |$knormal:6|
                                   |$alpha-2:b|
                                   |$alpha-1:a|)
                  true
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:16| Int)
         (|$alpha-1:a| Int)
         (|$alpha-2:b| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (= |$V-reftype:16| |$alpha-1:a|)
                  (not (= 0 |$knormal:1|))
                  true
                  true
                  true)))
    (=> a!1
        (|gib$unknown:4| |$V-reftype:16|
                         |$alpha-3:n|
                         |$alpha-2:b|
                         |$alpha-1:a|)))))
(assert (forall ((|$knormal:2| Int)
         (|$alpha-3:n| Int)
         (|$knormal:1| Int)
         (|$V-reftype:18| Int)
         (|$alpha-2:b| Int)
         (|$alpha-1:a| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:2|)) (= |$alpha-3:n| 1))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-3:n| 0))
                  (= |$V-reftype:18| |$alpha-2:b|)
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:2|))
                  true
                  true
                  true)))
    (=> a!1
        (|gib$unknown:4| |$V-reftype:18|
                         |$alpha-3:n|
                         |$alpha-2:b|
                         |$alpha-1:a|)))))
(assert (forall ((|$knormal:26| Int)
         (|$knormal:24| Int)
         (|$knormal:19| Int)
         (|$knormal:17| Int)
         (|$knormal:18| Int)
         (|$alpha-6:b| Int)
         (|$alpha-5:a| Int)
         (|$alpha-4:n| Int))
  (let ((a!1 (= (not (= 0 |$knormal:19|))
                (and (not (= 0 |$knormal:17|))
                     (not (= 0 |$knormal:18|))))))
  (let ((a!2 (and (= (not (= 0 |$knormal:26|)) (>= |$knormal:24| 0))
                  a!1
                  (= (not (= 0 |$knormal:18|)) (>= |$alpha-6:b| 0))
                  (= (not (= 0 |$knormal:17|)) (>= |$alpha-5:a| 0))
                  (not (not (= 0 |$knormal:26|)))
                  (not (= 0 |$knormal:19|))
                  (|gib$unknown:4| |$knormal:24|
                                   |$alpha-4:n|
                                   |$alpha-6:b|
                                   |$alpha-5:a|))))
    (=> a!2 false)))))
(check-sat)
