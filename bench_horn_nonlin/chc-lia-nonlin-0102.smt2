;; Original file: adr_40.smt2
(set-logic HORN)
(declare-fun |array_max$unknown:4| (Int Int Int Int) Bool)
(declare-fun |array_max$unknown:6| (Int Int Int Int) Bool)
(declare-fun |make_array$unknown:9| (Int Int Int) Bool)


(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:7| Int)
         (|$alpha-5:a| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  (|array_max$unknown:4|
                    |$V-reftype:7|
                    |$alpha-5:a|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  true)))
    (=> a!1
        (|array_max$unknown:4|
          |$V-reftype:7|
          |$alpha-5:a|
          |$knormal:3|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:7| Int)
         (|$alpha-5:a| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  (|array_max$unknown:4|
                    |$V-reftype:7|
                    |$alpha-5:a|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  true)))
    (=> a!1
        (|array_max$unknown:4|
          |$V-reftype:7|
          |$alpha-5:a|
          |$knormal:3|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:29| Int)
         (|$knormal:9| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (= |$V-reftype:29| |$knormal:9|)
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|array_max$unknown:6|
                    |$knormal:9|
                    |$alpha-6:m|
                    |$knormal:3|
                    |$alpha-3:n|)
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true)))
    (=> a!1
        (|array_max$unknown:6|
          |$V-reftype:29|
          |$alpha-6:m|
          |$alpha-4:i|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:27| Int)
         (|$knormal:9| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (= |$V-reftype:27| |$knormal:9|)
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  (|array_max$unknown:6|
                    |$knormal:9|
                    |$knormal:11|
                    |$knormal:3|
                    |$alpha-3:n|)
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true)))
    (=> a!1
        (|array_max$unknown:6|
          |$V-reftype:27|
          |$alpha-6:m|
          |$alpha-4:i|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:10|))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-4:i| Int)
         (|$knormal:10| Int)
         (|$knormal:11| Int)
         (|$alpha-6:m| Int)
         (|$knormal:1| Int)
         (|$alpha-3:n| Int))
  (let ((a!1 (and (= |$knormal:3| (+ |$alpha-4:i| 1))
                  (= (not (= 0 |$knormal:10|))
                     (> |$knormal:11| |$alpha-6:m|))
                  (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:10|)))
                  (not (not (= 0 |$knormal:1|)))
                  true
                  (|array_max$unknown:4|
                    |$knormal:11|
                    |$alpha-4:i|
                    |$alpha-4:i|
                    |$alpha-3:n|)
                  true
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:1| Int)
         (|$alpha-4:i| Int)
         (|$alpha-3:n| Int)
         (|$V-reftype:24| Int)
         (|$alpha-6:m| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:1|))
                     (>= |$alpha-4:i| |$alpha-3:n|))
                  (= |$V-reftype:24| |$alpha-6:m|)
                  (not (= 0 |$knormal:1|))
                  true
                  true
                  true)))
    (=> a!1
        (|array_max$unknown:6|
          |$V-reftype:24|
          |$alpha-6:m|
          |$alpha-4:i|
          |$alpha-3:n|)))))
(assert (forall ((|$knormal:25| Int)
         (|$knormal:16| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int)
         (|$knormal:13| Int)
         (|$knormal:14| Int)
         (|$alpha-10:i| Int)
         (|$alpha-9:n| Int)
         (|$V-reftype:21| Int)
         (|$knormal:18| Int))
  (let ((a!1 (= (not (= 0 |$knormal:16|))
                (and (not (= 0 |$knormal:12|))
                     (not (= 0 |$knormal:15|)))))
        (a!2 (= (not (= 0 |$knormal:15|))
                (and (not (= 0 |$knormal:13|))
                     (not (= 0 |$knormal:14|))))))
  (let ((a!3 (and (= |$knormal:25| (- 1))
                  a!1
                  a!2
                  (= (not (= 0 |$knormal:14|)) (<= |$alpha-10:i| 0))
                  (= (not (= 0 |$knormal:13|)) (>= |$alpha-10:i| 0))
                  (= (not (= 0 |$knormal:12|)) (> |$alpha-9:n| 0))
                  (not (= 0 |$knormal:16|))
                  (|make_array$unknown:9|
                    |$V-reftype:21|
                    |$knormal:18|
                    |$alpha-9:n|)
                  true)))
    (=> a!3
        (|array_max$unknown:4|
          |$V-reftype:21|
          |$knormal:18|
          |$alpha-10:i|
          |$alpha-9:n|))))))
(assert (forall ((|$knormal:25| Int)
         (|$knormal:17| Int)
         (|$knormal:27| Int)
         (|$alpha-9:n| Int)
         (|$knormal:16| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int)
         (|$knormal:13| Int)
         (|$knormal:14| Int)
         (|$alpha-10:i| Int))
  (let ((a!1 (= (not (= 0 |$knormal:16|))
                (and (not (= 0 |$knormal:12|))
                     (not (= 0 |$knormal:15|)))))
        (a!2 (= (not (= 0 |$knormal:15|))
                (and (not (= 0 |$knormal:13|))
                     (not (= 0 |$knormal:14|))))))
  (let ((a!3 (and (= |$knormal:25| (- 1))
                  (= (not (= 0 |$knormal:17|))
                     (>= |$knormal:27| |$alpha-9:n|))
                  a!1
                  a!2
                  (= (not (= 0 |$knormal:14|)) (<= |$alpha-10:i| 0))
                  (= (not (= 0 |$knormal:13|)) (>= |$alpha-10:i| 0))
                  (= (not (= 0 |$knormal:12|)) (> |$alpha-9:n| 0))
                  (not (not (= 0 |$knormal:17|)))
                  (not (= 0 |$knormal:16|))
                  (|array_max$unknown:6|
                    |$knormal:27|
                    |$knormal:25|
                    |$alpha-10:i|
                    |$alpha-9:n|))))
    (=> a!3 false)))))
(assert (forall ((|$V-reftype:22| Int)
         (|$alpha-1:n| Int)
         (|$alpha-2:i| Int))
  (=> (and (= |$V-reftype:22| (- |$alpha-1:n| |$alpha-2:i|))
           true
           true)
      (|make_array$unknown:9|
        |$V-reftype:22|
        |$alpha-2:i|
        |$alpha-1:n|))))
(check-sat)
