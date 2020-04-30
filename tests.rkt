#lang racket

(require "automata.rkt")
(require "easy-examples.rkt")
;;; tests
(define run-tests? #t)


(define (tests)
  (and
   (accept? A* '())
   (accept? A* '(a))
   (accept? A* '(a a a a))
   (not (accept? A* '(a a a a b)))
   (not (accept? A+B* '()))
   (accept? A* '(a))
   (accept? A+B* '(a a a a))
   (accept? A+B* '(a a a a b))
   (not (accept? A+B* '(b b b b)))
   (not (accept? A+B* '(b a a a a a)))
   (accept? A*UB* '())
   (accept? A*UB* '(a a a a a))
   (not (accept? A*UB* '(a b a b a b a)))
   (accept? A*UB* '(b))
   (accept? A*UB* '(b b b b b))
   (accept? |A+UB|*|CUB|+ '(a a a b a b a b b c b c b c b))
   (let ((v1 (find-words A+B* 5)))
     (and
      (not (member '() v1))
      (member '(a) v1)
      (member '(a a b b) v1)
      (not (member '(a a b b a) v1))))
   (let ((v2 (find-words AnBn 4)))
     (and
      (member '() v2)
      (member '(a a b b) v2)
      (not (member '(a b a b) v2))))
   ;; this is slow
   (= 5050 (length (find-words A+B* 100)))))

(define (bool-tests)
  (let ((v (find-words Bool 4)))
    (and
     (member '(orbegin andbegin andend orend) v)
     (member '(orbegin q p orend) v)
     (member '(orbegin not p orend) v)
     (not (member '(orend not p orend) v))
     (not (member '(andbegin p p p andend) v)))))

;; cpu time: 12928 real time: 12107 gc time: 249

(time
 (if run-tests?
     (let ((b (tests))
           (bool-passes (bool-tests)))
       (begin
         (if b
             (displayln "Tests Pass")
             (error "Tests Fail!!!"))
         (if bool-passes
             (displayln "Bool tests pass")
             (error "Bool tests fail!!"))))
     (displayln "Tests skipped.")))

