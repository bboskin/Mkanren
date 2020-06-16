#lang racket

(require "grammars.rkt"
         "G-to-M.rkt"
         "queries.rkt"
         "examples.rkt"
         "automata.rkt"
         "basics.rkt")

(define test? #t)
;; implementations of a few grammars, using
;; features from grammars.rkt


(define (DFA-tests)
  (let* ((A*-Σ50 (find-words A*/DFA 50))
         (A+-Σ50 (find-words A+/DFA 50)))
    (and
     (member '() A*-Σ50)
     (not (member '() A+-Σ50))
     (set-equal?? (remove '() A*-Σ50) A+-Σ50)
     (set-equal?? '((a) (b)) (find-words AUB/DFA 100))
     (= (length (find-words AUB*/DFA 2)) 7)
     
     (accept? AUB•c+*/DFA '())
     (accept? AUB•c+*/DFA '(a))
     (accept? AUB•c+*/DFA '(a b c))
     (not (accept? AUB•c+*/DFA '(a b a c)))
     (accept? AUB•c+*/DFA '(a a a a b c b c a b c b c b c b c a b c))
     (not (accept? AUB•c+*/DFA '(a a a a b c b c a b a c b c b c b c a b c))))))




(define CFGs
  (list A*/CFG A+/CFG AUB/CFG AUB*/CFG AUB+/CFG AUB•c+*/CFG
        AnBn AnBn2 Bool/SuperSimp Bool/Simp Bool))

(define (CFG-tests) (andmap CFG? CFGs))


(define CNFs
  (list A*/CNF A+/CNF AUB/CNF AUB*/CNF AUB+/CNF AUB•c+*/CNF
        AnBn/CNF AnBn2/CNF Bool/SuperSimp/CNF Bool/Simp/CNF Bool/CNF))



(define (PDA-tests)
  (and (set-equal?? '(() (a) (a a) (a a a))
               (find-words A*/PDA 3))
       (set-equal?? (remove '() (find-words A*/PDA 10))
                    (find-words A+/PDA 10))
       (set-equal?? (find-words AUB/PDA 100) '((a) (b)))
       (accept? AUB*/PDA '())
       (accept? AUB*/PDA '(a b a b b a a a a a))
       (not (accept? AUB*/PDA '(a b a b b c a a a a a)))
       (not (accept? AUB+/PDA '()))
       (accept? AUB+/PDA '(a b a b b a a a a a))
       (equal? (find-words AUB•c+*/PDA 0) '(()))
       (accept? AUB•c+*/PDA '(a b c a b c b c b c))
       (not (accept? AUB•c+*/PDA '(a b c a b b c b c)))
       (set-equal?? (find-words AnBn/PDA 10) (find-words AnBn2/PDA 10))
       
       (set-equal?? (find-words AUB•c+*/PDA 2) '(() (a) (a a) (b c)))
       (set-equal?? (find-words AUB•c+*/PDA 4) (find-words AUB•c+*/DFA 4))
       (set-equal?? (find-words A*/PDA 4) (find-words A*/DFA 4))
       (set-equal?? (find-words A+/PDA 4) (find-words A+/DFA 4))
       (set-equal?? (find-words AUB+/PDA 4) (find-words AUB+/DFA 4))
       
       (accept? Bool/PDA
                '(andbegin not orbegin p q orend p not q not not p andbegin andend andend))
       (not
        (accept? Bool/PDA
                 '(andbegin not orbegin p q andbegin orend p not q not not p andbegin andend andend)))))


;; testing automata generated from performing set operations on grammars



(define (Set-tests)
  (and
   (set-equal?? '()
                (set-intersection
                 (find-words A*/DFA 5)
                 (find-words (M-Negation A*/DFA) 5)))
   
   (set-equal?? (find-words A*UAnBn/PDA 4)
                (set-union (find-words A*/PDA 4) (find-words AnBn/PDA 4)))
   (set-equal?? (find-words A*UA*/PDA 4)
                (find-words A*/DFA 4))
   (accept? 2Bool/PDA '(p p))
   (not (accept? 2Bool/PDA '(orbegin)))
   (not (accept? 2Bool/PDA '(p)))
   (accept? 2Bool/PDA '(not not not p andbegin orbegin orend p q p not orbegin orend andend))
   (not (accept? 2Bool/PDA '(andbegin p andbegin orbegin orend p q p not orbegin orend andend andeng)))
   ;; New tests to test intersection
   (set-equal?? (find-words A/DFA 100) '((a)))
   (set-equal?? (find-words A+/DFA2 20)
                (find-words A+/PDA 20))
   (set-equal?? (take-words A+/DFA 5)
                (take-words (M-Intersection A+BnCn A*/DFA) 5))
   (set-equal?? (find-words AUB/DFA 3)
                (find-words (M-Intersection
                             AUB/DFA
                             (M-Union AUB/PDA A+/PDA)) 3))
   (set-equal?? (find-words 2-stack/min 10)
                (find-words (M-Union
                             (M-Intersection AUB/PDA AnBnCn)
                             2-stack/min) 10))
   (set-equal?? (find-words 2-stack/min 10)
                (find-words (M-Union
                             2-stack/min
                             (M-Intersection AnBnCn AUB/PDA)) 10))
   (set-equal?? (find-words A*B*C* 2)
                (find-words (M-Concatenation
                             (CNF->PDA (CFG->CNF (RE->CFG '(a *))))
                             (M-Concatenation
                              (RE->DFA '(b *))
                              (CNF->PDA (CFG->CNF (RE->CFG '(c *))))))
                            2))
   #;
   (set-equal?? (find-words E 1)
                (find-words (M-Difference A*/DFA A+/DFA) 1))))



(define (Min-tests)
  (and
   (set-equal?? (find-words A*/min 10) (find-words A*/DFA 10))
   (set-equal?? (find-words A+/min 10) (find-words A+/DFA 10))
   (set-equal?? (find-words AUB/min 10) (find-words AUB/DFA 10))
   (set-equal?? (find-words AUB*/min 4) (find-words AUB*/DFA 4))
   (set-equal?? (find-words AUB+/min 4) (find-words AUB+/DFA 4))
   (set-equal?? (find-words AUB•c+*/min 4) (find-words AUB•c+*/DFA 4))
   (set-equal?? (find-words AnBn/min 10) (find-words AnBn/PDA 10))
   (set-equal?? (find-words AnBn2/min 10) (find-words AnBn2/PDA 10))
   (set-equal?? (find-words DumbBool/min 6) (find-words DumbBool/PDA 6))
   (set-equal?? (find-words Bool/SuperSimp/min 4)
                (find-words Bool/SuperSimp/PDA 4))
   (set-equal?? (find-words Bool/Simp/min 4)
                (find-words Bool/Simp/PDA 4))
   (set-equal?? (find-words Bool/min 3)
                (find-words Bool/PDA 3))
   (set-equal?? (find-words 2-stack/min 3)
                (find-words 2-stack/PDA 3))))



(if test?
    (begin
      (if (time (DFA-tests))
          (displayln "DFA tests passed")
          (error "DFA tests failed"))
      
      (if (time (and (CFG-tests)
               (and (andmap CFG? CNFs)
                    (andmap CNF? CNFs))))
          (displayln "CFG->CNF conversion tests passed")
          (error "CFG->CNF conversion tests failed"))
      
      (if (time (PDA-tests))
          (displayln "PDA tests passed")
          (error "PDA tests failed"))
      
      (if (time (Set-tests))
          (displayln "Set operation PDA tests passed")
          (error "Set tests failed"))
      
      (if (time (Min-tests))
          (displayln "Minimization-tests passed")
          (error "Minimization tests failed")))
    (displayln "all tests skipped"))