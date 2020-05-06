#lang racket

(require "grammars.rkt"
         "G-to-M.rkt"
         "queries.rkt")
;; implementations of a few grammars, using
;; features from grammars.rkt

;; some REs
(define A* '(a *))
(define A+ '(a +))
(define AUB '(a U b))
(define AUB* '((a U b) *))
(define AUB+ '((a U b) +))
(define AUB•c+*  '((a U ((b • c) +)) *))

;; some DFAs
(define A*/DFA (RE->DFA A*))
(define A+/DFA (RE->DFA A+))
(define AUB/DFA (RE->DFA AUB))
(define AUB*/DFA (RE->DFA AUB*))
(define AUB+/DFA (RE->DFA AUB+))
(define AUB•c+*/DFA (RE->DFA AUB•c+*))

(define (DFA-tests)
  (let* ((A*-Σ50 (find-words A*/DFA 50))
         (A+-Σ50 (find-words A+/DFA 50)))
    (and
     (member '() A*-Σ50)
     (not (member '() A+-Σ50))
     (equal? (cdr A*-Σ50) A+-Σ50))
    (equal? '((a) (b)) (find-words AUB/DFA 100))
    (equal? (length (find-words AUB*/DFA 2)) 7)

    (accept? AUB•c+*/DFA '())
    (accept? AUB•c+*/DFA '(a))
    (accept? AUB•c+*/DFA '(a b c))
    (not (accept? AUB•c+*/DFA '(a b a c)))
    (accept? AUB•c+*/DFA '(a a a a b c b c a b c b c b c b c a b c))
    (not (accept? AUB•c+*/DFA '(a a a a b c b c a b a c b c b c b c a b c)))))

(if (DFA-tests)
    (displayln "DFA tests passed")
    (error "DFA tests failed"))

;; Testing RE->CFG->CNF conversion
(define A*/CFG (RE->CFG A*))
(define A+/CFG (RE->CFG A+))
(define AUB/CFG (RE->CFG AUB))
(define AUB*/CFG (RE->CFG AUB*))
(define AUB+/CFG (RE->CFG AUB+))
(define AUB•c+*/CFG (RE->CFG AUB•c+*))

(define AnBn '((S -> ε (A S B))
               (A -> 'a)
               (B -> 'b)))

(define AnBn2 '((S -> ε ('a S 'b))))

(define DumbBool '((S -> ('orbegin S* 'orend))
                   (S* -> ε (S S*))))

(define Bool/SuperSimp
  '((S -> 'p ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define Bool/Simp
  '((S -> 'p ('not S) ('andbegin S* 'andend) ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define Bool
  '((S -> 'T 'F 'p 'q
       ('not S)
       ('andbegin S* 'andend)
       ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define CFGs
  (list A*/CFG A+/CFG AUB/CFG AUB*/CFG AUB+/CFG AUB•c+*/CFG
        AnBn AnBn2 Bool/SuperSimp Bool/Simp Bool))

(define (CFG-tests) (andmap CFG? CFGs))

(define A*/CNF (CFG->CNF A*/CFG))
(define A+/CNF (CFG->CNF A+/CFG))
(define AUB/CNF (CFG->CNF AUB/CFG))
(define AUB*/CNF (CFG->CNF AUB*/CFG))
(define AUB+/CNF (CFG->CNF AUB+/CFG))
(define AUB•c+*/CNF (CFG->CNF AUB•c+*/CFG))
(define AnBn/CNF (CFG->CNF AnBn))
(define DumbBool/CNF (CFG->CNF DumbBool))
(define Bool/SuperSimp/CNF (CFG->CNF Bool/SuperSimp))
(define Bool/Simp/CNF (CFG->CNF Bool/Simp))
(define Bool/CNF (CFG->CNF Bool))
(define AnBn2/CNF (CFG->CNF AnBn2))

(define CNFs
  (list A*/CNF A+/CNF AUB/CNF AUB*/CNF AUB+/CNF AUB•c+*/CNF
        AnBn/CNF AnBn2/CNF Bool/SuperSimp/CNF Bool/Simp/CNF Bool/CNF))

(define (CNF-tests)
  (and (andmap CFG? CNFs)
       (andmap CNF? CNFs)))

(if (and (CFG-tests)
         (CNF-tests))
    (displayln "CFG->CNF conversion tests passed")
    (error "CFG->CNF conversion tests failed"))

;;;; some PDAs
(define A*/PDA (CNF->PDA A*/CNF))
(define A+/PDA (CNF->PDA A+/CNF))
(define AUB/PDA (CNF->PDA AUB/CNF))
(define AUB*/PDA (CNF->PDA AUB*/CNF))
(define AUB+/PDA (CNF->PDA AUB+/CNF))
(define AUB•c+*/PDA (CNF->PDA AUB•c+*/CNF))
(define AnBn/PDA (CNF->PDA AnBn/CNF))
(define AnBn2/PDA (CNF->PDA AnBn2/CNF))
(define DumbBool/PDA (CNF->PDA DumbBool/CNF))
(define Bool/SuperSimp/PDA (CNF->PDA Bool/SuperSimp/CNF))
(define Bool/Simp/PDA (CNF->PDA Bool/Simp/CNF))
(define Bool/PDA (CNF->PDA Bool/CNF))

(define (PDA-tests)
  (and (equal? '(() (a) (a a) (a a a))
               (find-words A*/PDA 3))
       (equal? (cdr (find-words A*/PDA 10))
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
       (equal? (find-words AnBn/PDA 10) (find-words AnBn2/PDA 10))
       
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

(if (PDA-tests)
    (displayln "PDA tests passed")
    (error "PDA tests failed"))

