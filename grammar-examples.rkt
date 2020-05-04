#lang racket

(require "grammars.rkt"
         "automata.rkt")
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
        AnBn Bool/SuperSimp Bool/Simp Bool))

(define (CFG-tests) (andmap CFG? CFGs))

(define A*/CNF (CFG->CNF A*/CFG))
(define A+/CNF (CFG->CNF A+/CFG))
(define AUB/CNF (CFG->CNF AUB/CFG))
(define AUB*/CNF (CFG->CNF AUB*/CFG))
(define AUB+/CNF (CFG->CNF AUB+/CFG))
(define AUB•c+*/CNF (CFG->CNF AUB•c+*/CFG))
(define AnBn/CNF (CFG->CNF AnBn))
(define Bool/SuperSimp/CNF (CFG->CNF Bool/SuperSimp))
(define Bool/Simp/CNF (CFG->CNF Bool/Simp))
(define Bool/CNF (CFG->CNF Bool))

(define CNFs
  (list A*/CNF A+/CNF AUB/CNF AUB*/CNF AUB+/CNF AUB•c+*/CNF
        AnBn/CNF Bool/SuperSimp/CNF Bool/Simp/CNF Bool/CNF))

(define (CNF-tests)
  (and (andmap CFG? CNFs)
       (andmap CNF? CNFs)))

(if (and (CFG-tests) (CNF-tests))
    (displayln "CFG->CNF conversion tests passed")
    (error "CFG->CNF conversion tests failed"))

;;;; some PDAs
(define A*/PDA (CNF->PDA A*/CNF))
(define AUB/PDA (CNF->PDA AUB/CNF))

