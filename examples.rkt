#lang racket

(require "grammars.rkt"
         "G-to-M.rkt"
         "automata.rkt")

(provide (all-defined-out))


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

;; Some CNFs
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

(define A*UAnBn/PDA (CNF->PDA (CFG->CNF (G-Union A*/CFG AnBn))))
(define A*UA*/PDA (CNF->PDA (CFG->CNF (G-Union A*/CFG A+/CFG))))

(define 2Bool/PDA (CNF->PDA (CFG->CNF (G-Concatenation Bool Bool))))

;; testing minimized automata (for some reason i cant require machines.rkt)

(define A*/min (minimize-PDA A*/DFA))
(define A+/min (minimize-PDA A+/DFA))
(define AUB/min (minimize-PDA AUB/DFA))
(define AUB*/min (minimize-PDA AUB*/DFA))
(define AUB+/min (minimize-PDA AUB+/DFA))
(define AUB•c+*/min (minimize-PDA AUB•c+*/DFA))
(define AnBn/min (minimize-PDA AnBn/PDA))
(define AnBn2/min (minimize-PDA AnBn2/PDA))
(define DumbBool/min (minimize-PDA DumbBool/PDA))
(define Bool/SuperSimp/min (minimize-PDA Bool/SuperSimp/PDA))
(define Bool/Simp/min (minimize-PDA Bool/Simp/PDA))
(define Bool/min (minimize-PDA Bool/PDA))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tests involving multiple stacks, and more minimization

(define 2-stack/PDA
  (Automaton
   'S
   '(F)
   '(S F)
   '((S a S preserve-stack (pop on #t push (A)))
     (S b S (pop on #t push (Z)) preserve-stack)
     (S c F (pop on Z push ()) (pop on A push ()))
     (F c F (pop on Z push ()) (pop on A push ())))
   '(a b c)
   '((Z)
     (A))))

(define 2-stack/min (minimize-PDA 2-stack/PDA))
