#lang racket

(require "grammars.rkt"
         "automata.rkt")

;;;; stuff to do with number processing

(define number?/RE '(O U (I • ((O U I) *))))
(define even?/RE '(O U ((I • ((O U I) *)) • O)))
(define odd?/RE '(O U ((I • ((O U I) *)) • I)))


(define number?/DFA (RE->DFA number?/RE))
(define even?/DFA (RE->DFA even?/RE))
(define odd?/DFA (RE->DFA odd?/RE))

;; stuff to do with boolean logic
(define valid?1/CFG
  '((True -> 't        ('not False) ('andbegin And 'andend) ('orbegin Or 'orend))
    (False -> 'f       ('not True) ('andbegin Nand 'andend) ('orbegin Nor 'orend))
    (And -> ('t And) ('f And-Fail) ('not And1n) '(andbegin And 'andend) '(orbegin Or 'orend))
    (And1 -> ('t And) ('f And-Fail) ('not And1n) '(andbegin And 'andend) '(orbegin Or 'orend))
    (And1n -> ('t And-Fail) ('f And-Fail) ('not And1) '(andbegin Nand 'andend) '(orbegin Nor 'orend))
    (And-Fail ->)
    (And-Fail1 ->)
    (And-Fail1n ->)
    
    (Nand -> ('t AF) ('f Nand-Fail) ('not AF1n) '(andbegin And 'andend) '(orbegin Or 'orend))
    (Nand1 ->)
    (Nand1n ->)
    (Nand-Fail ->)
    (Nand-Fail1 ->)
    (Nand-Fail1n ->)

    (Or -> ('t OS) ('f OT) ('not OT1n) '(andbegin And 'andend) '(orbegin Or 'orend))
    (Or1 ->)
    (Or1n ->)
    (Or-Succ ->)
    (Or-Succ1 ->)
    (OT-Succ1n ->)
    
    (Nor -> ('t OS) ('f AFF) ('not OF1n) '(andbegin And 'andend) '(orbegin Or 'orend))
    (Nor1 ->)
    (NOr1n ->)    
    (Nor-Succ ->)
    (Nor-Succ1 ->)
    (Nor-Succ1n ->)))


