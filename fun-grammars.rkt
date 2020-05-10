#lang racket

(require "grammars.rkt"
         "machines.rkt"
         "basics.rkt"
         "queries.rkt"
         "G-to-M.rkt"
         "draw-automata.rkt"
         2htdp/universe)

(provide (all-defined-out))
;;;; stuff to do with number processing

(define number?/RE '(O U (I • ((O U I) *))))
(define even?/RE '(O U ((I • ((O U I) *)) • O)))
(define odd?/RE '(O U ((I • ((O U I) *)) • I)))

(define number?/DFA (RE->DFA number?/RE))
(define even?/DFA (RE->DFA even?/RE))
(define odd?/DFA (RE->DFA odd?/RE))

;; stuff to do with boolean logic

#|
;; keeping track of minimization progress

;; PRE any minimization efforts
> (length (Automaton-all-states Val-of))
182
> (length (Automaton-transition-function Val-of))
381
>

;; AFTER CNF minimization efforts
> (length (Automaton-all-states Val-of))
70
> (length (Automaton-transition-function Val-of))
262

;; AFTER PDA minimization efforts
> (length (Automaton-all-states (minimize-PDA Val-of)))
43
(length (Automaton-transition-function (minimize-PDA Val-of)))
194
|#


(define val-of
  '((True ->
          't
          ('not False)
          ('andbegin True* 'andend)
          ('orbegin Value* True Value* 'orend))
    
    (True* -> ε (True True*))

    (False ->
           'f
           ('not True)
           ('andbegin Value* False Value* 'andend)
           ('orbegin False* 'orend))
    (False* -> ε (False False*))
    (Value -> True False)
    (Value* -> ε (Value Value*))))

(define Val-of (CNF->PDA (CFG->CNF val-of)))
(define Val-of/min (minimize-PDA Val-of))



(define Eng
  '((P -> (Subject VerbPhrase))
    (Subject -> (Adjective* ProperNoun) (Article Adjective* Noun))
    (Adjective* -> ε (Adjective Adjective*))
    (Adjective -> 'fast 'slow 'big 'small 'beautiful 'sad 'melancholy
               'green)
    (ProperNoun -> 'Ben 'Tessa 'Trudi 'Benzo 'Robert 'Google 'God)
    (Noun -> 'car 'love 'book 'movie 'graph 'city 'country)
    (VerbPhrase -> Verb (Adverb Verb) (Verb Article Noun))
    (Adverb -> 'quickly 'fastly 'slowly 'wonderfully 'greasily)
    (Verb -> 'is 'knows 'runs 'drives 'bakes 'shapes)
    (Article -> 'an 'the)))

(define Eng/min (minimize-PDA (CNF->PDA (CFG->CNF Eng))))

;; drawing

(big-bang Eng/min
    [to-draw draw-automaton])





