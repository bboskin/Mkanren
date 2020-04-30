#lang racket

(require "grammars.rkt"
         "automata.rkt")
;; implementations of a few grammars, using
;; features from grammars.rkt

(define A
  '((S -> 'a)
    (S -> P)
    (P -> 'b)))

(define AnBn
  '((S -> ε)
    (S -> 'a S 'b)))

(define Bool
  '((S -> 'T)
    (S -> 'F)
    (S -> 'p)
    (S -> 'q)
    (S -> 'not S)
    (S -> 'andbegin S* 'andend)
    (S -> 'orbegin S* 'orend)
    (S* -> ε)
    (S* -> S S*)))
