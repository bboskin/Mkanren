#lang racket

;;;;
;; a first start at implementing
;; a minikanren-style way of defining relations
;; using automata.


(define ( o)
  (λ (w)4 ))




;; how I'd want to define even?o


#;
(derel even?o
  (conde
   [(== x '(0))]
   [('(1 0) *) even?o]))

;; how I'd want to define boolo
#;
(defrel boolo
  (conde
   [(== x #t)]
   [(== x #f)]
   {}))