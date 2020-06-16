#lang racket


(require "basics.rkt" "automata.rkt")

#|

Types used in the file
- Word : (List Letter)
- Input : Letter U Word

|#

;; i->δ : Input -> Transition-Function
(define (i->δ S F i)
  (match F
    [`(,cs ...) (map (λ (c) `(,S ,c ,F)) cs)]
    [c `((,S ,c ,F))]))

;; == : Input -> Automaton
(define ==
  (λ (i)
    (let* ((S (gensym 'S))
           (F `(,(gensym 'F))))
      (let* ((δ (i->δ S F i))
             (Σ (remove 'ε (map cadr δ)))
             (Γ (map (λ (Γ) (map car Γ)) δ))
             (A (set-union (map car Γ))))
        (Automaton S F A δ Σ Γ)))))