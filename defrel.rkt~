#lang racket


;; takes a terminal
;; and turns it into a
;; 1-line CFG
(define-syntax goal
  (syntax-rules ()
    [(_ e1 ...) `((,(gensym 'S) -> ,e1 ...))]))



;; here is an example of how we would write even?
;; on binary numbers  (not reversed)
#;
(defrel (even? x)
  (conde
   [(== x '(1 0))]
   [(fresh (a d)
           (== x `(,a . ,d))
           (conde
            [(== a '1)]
            [(== a '0)])
           (even? d))]))

#;
(defrel (appendo e1 e2 o)
  (conde
   [(== e1 '()) (== e2 o)]
   [(fresh (a d o2)
           (== e1 `(,a . ,d))
           (== o `(,a . ,o2))
           (appendo d e2 o2))]))


(define Σ '(a b c))





(define appendo
  '((S -> (L L O))
    (O -> L L)
    (L1 -> '() ('a L1) ('b L1) ('c L1))
    ))