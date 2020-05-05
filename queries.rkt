#lang racket

(require "automata.rkt")

(provide  find-words
          accept?)


;; Sets
(define (set-cons x s)
  (if (member x s) s (cons x s)))
(define (set-union s1 s2) (foldr set-cons s2 s1))
(define (set-equal? s1 s2)
  (and (= (length s1) (length s2))
       (andmap (λ (x) (member x s2)) s1)
       (andmap (λ (x) (member x s1)) s2)))

(define-syntax accept?
  (syntax-rules ()
    [(_ M w) (accept? M w #f)]
    [(_ M w disp?)
     (run M
          `(,w)
          (λ (_) #f)
          (λ (a) (null? (car a)))
          (list (λ (_1 _2 acc) (cdr acc)))
          #f
          (λ (_1 _2) #t)
          (λ (_ a) (if (null? (car a)) '() (list (caar a))))
          disp?)]))

(define-syntax find-words
  (syntax-rules ()
    [(_ M k) (find-words M k #f)]
    [(_ M k disp?)
     (run
      M
      '(())
      (λ (a) (> (length (car a)) k))
      (λ (a) #t)
      (list (λ (_ i a) (cons i a)))
      '()
      (λ (a ans)
        (let ((w (reverse (car a)))
              (ans (ans)))
          (if (member w ans)
              ans
              (cons w ans))))
      (λ (Σ _) Σ)
      disp?)]))





