#lang racket

(require "basics.rkt")

(provide find-words accept? random-word)

(define-syntax accept?
  (syntax-rules ()
    [(_ M w) (accept? M w #f)]
    [(_ M w disp?)
     (run M
          `(,w)
          (λ (_) #f)
          (λ (e) e)
          (λ (a) (null? (car a)))
          (list (λ (_1 _2 acc) (cdr acc)))
          #f
          (λ (a A) #t)
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
      (λ (x) #f)
      (λ (a) #t)
      (list (λ (_ i a) (snoc i a)))
      '()
      (λ (a A) (set-cons (car a) A))
      (λ (Σ _) Σ)
      disp?)]))

(define-syntax random-word
  (syntax-rules ()
    [(_ M k) (find-words M k #f)]
    [(_ M k disp?)
     (run
      M
      '(())
      (λ (a) #f)
      (λ (x) x)
      (λ (a) #t)
      (list (λ (_ i a) (snoc i a)))
      #f
      (λ (a _) a)
      (λ (Σ _) (shuffle Σ))
      'dfs
      disp?)]))





