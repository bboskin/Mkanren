#lang racket

(require "basics.rkt")

(provide find-words accept? random-word take-words)

(define-syntax accept?
  (syntax-rules ()
    [(_ M w) (accept? M w #f)]
    [(_ M w disp?)
     (run/fast M
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
     (run/bfs
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
    [(_ M k) (random-word M k #f)]
    [(_ M k disp?)
     (run/fast
      M
      '(())
      (λ (a) #f)
      (λ (x) x)
      (λ (a) #t)
      (list (λ (_ i a) (snoc i a)))
      #f
      (λ (a A) (if A A (if (<= k (length (car a))) (car a) #f)))
      (λ (Σ _) (shuffle Σ))
      disp?)]))


(define-syntax take-words
  (syntax-rules ()
    [(_ M k) (take-words M k #f)]
    [(_ M k disp?)
     (run/fast
      M
      '(())
      (λ (a) #f)
      (λ (A) (>= (length A) k))
      (λ (a) #t)
      (list (λ (_ i a) (snoc i a)))
      '()
      (λ (a A) (set-cons (car a) A))
      (λ (Σ _) Σ)
      disp?)]))





