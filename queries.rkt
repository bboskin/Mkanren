#lang racket

(require "basics.rkt")

(provide  find-words accept?)




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





