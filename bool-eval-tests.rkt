#lang racket

(require "sat.rkt"
         "automata.rkt")


(define (begin? x) (memv x '(andbegin orbegin)))
(define (end? x) (memv x '(andend orend)))

(define (sexp? e)
  (match e
    [(? var?) #t]
    [`(not ,(? sexp?)) #t]
    [`(and . ,es) (andmap sexp? es)]
    [`(or . ,es) (andmap sexp? es)]
    [else #f]))

(define (list-of-sexps? e)
  (andmap sexp? e))

;; converts a word to an s-exp
;; This function, within itself, returns
;; either a single s-expression or or a list of s-expressions.
;; at top-level, for complete expressions, it returns 1 s-exp

(define (add-to-top-sexp c e)
  (if (sexp? e)
      `(,c ,e)
      (cons (add-to-top-sexp c (car e)) (cdr e))))

(define (add-to-top-list-of-sexps c e)
  (if (list-of-sexps? e) `(,c . ,e)
      (cons (add-to-top-list-of-sexps c (car e)) (cdr e))))

(define (word->s w)
  (match w
    ['() 'ε]
    [`(,(? var? v) . ,cs)
     (match (word->s cs)
       ['ε v]
       [(? sexp? s) `(,v ,s)]
       [l (add-to-top-list-of-sexps v l)])]
    [`(not . ,cs)
     (match (word->s cs)
       ['ε (error "INVALID")]
       [(? sexp? s) `(not ,s)]
       [l (add-to-top-sexp 'not l)])]
    [`(andbegin . ,cs)
     (match (word->s cs)
       ['ε (error "INVALID")]
       [(? sexp? s) `(and ,s)]
       [l (add-to-top-list-of-sexps 'and l)])]
    [`(orbegin . ,cs)
     (match (word->s cs)
       ['ε (error "INVALID")]
       [(? sexp? s) `(and ,s)]
       [l (add-to-top-list-of-sexps 'or l)])]
    [`(andend . ,cs)
     (match (word->s cs)
       ['ε '()]
       [(? sexp? s) (error "INVALID")]
       [l (add-to-top-list-of-sexps '() l)])]
    [`(orend . ,cs)
     (match (word->s cs)
       ['ε '()]
       [(? sexp? s) (error "INVALID")]
       [l (add-to-top-list-of-sexps '() l)])]))

(define ((val-of ρ) e)
  (match e
    ['ε (error 'val-of "value undefined for empty string")]
    [(? var?) (accept? ρ `(,e))]
    [`(not ,e) (not ((val-of ρ) e))]
    [`(and ,es ...)
     (andmap (λ (x) x) (map (val-of ρ) es))]
    [`(or ,es ...)
     (ormap (λ (x) x) (map (val-of ρ) es))]
    [else (error 'val-of (format "Invalid expression ~s" e))]))

(define (check-words k)
  (let ((ws (find-words Bool k)))
    (let ((M-res (map (λ (x) (accept? (Val-of p-true) x)) ws))
          (S-res (map (λ (x) ((val-of p-true) (word->s x))) ws)))
      (let loop ((M M-res)
                 (S S-res)
                 (w ws)
                 (k 0))
        (if (null? w)
            (displayln "all passed!")
            (if (car M)
                (if (car S)
                    (loop (cdr M) (cdr S) (cdr w) (add1 k))
                    (displayln
                     (list "false positive at test number" k "on" (car M) (car S) (car w))))
                (if (car S)
                    (displayln
                     (list "false negative at test number" k "on" (car M) (car S) (car w)))
                    (loop (cdr M) (cdr S) (cdr w) (add1 k)))))))))

(define (check-words-only k)
  (let ((ws (find-words-only Bool k)))
    (let ((M-res (map (λ (x) (accept? (Val-of p-true) x)) ws))
          (S-res (map (λ (x) ((val-of p-true) (word->s x))) ws)))
      (let loop ((M M-res)
                 (S S-res)
                 (w ws)
                 (k 0))
        (if (null? w)
            (displayln "all passed!")
            (if (car M)
                (if (car S)
                    (loop (cdr M) (cdr S) (cdr w) (add1 k))
                    (displayln
                     (list "false positive at test number" k "with" (car M) (car S) (car w))))
                (if (car S)
                    (displayln
                     (list "false negative at test number" k "with" (car M) (car S) (car w)))
                    (loop (cdr M) (cdr S) (cdr w) (add1 k)))))))))

(define (random-term)
  (list-ref '(p q not andbegin andend orbegin orend) (random 7)))

(define (random-word k)
  (if (zero? k) '(p)
      (match (random 4)
        [0 '(p)]
        [1 `(not ,@(random-word (sub1 k)))]
        [2 `(andbegin
             ,@(foldr append '() (build-list (sub1 k) random-word))
             andend)]
        [3 `(orbegin
             ,@(foldr append '() (build-list (sub1 k) random-word))
             orend)])))

;; regularly passing (probe-val-of 100) with (random-word 20)
(define (probe-val-of k-trials)
  (length
   (let loop ((k k-trials))
     (cond
       [(zero? k) '()]
       [else (let ((w (random-word 20)))
               (let ((M-res (accept? (Val-of p-true) w))
                     (S-res ((val-of p-true) (word->s w))))
                 (cond
                   [(and M-res S-res) (cons w (loop (sub1 k)))]
                   [(or M-res S-res)
                    (error 'sat-disagreement (format "Failed on word ~s, M said ~s S said ~s" w M-res S-res))]
                   [else (loop (sub1 k))])))]))))

;; Uncomment this, and it will run hundreds of large, random tests. will print some numbers


(begin
  #;#;#;(probe-val-of 100)
  (probe-val-of 100)
  (probe-val-of 100)
  (probe-val-of 100))

(define (run-thorough k ρ)
  (let ((M (Val-of ρ)))
    (let ((ws (find-words Bool k)))
      (andmap
       (λ (w)
         (let ((M? (accept? M w))
               (S? ((val-of ρ) (word->s w))))
         (if (or (and M? S?)
             (and (not M?) (not S?)))
             #t
             (displayln w))))
       ws))))


;; a more thorough search through all short words

(begin
  (run-thorough 4 none-true))