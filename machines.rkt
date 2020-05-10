#lang racket

(require "basics.rkt")

(provide M-Union
         M-Concatenation
         M-Intersection
         M-Difference
         M-Negation
         minimize-PDA)




(define (M-Union M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((S0 (gensym 'Start))
           (F2 (rename-xs A2 (λ (x) (symbol-append x 'b)) F2))
           (A2 (rename-xs A2 (λ (x) (symbol-append x 'b)) A2))
           (δ2 (rename-xs A2 (λ (x) (symbol-append x 'b)) δ2)))
       (Automaton
        S0
        (append F1 F2)
        (append A1 A2)
        `((,S0 ε ,S1 preserve-stack)
          (,S0 ε ,S2 preserve-stack)
          . ,(append δ1 δ2))
        (set-union Σ1 Σ2)
        (map set-union Γ1 Γ2)))]))

(define (M-Concatenation M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((F2 (rename-xs A2 (λ (x) (symbol-append x 'b)) F2))
           (A2 (rename-xs A2 (λ (x) (symbol-append x 'b)) A2))
           (δ2 (rename-xs A2 (λ (x) (symbol-append x 'b)) δ2)))
       (Automaton
        S1
        F2
        (append A1 A2)
        `(,@(map (λ (f) `(,f ε ,S2 (pop on #f push (#f)))) F1)
          . ,(append δ1 δ2))
        (set-union Σ1 Σ2)
        (map set-union Γ1 Γ2)))]))

(define (M-Negation M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let* ((trash (gensym 'Trash))
            (A (cons trash A))
            (F (set-difference A F))
            (trash-rules
             (foldr
              (λ (x a)
                `(,@(map (λ (γ) `(,x ε ,trash (pop on ,γ push ()))) Γ) ,@a))
              '()  A))
            (δ (append trash-rules δ)))
       (Automaton S F A δ Σ Γ))]))

(define (M-Intersection M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     'TODO]))

(define (M-Difference M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     'TODO]))

(define (make-circumstances Σ Γ)
  (foldr (λ (γ a) (append (cartesian-product Σ γ) a)) '() Γ))



(define (lookup-group s gs k)
  (cond
    [(null? gs) (error 'lookup-group "State not in a group")]
    [(memv s (car gs)) k]
    [else (lookup-group s (cdr gs) (add1 k))]))

(define ((find-dest s γ δ gs) S)
  (cons S
        (foldr
         (λ (x a)
           (if (eqv? (car x) S)
               (set-union
                a
                (match (cdr x)
                  [`(ε ,S2 preserve-stack)
                   `(,(lookup-group S2 gs 0))]
                  [`(ε ,S2 (pop on #t push ,vs))
                   `(,(lookup-group S2 gs 0))]
                  [`(ε ,S2 (pop on ,g push ,vs))
                   (if (eqv? g γ)
                       `(,(lookup-group S2 gs 0))
                       '())]
                  [`(,a ,S2 preserve-stack) (if (eqv? a s) `(,S2) '())]
                  [`(,a ,S2 (pop on #t push ,vs))
                   (if (eqv? a s) `(,(lookup-group S2 gs 0)) '())]
                  [`(,a ,S2 (pop on ,g push ,vs))
                   (if (and (eqv? a s) (eqv? g γ)) `(,(lookup-group S2 gs 0)) '())]))
               a))
           '()
           δ)))


(define (update-group g dests)
  (match g
    ['() '()]
    [`(,e1 . ,es)
     (let ((ans (update-group es dests)))
       (let loop ((ls ans))
         (match ls
           ['() `((,e1))]
           [`((,s1 . ,ss) . ,ans)
            (if (set-equal?? (cdr (assv e1 dests)) (cdr (assv s1 dests)))
                `((,e1 ,s1 . ,ss) . ,ans)
                `((,s1 . ,ss) . ,(loop ans)))])))]))

(define (update-by-dest init-groups s γ δ)
  (let ((F (find-dest s γ δ init-groups)))
    (let loop ((groups init-groups))
      (match groups
        ['() '()]
        [`(,g1 . ,g)
         (append (update-group g1 (map F g1)) (loop g))]))))



(define (get-state-groups M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let ((groups `(,F ,(set-difference A F)))
           (init-C (make-circumstances Σ Γ)))
       (let loop ((groups groups)
                  (C init-C))
         (match C
           ['() groups]
           [`((,s1 ,γ1) . ,C)
            (let ((groups (update-by-dest groups s1 γ1 δ)))
              (loop groups C))])))]))

(define (minimize-PDA M)
  (let ((groups (get-state-groups M)))
    (let ((A (map car groups)))
      (match M
        [(Automaton S F A-old δ Σ Γ)
         (let ((F (set-intersection A F))
               (δ (filter (λ (x) (and (memv (car x) A)
                                      (memv (caddr x) A)))
                          δ)))
           (Automaton S (set-intersection A F) A δ Σ Γ))]))))



#|

(minimize-PDA (Automaton
 'S2504
 '(S2504F)
 '(S2504 S2504F S25042505 S25042505F S SF)
 '((S a SF preserve-stack)
   (S ε S25042505 (pop on #t push (γ2625)))
   (S25042505F ε S (pop on γ2625 push (γ2625)))
   (SF ε SF (pop on γ2625 push ()))
   (S25042505 a S25042505F preserve-stack)
   (S2504 a S2504F preserve-stack)
   (S2504 ε S25042505 (pop on #t push (γ2624)))
   (S25042505F ε S (pop on γ2624 push (γ2624)))
   (SF ε S2504F (pop on γ2624 push ()))
   (S2504 ε S2504F preserve-stack))
 '(a)
 '((γ2625 γ2624))))
((S2504F))
(S2504F)
|#
