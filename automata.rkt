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


;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions for Intersection
;; (which for now assumes separate namespaces for the two input machines


(define (state-cart-prod A1 A2)
  (foldr (λ (a v) (append (map (λ (x) `(,a ,x)) A2)  v))
         '()
         A1)
  (match A1
    ['() (map list A2)]
    [`(,a . ,d)
     (map
      (λ (x)
        `(,(symbol-append a (car x)) ,a . ,(cdr x)))
      (state-cart-prod d A2))]))

(define (M-Intersection M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let* ((Σ (set-union Σ1 Σ2))
            (A-max (append (map (λ (x) (cons (gensym) x)) (cartesian-product A1 A2)) A1 A2))
            (S (foldr (λ (x a) (if a a (if (equal? (list S1 S2) (cdr x)) (car x) #f))) #f A-max))
            (F (filter (λ (x) (and (memv (car x) F1) (memv (cadr x) F2))) A-max))) 
       (let loop ((Γ (map (λ (_) '()) ))
                  (δ-used '())
                  (δ-available (set-union δ1 δ2))
                  (A '())
                  (Q `(,S))
                  (V '()))
         (match Q
             ['() (Automaton S F A δ-used Σ Γ)]
             [`(,(? (member-of V)) . ,Q) (loop Γ δ-used δ-available A Q V)]
             [`((,s ,ks) . ,rest)
              (let ((V `((,s ,ks) . ,V))
                    (A (if (and (member s F s) (all-empty? ks) (include? a)) (f a A) A))
                    (T (update-T
                        rest
                        (א Σ a)
                        (apply-transitions U δ s ks a)
                        (update-epsilons s δ ks a))))
                (loop T V A))])))]))




(define (M-Difference M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     'TODO]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; two-phase PDA minimization

(define (rep S groups)
  (caar (filter (λ (x) (member S x)) groups)))


(define (make-circumstances Σ Γ)
  (foldr
   (λ (γ a) (append (cartesian-product Σ γ) a))
   '()
   (if (null? Γ)
       '((#f))
       (map (λ (x) (cons #f x)) Γ))))

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
                (match (cdr x)
                  [`(,a ,S2)
                   (if (eqv? a s) `(,(lookup-group S2 gs 0)) '())]
                  [`(ε ,S2 preserve-stack)
                   `(,(lookup-group S2 gs 0))]
                  [`(ε ,S2 (pop on #t push ,vs))
                   `(,(lookup-group S2 gs 0))]
                  [`(ε ,S2 (pop on ,g push ,vs))
                   (if (eqv? g γ)
                       `(,(lookup-group S2 gs 0))
                       '())]
                  [`(,a ,S2 preserve-stack)
                   (if (eqv? a s) `(,(lookup-group S2 gs 0)) '())]
                  [`(,a ,S2 (pop on #t push ,vs))
                   (if (eqv? a s) `(,(lookup-group S2 gs 0)) '())]
                  [`(,a ,S2 (pop on ,g push ,vs))
                   (if (and (eqv? a s) (eqv? g γ))
                       `(,(lookup-group S2 gs 0))
                       '())])
                a)
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
    (foldr (λ (g1 a)
             (append (update-group g1 (map F g1)) a))
           '()
           init-groups)))



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
            (loop (update-by-dest groups s1 γ1 δ) C)])))]))


(define (update-δ groups δ)
  (foldr
   (λ (x a)
     (match x
       [`(,s1 ε ,s2 preserve-stack)
        (let ((s1 (rep s1 groups)) (s2 (rep s2 groups)))
          (if (eqv? s1 s2) a
              (set-cons `(,s1 ε ,s2 preserve-stack) a)))]
       [`(,s1 ,s ,s2 . ,r)
        (set-cons `(,(rep s1 groups) ,s ,(rep s2 groups) . ,r) a)]))
   '()
   δ))

(define (add-to-group s L groups)
  (match groups
    ['() `((,s ,L (,s)))]
    [`((,rep ,L-g ,g) . ,groups)
     (if (set-equal?? L-g (replace* s rep L))
         `((,rep ,L-g (cons s g)) . ,groups)
         `((,rep ,L-g ,g) . ,(add-to-group s L groups)))]))

(define (get-stack-groups M)
  (match M
    [(Automaton S F A δ Σ '()) #f]
    [(Automaton S F A δ Σ `(,Γ))
     (let ((asoclist (map (λ (x) (cons x (filter (λ (r) (member* x r)) δ))) Γ)))
       (let loop ((symbols Γ)
                  (groups '()))
         (match symbols
           ['() groups]
           [`(,s1 . ,symbols)
            (let ((L (cdr (assv s1 asoclist))))
              (loop symbols
                    (add-to-group s1 L groups)))])))]
    [else (error "not handling multiple stacks yet")]))

(define ((stack-rep groups) S)
  (caar (filter (λ (x) (member S (caddr x))) groups)))

(define (update-stack groups δ)
  (if (false? groups)
      (values #f δ)
      (values (map car groups)
          (foldr
           (λ (r a)
             (match r
               [`(,S1 ,s ,S2) (cons r a)]
               [`(,S1 ,s ,S2 preserve-stack) (cons r a)]
               [`(,S1 ,s ,S2 (pop on #t push ,vs))
                (set-cons
                 `(,S1 ,s ,S2 (pop on #t push ,(map (stack-rep groups) vs)))
                 a)]
               [`(,S1 ,s ,S2 (pop on ,b push ,vs))
                (set-cons
                 `(,S1 ,s ,S2 (pop on ,((stack-rep groups) b) push ,(map (stack-rep groups) vs)))
                 a)]))
           '()
           δ))))

(define (minimize-states M)
  (match M
    [(Automaton S F _ δ Σ Γ)
     (let* ((groups (get-state-groups M))
            (A (map car groups))
            (F (set-intersection A F))
            (δ (update-δ groups δ)))
       (Automaton S (set-intersection A F) A δ Σ Γ))]))

(define (minimize-stack M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let-values (((Γ δ) (update-stack (get-stack-groups M) δ)))
       (Automaton S F A δ Σ (if Γ `(,Γ) '())))]))

(define (minimize-PDA M)
  (minimize-stack (minimize-states M)))

