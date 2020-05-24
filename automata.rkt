#lang racket

(require "basics.rkt")


(provide M-Union
         M-Concatenation
         M-Intersection
         M-Difference
         M-Negation
         minimize-PDA)



(define (M-Difference M1 M2)
  (M-Intersection M1 (M-Negation M2)))

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

#|
We add powerstates to δ.

The powerstate <(S1 ...) a k?> is a state that can be transitioned
to on a with k?,
and epsilon transitions to S1 ... on all stack configurations.

Powerstates do not point to powerstates.

We can transition from a non-powerstate to a powerstate when on the agreeing
input symbols

|#




(define (add-stack-ignores mode δ k)
  (match mode
    ['right (let ((v (build-list k (λ (_) 'preserve-stack))))
              (map (λ (x) (append x v)) δ))]
    ['left (let ((v (build-list k (λ (_) 'preserve-stack))))
    (map (λ (x)
           (match x
             [`(,S1 ,c ,S2 . ,s) `(,S1 ,c ,S2 ,@v . ,s)]))
         δ))]))



(define (make-var-names A)
  (cond
    [(null? A) (λ (x) x)]
    [(symbol? (car A)) (make-var-names (cdr A))]
    [else (let ((g (gensym 'COMP))
                (res (make-var-names (cdr A))))
            (λ (x) (if (and (list? x) (set-equal?? (car A) x)) g (res x))))]))

(define (merge s1 s2)
  (match* (s1 s2)
    [((? symbol?) (? symbol?)) (if (eqv? s1 s2) s2  `(,s1 ,s2))]
    [((? list?) (? symbol?)) (set-cons s2 s1)]
    [((? symbol?) (? list?)) (set-cons s1 s2)]
    [((? list?) (? list?)) (set-union s1 s2)]))


(define (stacks-mutually-occur? ks1 ks2)
  (match* (ks1 ks2)
    [('() '()) '()]
    [(`(preserve-stack . ,ks1) `(,k2 . ,ks2))
     (cons k2 (stacks-mutually-occur? ks1 ks2))]
    [(`(,k1 . ,ks1) `(preserve-stack . ,ks2))
     (cons k1 (stacks-mutually-occur? ks1 ks2))]
    [(`((pop on ,c1 push ,vs1) . ,ks1)
      `((pop on ,c2 push ,vs2) . ,ks2))
     (if (not (equal? vs1 vs2)) #f
         (cond
           [(eqv? c1 #t) (cons `(pop on ,c2 push ,vs1) (stacks-mutually-occur? ks1 ks2))]
           [(eqv? c2 #t) (cons `(pop on ,c1 push ,vs1) (stacks-mutually-occur? ks1 ks2))]
           [(eqv? c1 c2) (cons `(pop on ,c2 push ,vs1) (stacks-mutually-occur? ks1 ks2))]
           [else #f]))]
    [(_ _) #f]))

(define ((find-rules s1 s2 S1 S2 Σ δ1 δ2) c a)
  (append (let ((s1-rel (filter (λ (x) (eqv? (car x) s1)) δ1))
                (s2-rel (filter (λ (x) (eqv? (car x) s2)) δ2)))
            (foldr
             (λ (x a)
               (match x
                 [`((,from1 ,from2)
                    ,(? (λ (x) (or (eqv? c 'ε) (memv c Σ))) c)
                    ,tos . ,stack-instrs)
                  (append
                   (map (λ (e) `(,from1 ,c ,from2 ,e . ,stack-instrs))
                        (cartesian-product
                         (filter (λ (x) (memv x S1)) tos)
                         (filter (λ (x) (memv x S2)) tos)))
                   a)]
                 [else a]))
             '()
             (foldr
              (λ (x a)
                (match x
                  [`((,from1 ,on1 ,to1 . ,stck1)
                     (,from2 ,on2 ,to2 . ,stck2))
                   (cond
                     [(and (or (eqv? on1 #t)
                               (eqv? on2 #t)
                               (eqv? on1 on2))
                           (stacks-mutually-occur? stck1 stck2))
                      =>
                      (λ (stack-instrs)
                        `(((,s1 ,s2) ,on1 ,(merge to1 to2) . ,stack-instrs)
                          . ,a))]
                     [else a])]))
              '()
              (foldr
               (cartesian-product s1-rel s2-rel)))))
          a))


(define (give-names A)
  (match A
    [(Automaton S F A δ Σ Γ)
     (let* ((get-name (make-var-names A))
            (S (get-name S))
            (F (map get-name F))
            (A (map get-name A))
            (δ (map (λ (x)
                      (match x
                        [`(,S1 ,c ,S2 . ,r)
                         `(,(get-name S1) ,c ,(get-name S2) . ,r)]))
                    δ)))
       (Automaton S F A δ Σ Γ))]))

(define (M-Intersection M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     
     (let* ((Σ (set-intersection Σ1 Σ2))
            (Γ (append Γ1 Γ2))
            (S (list S1 S2))
            (A-max (cartesian-product A1 A2))
            
            (δ (foldr (find-rules
                       S1 S2 Σ
                       (add-stack-ignores 'right δ1 (length Γ2))
                       (add-stack-ignores 'left δ2 (length Γ1)))
                      '()
                      A-max))
            (A (to-set (cons S (append (map car δ) (map caddr δ)))))
            (F (set-intersection A (cartesian-product F1 F2))))
       ;; making single-symbol names for compound states, and updating S, F, A, and δ
       (minimize-PDA (give-names (Automaton S F A δ Σ Γ)))
       )]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; two-phase PDA minimization
;; first states are minimized (and transitions as permitted)
;; and then stack symbols are consolidated (and transitions as permitted)

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

