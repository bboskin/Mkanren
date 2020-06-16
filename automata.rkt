#lang racket

(require "basics.rkt")


(provide Automaton
         
         M-Union
         M-Intersection
         M-Negation
         M-Difference
         M-Concatenation
         
         minimize-PDA)

;; M-Union : Automaton x Automaton -> Automaton
(define (M-Union M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((S0 (gensym 'Start))
           (S2 (symbol-append S2 'b))
           (F2 (rename-xs A2 (λ (x) (symbol-append x 'b)) F2))
           (A2 (rename-xs A2 (λ (x) (symbol-append x 'b)) A2))
           (δ2 (rename-xs A2 (λ (x) (symbol-append x 'b)) δ2))
           (k-stacks (max (length Γ1) (length Γ2))))
       (let* ((k-needed-1 (- k-stacks (length Γ1)))
              (k-needed-2 (- k-stacks (length Γ2)))
              (Γ1 (append Γ1 (build-list k-needed-1 (λ (_) '()))))
              (Γ2 (append Γ2 (build-list k-needed-2 (λ (_) '())))))
         (Automaton
          S0
          (append F1 F2)
          (cons S0 (append A1 A2))
          `(,((add-stack-ignore 'left k-stacks)`(,S0 ε ,S1))
            ,((add-stack-ignore 'left k-stacks)`(,S0 ε ,S2))
            . ,(append
                (add-stack-ignores 'right δ1 k-needed-1)
                (add-stack-ignores 'right δ2 k-needed-2)))
        (set-union Σ1 Σ2)
        (map set-union Γ1 Γ2))))]))

;; M-Intersection : Automaton x Automaton -> Automaton
;; helpers defined at the end of the file
(define (M-Intersection M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let* ((Σ (set-intersection Σ1 Σ2))
            (Γ (append Γ1 Γ2))
            (S (list S1 S2))
            (δ (append
                (add-stack-ignores 'right δ1 (length Γ2))
                (add-stack-ignores 'left δ2 (length Γ1))))
            (δ (project-to-compound-states S A1 A2 δ Σ))
            (A (append (map car δ) (map caddr δ)))
            (F (filter (λ (x) (and (memv (car x) F1) (memv (cadr x) F2))) A)))
       (minimize-PDA (give-names (Automaton S F A δ Σ Γ))))]))

;; untested
;; M-Negation : Automaton -> Automaton
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
              '() A))
            (δ (append trash-rules δ)))
       (Automaton S F A δ Σ Γ))]))

;;;;;;;;;;;;;;;;;;;;;;;;
;; M-Difference (relies on interesection and Negation)

;; untested
(define (M-Difference M1 M2)
  (M-Intersection M1 (M-Negation M2)))

;; untested
;; M-Concatenation : Automaton x Automaton -> Automaton
(define (M-Concatenation M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((S2 (symbol-append S2 'b))
           (F2 (rename-xs A2 (λ (x) (symbol-append x 'b)) F2))
           (A2 (rename-xs A2 (λ (x) (symbol-append x 'b)) A2))
           (δ2 (rename-xs A2 (λ (x) (symbol-append x 'b)) δ2))
           (k-stacks (max (length Γ1) (length Γ2))))
       (let* ((k-needed-1 (- k-stacks (length Γ1)))
              (k-needed-2 (- k-stacks (length Γ2)))
              (Γ1 (append Γ1 (build-list k-needed-1 (λ (_) '()))))
              (Γ2 (append (build-list k-needed-2 (λ (_) '())) Γ2)))
         (Automaton
          S1
          F2
          (append A1 A2)
          `(,@(add-stack-ignores
               'right (map (λ (f) `(,f ε ,S2)) F1) k-stacks)
            . ,(append
                (add-stack-ignores 'right δ1 k-needed-1)
                (add-stack-ignores 'left δ2 k-needed-2)))
        (set-union Σ1 Σ2)
        (map set-union Γ1 Γ2))))]))

;; minimize-PDA : Automaton -> Automaton
(define (minimize-PDA M)
  (shrink-stack (shrink-states M)))

;;;;;;;;;;;;;;;;;;;
;; helpers for intersection

(define (k-preserves k) (build-list k (λ (_) 'preserve-stack)))
(define (add-k-preserves-on-right δ k)
  (map
   (λ (x)
     (match x
       [`(,S1 ,a ,S2 . ,rules)
        `(,S1 ,a ,S2 ,@rules . ,(k-preserves k))]))
   δ))
(define (add-k-preserves-on-left δ k)
  (map
   (λ (x)
     (match x
       [`(,S1 ,a ,S2 . ,rules)
        `(,S1 ,a ,S2 ,@(k-preserves k) . ,rules)]))
   δ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers for two(soon to be three)-phase PDA minimization
;; first states are minimized (and transitions as permitted)
;; and then stack symbols are consolidated (and transitions as permitted)
;; and then more states/transitions are reduced
;; by certain easy patterns (S1 -s-> S2 -ε-> S3 ==> S1 -s-> S3) TODO

#|
Types/constructs used for minimization,
in additions to those described in basics.rkt

Group -- `(,Symbol . ,(List Symbol)) the first symbol is the
'representive' of the states in the cdr

|#

;;;;;;;;;;;;
;; functions that could used in several phases

;; rep : Symbol x (List Group) -> (List Symbol)
(define (rep S groups)
  (let ((gs (filter (λ (x) (member S x)) groups)))
    (match (length gs)
      [0 S]
      [1 (caar gs)]
      [n+2 (error "automata state ~s has more than one representative: ~s" S (map car gs))])))

;; rep-in : (List Group) -> Symbol -> (List Symbol)
;; convenient for higher-order fns, used in stack minimization
(define ((rep-in groups) S)
  (rep S groups))

;; update-states : (List Group) -> Transition -> (List Transition)
(define ((update-states gs) r) (map (rep-in gs) r))

;; update-inst : (List Group) -> Stack-Instruction -> Stack-instruction
(define ((update-inst groups) r)
  (match r
    ['preserve-stack
     'preserve-stack]
    [`(pop on #t push ,vs)
     `(pop on #t push ,(map (rep-in groups) vs))]
    [`(pop on ,b push ,vs)
     `(pop on ,(rep b groups) push ,(map (rep-in groups) vs))]))

;; update-stack : (List Group) -> Transition -> Transition
(define ((update-stack gs) r)
  (match r
    [`(,S1 ,s ,S2 . ,rules)
     `(,S1 ,s ,S2 . ,(map (update-inst gs) rules))]))



;;;;;;;;;;;;;;;;
;; phase 1

;; stack-agrees : Symbol x Stack-Instruction -> Boolean
(define (stack-agrees? γ r)
  (match r
    ['preserve-stack #t]
    [`(pop on #t push ,vs) #t]
    [`(,pop on ,g push ,vs) (eqv? γ g)]))

;; lookup-group : Symbol x (List Group) x Nat -> Nat
(define (lookup-group s gs k)
  (cond
    [(null? gs) (error 'lookup-group "State not in a group")]
    [(memv s (car gs)) k]
    [else (lookup-group s (cdr gs) (add1 k))]))

;; circ-group-helper : Symbol x Symbol x (List Group) -> Symbol -> (List Nat)
(define ((circ-group-helper s γs gs) x)
  (match x
    [`(,a ,S2)
     (if (eqv? a s) `(,(lookup-group S2 gs 0)) '())]
    [`(ε ,S2 . ,rs)
     (if (andmap stack-agrees? γs rs)
         `(,(lookup-group S2 gs 0))
         '())]
    [`(,a ,S2 . ,rs)
     (if (and (eqv? a s) (andmap stack-agrees? γs rs))
         `(,(lookup-group S2 gs 0))
         '())]))


;; circ-group : Symbol x Symbol x Transition-Function x (List Group)
;;   -> Symbol -> (cons Symbol (List Nat)
(define ((circ-group s γs δ gs) S)
  (cons S
        (foldr
         (λ (x a)
           (set-union ((circ-group-helper s γs gs) (cdr x)) a))
           '()
           (filter (λ (x) (eqv? (car x) S)) δ))))

;; circ-help : (List Symbol) x (List (List Symbol)) -> (List (List Symbol))
(define (circ-help ls a)
  (append-map  (λ (i) (map (λ (x) (cons i x)) a)) ls))


;; make-circumstances : (List Letter) x (List (List Symbol)) ->
(define (make-circumstances Σ Γ)
  (let ((Γ (if (null? Γ) '() (map (λ (x) (cons #f x)) Γ))))
    (let ((ans (map reverse
                    (foldl
                     circ-help
                     (map list Σ)
                     (reverse Γ)))))
      ans)))

;; update-group : Group x (List Group) -> (List Group)
(define (update-group g dests)
  (foldr
   (λ (e1 ans)
     (let loop ((ls ans))
       (match ls
         ['() `((,e1))]
         [`((,s1 . ,ss) . ,ans)
          (if (set-equal?? (cdr (assv e1 dests)) (cdr (assv s1 dests)))
              `((,e1 ,s1 . ,ss) . ,ans)
              `((,s1 . ,ss) . ,(loop ans)))])))
   '()
   g))

;; apply-circumstance :
;;  Transition-Function -> `(,Symbol ,(Maybe Symbol) x (List Group) -> (List Group)

(define ((apply-circumstance δ) P groups)
  (let* ((F (circ-group (car P) (cdr P) δ groups)))
    (append-map (λ (g) (update-group g (map F g))) groups)))

;; state-groups :
;;  Transition-Function x (List Symbol) x (List Symbol) x (List Letter) x (List (List Symbol))
;;  -> (List Group)
(define (state-groups δ A F Σ Γ)
  (foldl
   (apply-circumstance δ)
   `(,F ,(set-difference A F))
   (make-circumstances Σ Γ)))

;; shrink-states : Automaton -> Automaton
(define (shrink-states M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let* ((groups (remove '() (state-groups δ A F Σ Γ)))
            (A (map car groups))
            (S (rep S groups))
            (F (set-intersection A F))
            (δ (map (update-states groups) δ)))
       (Automaton S (set-intersection A F) A δ Σ Γ))]))

;; add-to-group : Symbol x Transition-Function x (List Group) -> (List Group)
(define (add-to-group s δ groups)
  (match groups
    ['() `((,s ,δ (,s)))]
    [`((,rep ,δg ,g) . ,groups)
     (if (set-equal?? δg (replace* s rep δ))
         `((,rep ,δg (cons s g)) . ,groups)
         `((,rep ,δg ,g) . ,(add-to-group s δ groups)))]))

;; stack-groups : Automaton -> (List Group)
(define (stack-groups M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (map (λ (Γ)
            (let ((assoclist (map (λ (x) (cons x (filter (λ (r) (member* x r)) δ))) Γ)))
              (foldl
               (λ (s a)
                 (add-to-group s (cdr (assv s assoclist)) a))
               '()
               Γ)))
          Γ)]))

;; stackless : Transition-Function x Stack -> Transition-Function
(define (stackless δ Γ)
  (filter (λ (T) (andmap (λ (x) (not (member* x T))) Γ)) δ))

;; shrink-stack : Automaton -> Automaton
(define (shrink-stack M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let* ((gss (stack-groups M))
            (v (map (λ (x) (map (update-stack x) δ)) gss))
            (δ (foldr append (stackless δ (foldr append '() Γ)) v))
            (Γ (map (λ (gs) (map car gs)) gss)))
       (Automaton S F A δ Σ Γ))]))

;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers for Set-Intersection


(define ((add-stack-ignore mode k) t)
  (match mode
    ['right (let ((v (build-list k (λ (_) 'preserve-stack))))
              (append t v))]
    ['left (let ((v (build-list k (λ (_) 'preserve-stack))))
             (match t
               [`(,S1 ,c ,S2 . ,s)
                `(,S1 ,c ,S2 ,@v . ,s)]))]))

(define (add-stack-ignores mode δ k)
  (map (add-stack-ignore mode k) δ)
  #;
  (match mode
    ['right (let ((v (build-list k (λ (_) 'preserve-stack))))
              (map (λ (x) (append x v)) δ))]
    ['left (let ((v (build-list k (λ (_) 'preserve-stack))))
             (map (λ (x)
                    (match x
                      [`(,S1 ,c ,S2 . ,s)
                       `(,S1 ,c ,S2 ,@v . ,s)]))
                  δ))]))

;; renaming an automaton with compound (list) state names
;; to symbol state names

;; make-var-names : (List (List Symbol)) -> (List Symbol) -> Symbol
(define (make-var-names A)
  (cond
    [(null? A) (λ (x) x)]
    [(symbol? (car A)) (make-var-names (cdr A))]
    [else (let ((g (gensym 'COMP))
                (res (make-var-names (cdr A))))
            (λ (x) (if (and (list? x) (set-equal?? (car A) x)) g (res x))))]))

;; give-names : Comoound-Automaton -> Automaton
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


;; given all of the transitions reaching  out of the compound state S,
;; consolidate transitions based on the letter/stack condition,
;; and have them point from the compound state



(define (merge-stack-rules ra rb)
  (map
   (λ (r1 r2)
     (match* (r1 r2)
       [('preserve-stack r) r]
       [(r 'preserve-stack) r]
       [(_ _) (error "Stacks not completely Independent")]))
   ra rb))

(define ((merge-transition t1) t2)
  (match* (t1 t2)
    [(`(,S1a ,aa ,S2a . ,ra)
      `(,S1b ,_ ,S2b . ,rb))
     `((,S1a ,S1b) ,aa (,S2a ,S2b) . ,(merge-stack-rules ra rb))]))


(define (find-partner-transitions t1 t2)
  (match t1
    ['() '()]
    [`((,S1 ,a ,S2 . ,rs) . ,d)
     (let ((yes (filter (λ (x) (eqv? (cadr x) a)) t2)))
       (append
        (map (merge-transition (car t1)) yes)
        (find-partner-transitions d t2)))]))

(define ((add-state p S) t)
  (match t
    [`(,S1 ,a ,S2 . ,rs)
     (match p
       [1 `((,S ,S1) ,a (,S ,S2) . ,rs)]
       [2 `((,S1 ,S) ,a (,S2 ,S) . ,rs)])]))

;; group-transitions : Transition-Function x Transition-Function ->
;; Compound-Transition-Function
(define (group-transitions S1 S2 Σ ts1 ts2)
  (let ((ε-1 (filter (λ (x) (eqv? (cadr x) 'ε)) ts1))
        (ε-2 (filter (λ (x) (eqv? (cadr x) 'ε)) ts2))
        (a-1 (filter (λ (x) (and (not (eqv? (cadr x) 'ε))
                                 (memv (cadr x) Σ)))
                     ts1))
        (a-2 (filter (λ (x) (and (not (eqv? (cadr x) 'ε))
                                 (memv (cadr x) Σ)))
                     ts2)))
    (let ((ε-transitions
           (append
            (map (add-state 2 S2) ε-1)
            (map (add-state 1 S1) ε-2)))
          (a-transitions
           (find-partner-transitions a-1 a-2)))
      (append ε-transitions a-transitions))))

;; given a start state, all the states, and a transition function,
;; return an equivalent transition function that operates on compound states

;; project-to-compound-states : (List Symbol) x (List Symbol) x Transition-Function
;; -> Compound-Transition-Function
(define (project-to-compound-states Start A1 A2 δ Σ)
  (let ((transition-groups1
         (map (λ (x) (cons x (filter (λ (y) (eqv? (car y) x)) δ))) A1))
        (transition-groups2
         (map (λ (x) (cons x (filter (λ (y) (eqv? (car y) x)) δ))) A2)))
    (let loop ((Q `(,Start))
               (V '())
               (δ '()))
      (match Q
        ['() δ]
        [`(,(? (member-of V)) . ,Q) (loop Q V δ)]
        [`((,S1 ,S2) . ,Q)
         (let ((ts1 (assv S1 transition-groups1))
               (ts2 (assv S2 transition-groups2)))
                (let ((ts (group-transitions S1 S2 Σ
                                             (if ts1 (cdr ts1) '())
                                             (if ts2 (cdr ts2) '()))))
                  (let ((δ (append ts δ))
                        (V (cons `(,S1 ,S2) V))
                        (Q (append Q (map caddr ts))))
                    (loop Q V δ))))]))))

(define Start '(S145408 Start146913))
(define A1 '(S145408 S145404 F145405 S145406 F145407))
(define A2 '(S145451 S145451F S145449b S145449Fb S145426b S145426Fb))
(define δ '((S145408 ε S145404 preserve-stack)
     (S145408 ε S145406 preserve-stack)
     (S145404 a F145405 preserve-stack)
     (S145406 b F145407 preserve-stack)
     (Start146913 ε S145451 preserve-stack)
     (Start146913 ε S145449b preserve-stack)
     (S145451 b S145451F preserve-stack)
     (S145451 a S145451F preserve-stack)
     (S145426b a S145426Fb preserve-stack)
     (S145449b ε S145426b (pop on #t push (γ145568)))
     (S145426Fb ε S145449b (pop on γ145568 push (γ145568)))
     (S145449Fb ε S145449Fb (pop on γ145568 push ()))
     (S145449b a S145449Fb preserve-stack)))
(define Σ '(a b))
