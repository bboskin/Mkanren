#lang racket

(require "basics.rkt"
         "automata.rkt")
(provide RE->DFA CNF->PDA CFG->PDA)

;;;;;;;;;;;;;;;;;;;;;;;;
;; Automated generation of abstract machines from grammars


;; making NFAs from REs
(define (RE->DFA e)
 (match e
    [(? symbol? x)
     (let ((S (gensym 'S))
           (F (gensym 'F)))
       (Automaton S `(,F) `(,S ,F) `((,S ,x ,F)) `(,x) '()))]
    [`(,e1 • ,e2)
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 _) (Automaton S2 F2 A2 δ2 Σ2 _))
        (Automaton
         S1 F2 (set-union A1 A2)
         (set-union (map (λ (F) `(,F ε ,S2)) F1) (set-union δ1 δ2))
         (set-union Σ1 Σ2)
         '())])]
    [`(,e1 U ,e2)
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
         (Automaton S2 F2 A2 δ2 Σ2 Γ2))
        (let ((new-S (gensym 'S)))
          (Automaton
           new-S (set-union F1 F2) (cons new-S (set-union A1 A2))
           (append `((,new-S ε ,S1) (,new-S ε ,S2)) (set-union δ1 δ2))
           (set-union Σ1 Σ2)
           '()))])]
    [`(,e1 +)
     (match (RE->DFA e1)
       [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
        (Automaton
         S1 F1 A1
         (append (map (λ (x) `(,x ε ,S1)) F1) δ1)
         Σ1
         '())])]
    [`(,e1 *)
     (match (RE->DFA e1)
       [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
        (Automaton
           S1 (cons S1 F1) A1
           (append (map (λ (x) `(,x ε ,S1)) F1) δ1)
           Σ1
           '())])]
    [else (error "Not a valid RE!!")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; generating PDAs from CNFs

;; environment  : (List Symbol) -> Environment
(define (env A)
  (let ((F (λ (x) (string->symbol (string-append (symbol->string x) "F")))))
    (map (λ (x) `(,x ,(F x))) A)))

;; final-State :
(define (final-state S ρ)

  (symbol-append S 'F)
  #;(let ((pr? (assv S ρ)))
    (if pr? (cadr pr?) (error (format "No values for ~s" S)))))

;; add : Symbol x Environment x Destination x Automaton -> Automaton
(define (add S ρ r M)
  (match M
    [(Automaton S0 F A δ Σ Γ)
     (let  ((Sf (final-state S ρ)))
       (match r
         ['ε (Automaton S0 F A (set-cons `(,S ε ,Sf preserve-stack) δ) Σ Γ)]
         [`',a
          (let* ((δ (set-cons `(,S ,a ,Sf preserve-stack) δ))
                 (Σ (set-cons a Σ)))
            (Automaton S0 F A δ Σ Γ))]
         [`(,(? symbol? P) ,(? symbol? Q))
          (let ((Fp (final-state P ρ))
                (Fq (final-state Q ρ))
                (γ (gensym 'γ)))
            (let ((S->P `(,S ε ,P (pop on #t push (,γ))))
                  (P->Q `(,Fp ε ,Q (pop on ,γ push (,γ))))
                  (Q->F `(,Fq ε ,Sf (pop on ,γ push ()))))
              (let ((δ (set-union `(,S->P ,P->Q ,Q->F) δ))
                    (Γ `((,γ . ,(car Γ)))))
                (Automaton S0 F A δ Σ Γ))))]
         [else (error "unknown rule format")]))]))

(define (init-M ρ)
  (let* ((S0 (caar ρ))
         (F `(,(final-state S0 ρ)))
         (A (foldr append '() ρ)))
    (Automaton S0 F A '() '() '(()))))

(define (CNF->PDA G)
  (let ((ρ (env (map car G))))
    (let go ((M (init-M ρ))
             (G G))
      (match G
        ['() M]
        [`((,S ->) . ,G) (go M G)]
        [`((,S -> ,e ,es ...) . ,G)
         (go (add S ρ e M)
             `((,S -> . ,es) . ,G))]))))


;; Production-Rule' : a Production-Rule where symbols may already have
;; an associated automaton in the global dictionary.


;; inserts M1 as a subautomaton within M1.
;; assumes that M1 has already been given transitions to point
;; to the start/final states of M2
(define (zip-Ms M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((k1 (length Γ1))
           (k2 (length Γ2)))
       (let ((δ1 (add-stack-ignores 'right δ1 (max k2 k1) #;(max 0 (- k2 k1))))
             (δ2 (add-stack-ignores 'right δ2 (max k2 k1) #;(max 0 (- k1 k2)))))
         (let ((Γ1 (append Γ1 (build-list (max 0 (- k2 k1)) (λ (_) '()))))
               (Γ2 (append Γ2 (build-list (max 0 (- k1 k2)) (λ (_) '())))))
           (Automaton S1 F1
                      (set-union A1 A2)
                      (set-union δ1 δ2)
                      (set-union Σ1 Σ2)
                      (map append Γ1 Γ2)))))]))

(define (zip-with-predefined M S1 ρ)
  (let* ((γ (gensym 'γ))
         (M0 (cdr M))
         (S S1)
         (F (final-state S1 ρ)))
    (match M0
      [(Automaton Sm `(,Fm) Am δm Σm Γm)
       (zip-Ms
        (Automaton S `(,F) (list S F)
                   `((,S ε ,Sm (pop on #t push (,γ)))
                     (,Fm ε ,F (pop on ,γ push ()))) '() `((,γ)))
        M0)])))


(define ((k-bs S) i)
  (cond
    [(zero? i) S]
    [else (symbol-append ((k-bs S) (sub1 i)) 'F)]))


(define (concatify x y old-γ new-γ)
  (match* (x y)
    [((Automaton Sx Fx Ax δx Σx Γx)
      (Automaton Sy Fy Ay δy Σy Γy))
     (let ((δ (add-stack-ignores
                'right
                `(,@(map (λ (x) `(,x ε ,Sy (pop on ,old-γ push (,new-γ)))) Fx) . ,δx)
                (max (length Γx) (length Γy)))))
       (let ((Γx (append Γx (build-list (max 0 (- (length Γy) (length Γx))) (λ (_) '()))))
             (Γy (append Γy (build-list (max 0 (- (length Γx) (length Γy))) (λ (_) '())))))
         (Automaton Sx Fy Ax δ Σx (map set-union Γx Γy))))]))


(define (do-concat D? ρ es S1)
  (let loop ((es es)
             (S S1)
             (F0 (symbol-append S1 'i))
             (old-γ #t)
             (new-γ (gensym 'γ)))
  (match es
    ['() (Automaton S `(,S ,F0) `(,S ,F0) `((,S ε ,F0 (pop on ,old-γ push ()))) '() `((,old-γ ,new-γ)))]
    [`(,e . ,es)
     (let ((M1 ((1pRule->M S F0 D? ρ) `(,S -> ,e)))
           (M2 (loop es F0 (symbol-append F0 'i) new-γ (gensym 'γ))))
       (zip-Ms (concatify M1 M2 old-γ new-γ) M2))])))



;; 1pRule->M :
;; [Maybe Dictionary] x Environment -> Production-Rule' x Automaton
;;   -> Automaton

(define ((1pRule->M S1 F D? ρ) t)
  (match t
    [`(,_ -> ε) (Automaton S1 (list F) (list S1 F) `((,S1 ε ,F)) '() '())]
    [`(,_ -> ',(? symbol? a)) (Automaton S1 (list F) (list S1 F) `((,S1 ,a ,F)) `(,a) '())]
    [`(,_ -> ,(? symbol? P))
     (cond
       [(and D? (assv P D?)) => (λ (M) (zip-with-predefined M S1 ρ))]
       [else (let* ((γ (gensym 'γ))
                    (Pf (final-state P ρ))
                    (M (Automaton S1 (list F) (list S1 F)
                                  `((,S1 ε ,P (pop on #t push (,γ)))
                                    (,Pf ε ,F (pop on ,γ push ())))
                                  '()
                                  `((,γ)))))
             M)])]
    [`(,_ -> ,es)
     (match (do-concat D? ρ es S1)
       [(Automaton S F1 A δ Σ Γ)
        (Automaton S `(,F) A
                   (add-stack-ignores
                    'right
                    `(,@(map (λ (f)  `(,f ε ,F . ,(build-list (length Γ) (λ (i) 'preserve-stack)))) F1)
                      ,@δ)
                    (length Γ))
                   Σ Γ)])]))

;; complete-stack : Automaton -> Automaton
(define (complete-stack M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let ((k (length Γ)))
       (Automaton S F A (add-stack-ignores 'right δ k) Σ Γ))]))

;; pRule->M :
;; [Maybe Dictionary] x Environment -> Production-Rule' x Automaton
;;   -> Automaton
(define ((pRule->M D? ρ) t)
  (match t
    [`(,S1 -> ,es ...)
     (let ((Rs (remove `(,S1 -> ,S1) (map (λ (x) `(,S1 -> ,x)) es))))
       (let ((Ms (map (1pRule->M S1 (final-state S1 ρ) D? ρ) Rs)))
         (if (null? Ms)
             (let ((e (gensym)))
               (Automaton e '() `(,e) '() '() '()))
             (complete-stack (foldl zip-Ms (car Ms) (cdr Ms))))))]))


(define (CFG->M D? G)
  (let ((ρ (env (map car G))))
    (let ((Ms (map (pRule->M D? ρ) G)))
      (foldr (λ (x a) (zip-Ms a x)) (car Ms) (cdr Ms)))))

(define (CFG->PDA G) (CFG->M #f G))
