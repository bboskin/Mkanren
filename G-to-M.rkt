#lang racket

(require "basics.rkt"
         "automata.rkt")
(provide RE->DFA CNF->PDA CNF->PDA/dict)

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
  (let ((pr? (assv S ρ)))
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
;; assumes that M1 already knows how to point to the start/final states
;; of M1
(define (zip-Ms M1 M2)
  (match* (M1 M2)
    [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
      (Automaton S2 F2 A2 δ2 Σ2 Γ2))
     (let ((k1 (length Γ1))
           (k2 (length Γ2)))
       (let ((δ1 (add-stack-ignores 'right δ1 (max 0 (- k2 k1))))
             (δ2 (add-stack-ignores 'right δ2 (max 0 (- k1 k2)))))
         (let ((Γ1 (append Γ1 (build-list (max 0 (- k2 k1)) (λ (_) '()))))
               (Γ2 (append Γ2 (build-list (max 0 (- k1 k2)) (λ (_) '())))))
           (Automaton S1 F1
                      (set-union A1 A2)
                      (append δ1 δ2)
                      (set-union Σ1 Σ2)
                      (map append Γ1 Γ2)))))]))

(define (zip-with-predefined M S1 ρ)
  (let* ((γ (gensym 'γ))
         (M0 (cdr M))
         (S S1)
         (F (final-state S1 ρ)))
    (match M0
      [(Automaton Sm Fm Am δm Σm Γm)
       (let ((M (zip-Ms
                 (Automaton S F (list S F)
                            `((,S ε ,Sm (pop on #t push (,γ)))
                              (,Fm ε ,F (pop on ,γ push ()))) '() `((,γ)))
                 M0)))
         (begin (displayln M) M))])))
;; 1pRule->M :
;; [Maybe Dictionary] x Environment -> Production-Rule' x Automaton
;;   -> Automaton
(define ((1pRule->M D? ρ) t)
  (match t
    [`(,S1 -> ε)
     (let* ((S S1)
            (F (final-state S ρ))
            (M (Automaton S (list F) (list S F) `((,S ε ,F)) '() '())))
       (begin (displayln M) M))]
    [`(,S1 -> ',(? symbol? a))
     (let* ((S S1)
            (F (final-state S ρ))
            (M (Automaton S (list F) (list S F) `((,S ,a ,F)) `(,a) '())))
       (begin (displayln M) M))]
    [`(,S1 -> ,(? symbol? P))
     (let (#;
           #;(γ (gensym 'γ))
           (M (and D? (assv P D?))))
       (cond
         [(and D? (assv P D?))
          =>
          (λ (M)
            (let ((M (zip-with-predefined M S1 ρ)))
             (begin (displayln M) M)))]
         [else (let* ((γ (gensym 'γ))
                      (S S1)
                      (F (final-state S ρ))
                      (Pf (final-state P ρ))
                      (M (Automaton S (list F) (list S F)
                                    `((,S ε ,P (pop on #t push (,γ)))
                                      (,Pf ε ,F (pop on ,γ push ()))) '() `((,γ)))))
             (begin (displayln M) M))])
       )]
    [`(,S1 -> ,es)
     (let ((M (foldr (λ (x y)
                       (let ((M (M-Concatenation x y)))
                         (begin (displayln M) M)))
                     ((1pRule->M D? ρ) `(,S1 -> ε))
                     (map (λ (e) ((1pRule->M D? ρ) `(,S1 -> ,e))) es))))
       (begin (displayln M) M))]))


#|

#(struct:Automaton A (AF) (A AF) ((A ε AF)) () ())

#(struct:Automaton A (AF) (A AF) ((A a AF)) (a) ())

#(struct:Automaton
A (AF) (A AF)
((A ε B (pop on #t push (γ38539)))
 (BF ε AF (pop on γ38539 push ())))
()
((γ38539)))
#(struct:Automaton A (AFb) (A AF Ab AFb)
 ((AF ε Ab preserve-stack)
  (A ε B (pop on #t push (γ38539)))
  (BF ε AF (pop on γ38539 push ()))
  (Ab ε AFb preserve-stack))
 ()
 ((γ38539)))
#(struct:Automaton
  A (AFbb) (A AF Ab AFb Abb AFbb)
  ((AF ε Ab preserve-stack)
   (A a AF preserve-stack)
   (AFb ε Abb preserve-stack)
   (Ab ε B (pop on #t push (γ38539)))
   (BF ε AFb (pop on γ38539 push ()))
   (Abb ε AFbb preserve-stack))
  (a)
  ((γ38539)))
#(struct:Automaton A (AFbb) (A AF Ab AFb Abb AFbb)
  ((AF ε Ab preserve-stack)
   (A a AF preserve-stack)
   (AFb ε Abb preserve-stack)
   (Ab ε B (pop on #t push (γ38539)))
   (BF ε AFb (pop on γ38539 push ()))
   (Abb ε AFbb preserve-stack))
  (a)
  ((γ38539)))

#(struct:Automaton
  A (AF) (A AF)
  ((A ε AF))
  ()
  ())

#(struct:Automaton A (AF) (A AF) ((A e AF)) (e) ())
#(struct:Automaton A (AF) (A AF) ((A ε F (pop on #t push (γ38540))) (FF ε AF (pop on γ38540 push ()))) () ((γ38540)))
#(struct:Automaton A (AFb) (A AF Ab AFb) ((AF ε Ab preserve-stack) (A ε F (pop on #t push (γ38540))) (FF ε AF (pop on γ38540 push ())) (Ab ε AFb preserve-stack)) () ((γ38540)))
#(struct:Automaton A (AFbb) (A AF Ab AFb Abb AFbb) ((AF ε Ab preserve-stack) (A e AF preserve-stack) (AFb ε Abb preserve-stack) (Ab ε F (pop on #t push (γ38540))) (FF ε AFb (pop on γ38540 push ())) (Abb ε AFbb preserve-stack)) (e) ((γ38540)))
#(struct:Automaton A (AFbb) (A AF Ab AFb Abb AFbb) ((AF ε Ab preserve-stack) (A e AF preserve-stack) (AFb ε Abb preserve-stack) (Ab ε F (pop on #t push (γ38540))) (FF ε AFb (pop on γ38540 push ())) (Abb ε AFbb preserve-stack)) (e) ((γ38540)))
#(struct:Automaton B (BF) (B BF) ((B d BF)) (d) ())
#(struct:Automaton B (BF) (B BF) ((B c BF)) (c) ())
#(struct:Automaton F (FF) (F FF) ((F aa FF)) (aa) ())
#(struct:Automaton F (FF) (F FF) ((F bbb FF)) (bbb) ())

|#

;; pRule->M :
;; [Maybe Dictionary] x Environment -> Production-Rule' x Automaton
;;   -> Automaton
(define ((pRule->M D? ρ) t)
  (match t
    [`(,S1 -> ,es ...)
     (let ((Rs (remove `(,S1 -> ,S1) (map (λ (x) `(,S1 -> ,x)) es))))
       (let ((Ms (map (1pRule->M D? ρ) Rs)))
         (if (null? Ms)
             (Automaton 'S '() '(S) '() '() '())
             (let ((tM (foldr zip-Ms (car Ms) (cdr Ms))))
               tM))))]))


(define (CFG->M D? G)
  (let ((ρ (env (map car G))))
    (let ((Ms (map (pRule->M D? ρ) G)))
      (foldr (λ (x a) (zip-Ms a x)) (car Ms) (cdr Ms)))))

(define (CFG->PDA G) (CFG->M #f G))
#|
> (define S (CFG->PDA '((S -> ε ('a S)))))
> S
(Automaton
 'Start87088
 '(SFbb SFb)
 '(Start87088 S SF Sb SFb Sbb SFbb Sb SFb)
 '((Start87088 ε S preserve-stack)
   (Start87088 ε Sb preserve-stack)
   (SF ε Sb preserve-stack)
   (S a SF preserve-stack)
   (SFb ε Sbb preserve-stack)
   (Sb ε Sb (pop on #t push (γ87087)))
   (SFb ε SFb (pop on γ87087 push ()))
   (Sbb ε SFbb preserve-stack)
   (Sb ε SFb preserve-stack))
 '(a)
 '((γ87087)))


|#
#;
(define (add/dict S ρ r M DICT)
  (match M
    [(Automaton S0 F A δ Σ Γ)
     (let  ((Sf (final-state S ρ)))
       (match r
         ['ε (Automaton S0 F A (set-cons `(,S ε ,Sf preserve-stack) δ) Σ Γ)]
         ;; new clause used for miniKanren compilation
         [(? symbol? y)
          (displayln "here0")
          (let ((v (assv y DICT)))
            (if v
                (match (cdr v)
                  [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
                   (let ((k-stacks (max (length Γ) (length Γ1))))
                     (let ((A (append A A1))
                           (δ `((,S ε ,S1 . ,(build-list k-stacks (λ (_) 'preserve-stack)))
                                ,@(map (λ (p)
                                         `(,(car p) ε ,(cadr p) . ,(build-list k-stacks (λ (_) 'preserve-stack))))
                                       (cartesian-product F1 F))
                                . ,(append (add-stack-ignores 'right δ1 (- k-stacks (length Γ1)))
                                           (add-stack-ignores 'right δ (- k-stacks (length Γ)))))))
                       (Automaton S0 F A δ Σ Γ)))])
                (error 'defrel (format "not a defined relation ~s" y) )))]
         [`',a
          (let* ((δ (set-cons `(,S ,a ,Sf preserve-stack) δ))
                 (Σ (set-cons a Σ)))
            (Automaton S0 F A δ Σ Γ))]
         [`(,(? symbol? P) ,(? symbol? Q))
          (cond
            [(assv P DICT) =>
                           
             (λ (M1)
               (displayln "here1")
               (cond
                 [(assv Q DICT) =>
                  (λ (M2)
                    (match* ((cdr M1) (cdr M2))
                      [((Automaton Sp Fp Ap δp Σp Γp)
                        (Automaton Sq Fq Aq δq Σq Γq))
                       'TODO]))]
                 [else
                  (match (cdr M1)
                    [(Automaton Sp Fp Ap δp Σp Γp)
                     (let ((Fq (final-state Q ρ))
                           (γ (gensym 'γ)))
                       (let ((S->P `(,S ε ,Sp (pop on #t push (,γ))))
                             (P->Q (map (λ (Fp) `(,Fp ε ,Q (pop on ,γ push (,γ)))) Fp))
                             (Q->F `(,Fq ε ,Sf (pop on ,γ push ())))
                             (k-stacks (max (length Γ) (length Γp))))
                         (let ((A (set-union A Ap))
                               (Σ (set-union Σ Σp))
                               (δ (append-map
                                   (λ (x)
                                     (add-stack-ignores
                                      'right
                                      (list x)
                                      (- k-stacks (length (cdddr x)))))
                                   (set-union `(,S->P ,@P->Q ,Q->F) (set-union δp δ))))
                               (Γ (map set-union
                                       (append
                                        `((,γ . ,(car Γ)) . ,(cdr Γ))
                                        (build-list (- k-stacks (length Γ))
                                                    (λ (_) '())))
                                       (append Γp
                                               (build-list (- k-stacks (length Γp))
                                                    (λ (_) '()))))))
                           (Automaton S0 F A δ Σ Γ))))])]))]
            [(assv Q DICT) =>
             (λ (M2)
               (match (cdr M2)
                 [(Automaton Sq Fq Aq δq Σq Γq)
                  (let ((Fp (final-state P ρ))
                        (γ (gensym 'γ)))
                    (let ((S->P `(,S ε ,P (pop on #t push (,γ))))
                          (P->Q `(,Fp ε ,Sq (pop on ,γ push (,γ))))
                          (Q->F (map (λ (Fq) `(,Fq ε ,Sf (pop on ,γ push ()))) Fq))
                          (k-stacks (max (length Γ) (length Γq))))
                      (let ((A (set-union A Aq))
                            (Σ (set-union Σ Σq))
                            (δ (map
                                (λ (x)
                                  (add-stack-ignores
                                   'right x (- k-stacks (length (cdddr x)))))
                                (set-union
                                 `(,S->P ,P->Q ,@Q->F)
                                 (set-union δq δ))))
                            (Γ `((,γ . ,(car Γ)))))
                        (Automaton S0 F A δ Σ Γ))))]))]
            [else
             (let ((Fp (final-state P ρ))
                   (Fq (final-state Q ρ))
                   (γ (gensym 'γ)))
               (let ((S->P `(,S ε ,P (pop on #t push (,γ))))
                     (P->Q `(,Fp ε ,Q (pop on ,γ push (,γ))))
                     (Q->F `(,Fq ε ,Sf (pop on ,γ push ()))))
                 (let ((δ (set-union `(,S->P ,P->Q ,Q->F) δ))
                       (Γ `((,γ . ,(car Γ)))))
                   (Automaton S0 F A δ Σ Γ))))])]
         [else (error "unknown rule format")]))]))

;;  CNF->PDA/dict : Grammar x Dictionary -> Automaton
(define (CNF->PDA/dict G DICT)
  (let ((ρ (env (map car G))))
    (let go ((M (init-M ρ))
             (G G))
      (match G
        ['() M]
        [`((,S ->) . ,G) (go M G)]
        [`((,S -> ,e ,es ...) . ,G)
         (go (add S ρ e M DICT)
             `((,S -> . ,es) . ,G))]))))