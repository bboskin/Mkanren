#lang racket

(require "basics.rkt"
         "grammars.rkt")
(provide RE->DFA CNF->PDA)

;;;;;;;;;;;;;;;;;;;;;;;;
;; Automated generation of abstract machines from grammars


;; making DFAs (actually NFAs) from REs
(define (RE->DFA e)
  (match e
    [(? symbol? x)
     (let ((S (gensym 'S))
           (F (gensym 'F)))
       (Automaton S `(,F) `(,S ,F) `((,S ,x ,F)) `(,x) '()))]
    [`(,(? RE? e1) • ,(? RE? e2))
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 _) (Automaton S2 F2 A2 δ2 Σ2 _))
        (Automaton
         S1 F2 (set-union A1 A2)
         (set-union (map (λ (F) `(,F ε ,S2)) F1) (set-union δ1 δ2))
         (set-union Σ1 Σ2)
         '())])]
    [`(,(? RE? e1) U ,(? RE? e2))
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
         (Automaton S2 F2 A2 δ2 Σ2 Γ2))
        (let ((new-S (gensym 'S)))
          (Automaton
           new-S (set-union F1 F2) (set-union A1 A2)
           (append `((,new-S ε ,S1) (,new-S ε ,S2)) (set-union δ1 δ2))
           (set-union Σ1 Σ2)
           '()))])]
    [`(,(? RE? e1) +)
     (match (RE->DFA e1)
       [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
        (Automaton
         S1 F1 A1
         (append (map (λ (x) `(,x ε ,S1)) F1) δ1)
         Σ1
         '())])]
    [`(,(? RE? e1) *)
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

;; environment 
(define (env A)
  (let ((F (λ (x) (string->symbol (string-append (symbol->string x) "F")))))
    (foldr (λ (x a) `((,x ,(F x)) . ,a)) '() A)))

(define (start-state S ρ)
  (let ((pr? (assv S ρ)))
    (if pr?
        (car pr?)
        (error (format "No values for ~s" S)))))

(define (final-state S ρ)
  (let ((pr? (assv S ρ)))
    (if pr?
        (cadr pr?)
        (error (format "No values for ~s" S)))))

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
         (go (add S ρ e M) `((,S -> . ,es) . ,G))]))))
         