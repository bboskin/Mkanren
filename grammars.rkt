#lang racket

(require "automata.rkt")

(provide RE? CFG?
         RE->DFA
         CFG->PDA
         RE->CFG)

(define (set-cons x s) (if (member x s) s (cons x s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Grammars: REs and CFGs, and how to convert an RE into a CFG

(define (RE? e)
  (match e
    [(? symbol?) #t]
    [`(,(? RE?) • ,(? RE?)) #t]
    [`(,(? RE?) U ,(? RE?)) #t]
    [`(,(? RE?) +) #t]
    [`(,(? RE?) *) #t]
    [else #f]))


(define (CFG? G)
  (define (production-rule? x)
    (match x
      [`(,(? symbol?) -> ε) #t]
      [`(,(? symbol?) -> (quote ,(? symbol?))) #t]
      [`(,(? symbol?) -> ,(? symbol?)) #t]
      [`(,(? symbol?) -> ,(? symbol? s) s2...) #t]
      [else #f]))
  (andmap production-rule? G))

(define (RE->CFG e)
  'TODO)

(define (RE->DFA e)
  (match e
    [(? symbol? x)
     (let ((S (gensym 'S))
           (F (gensym 'F)))
       (Automaton S `(,F) `(,S ,F) `((,S ,(λ (i) (eqv? x i)) ,F)) `(,x) '()))]
    [`(,(? RE? e1) • ,(? RE? e2))
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 Γ1) (Automaton S2 F2 A2 δ2 Σ2 Γ2))
        (Automaton
         S1 F2 (set-union A1 A2)
         (append (map (λ (F) `(,F ε ,S2)) F1) δ1 δ2)
         (set-union Σ1 Σ2)
         '())])]
    [`(,(? RE? e1) U ,(? RE? e2))
     (match* ((RE->DFA e1) (RE->DFA e2))
       [((Automaton S1 F1 A1 δ1 Σ1 Γ1)
         (Automaton S2 F2 A2 δ2 Σ2 Γ2))
        (let ((new-S (gensym 'S)))
          (Automaton
           new-S (set-union F1 F2) (set-union A1 A2)
           (append `((,new-S ε ,S1) (,new-S ε ,S2)) δ1 δ2)
           (set-union Σ1 Σ2)
           '()))])]
    [`(,(? RE? e1) +)
     (match (RE->DFA e1)
       [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
        (let ((new-S (gensym 'S)))
          (Automaton
           S1 (cons S1 F1) A1
           (append (map (λ (x) `(,x ε ,S1)) F1) δ1)
           Σ1
           '()))])]
    [`(,(? RE? e1) *)
     (match (RE->DFA e1)
       [(Automaton S1 F1 A1 δ1 Σ1 Γ1)
        (let ((new-S (gensym 'S)))
          (Automaton
           S1 F1 A1
           (append (map (λ (x) `(,x ε ,S1)) F1) δ1)
           Σ1
           '()))])]
    [else (error "Not a valid RE")]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CFGs and PDAs


(define (ε-δs S S2 δs)
  `((,S ε ,S2 preserve-stack) . ,δs))

(define (terminal-δs S2 S s δs)
  `((,S ,s ,S2 preserve-stack) . ,δs))

(define (substate-δs γ S s s-F S2 δs)
  `((,S ε ,s (pop on #t push (,γ)))
    (,s-F ε ,S2 (pop on ,γ push ()))
    ,@δs))

(define (rule->δ PDAs x r)
  (match x
    [`(,S0 -> ε)
     (let ((F (car (Automaton-final-state (cdr (assv S0 PDAs))))))
       (values '() '() `((,S0 ε ,F preserve-stack)) '()))]
    [`(,S0 -> ',(? symbol? s))
     (let ((F (car (Automaton-final-state (cdr (assv S0 PDAs))))))
       (values '() '() `((,S0 ,s ,F preserve-stack)) `(,s)))]
    [`(,S0 -> ,e ,es ...)
     (let* ((F (car (Automaton-final-state (cdr (assv S0 PDAs)))))
            (γ (gensym S0))
            (S2 (gensym S0))
            (init-δs `((,S0 ε ,S2 (pop on #t push (,γ))))))
       (let loop ((S S2)
                  (es (cons e  es))
                  (Γ `(,γ))
                  (A `(,S2))
                  (δs init-δs)
                  (Σ '()))
         (match es
           ['()
            (let ((δs `((,S ε ,F (pop on ,γ push ())) . ,δs)))
              (values Γ A δs Σ))]
           [`(ε . ,r)
            (loop S2 r Γ A (ε-δs S S2 δs) Σ)]
           [`(',(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (Σ (cons s Σ)))
              (loop S2 r Γ A (terminal-δs S2 S s δs) Σ))]
           [`(,(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (s-F (car (Automaton-final-state (cdr (assv s PDAs)))))
                   (γ (gensym S0))
                   (Γ (cons γ Γ)))
              (loop S2 r Γ A (substate-δs γ S s s-F S2 δs) Σ))])))]))

(define (get-states P)
  (foldr
   (λ (x a)
     (if (memv (car x) a) a (cons (car x) a)))
   '()
   P))

(define (init-group S)
  (let ((F (gensym 'F)))
    (cons S (Automaton S `(,F) `(,S ,F) '() '() '(())))))


(define (CFG->PDA S G)
  (let ((PDAs (map init-group (get-states G))))
    (let-values (((Γ A extra-δs Σ)
                  (let loop ((ls G)
                             (δs '())
                             (Γ '())
                             (All '())
                             (Σ '()))
                    (match ls
                      ['() (values Γ All δs Σ)]
                      [`(,x . ,r)
                       (let-values (((γ A a Σ1) (rule->δ PDAs x r)))
                         (loop r
                               (append a δs)
                               (append γ Γ)
                               (set-union A All)
                               (append Σ Σ1)))]))))
      (let ((F (Automaton-final-state (cdr (assv S PDAs))))
            (A (set-union
                (foldr set-union '() (map Automaton-all-states (map cdr PDAs)))
                A))
            (δ (append
                (foldr append '() (map Automaton-transition-function (map cdr PDAs)))
                extra-δs))
            (Γ (list Γ)))
        (Automaton S F A δ Σ Γ)))))