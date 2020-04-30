#lang racket

(require "automata.rkt")

(define (set-cons x s) (if (member x s) s (cons x s)))

;;;;;;;;;;;;;;;;;
;; Definition of a production rule.
;; points from a symbol to either an atom, ε,
;; or a series (concatenation) of symbols and atoms.

(define (production-rule? x)
  (match x
    [`(,(? symbol?) -> ε) #t]
    [`(,(? symbol?) -> (quote ,(? symbol?))) #t]
    [`(,(? symbol?) -> ,(? symbol?)) #t]
    [`(,(? symbol?) -> ,(? symbol? s) s2...) #t]
    [else #f]))

(define (CFG? G) (andmap production-rule? G))



;; This works!
(define A
  '((S -> 'a)
    (S -> P)
    (P -> 'b)))

(define AnBn
  '((S -> ε)
    (S -> 'a S 'b)))

(define Bool
  '((S -> 'T)
    (S -> 'F)
    (S -> 'p)
    (S -> 'q)
    (S -> 'not S)
    (S -> 'andbegin S* 'andend)
    (S -> 'orbegin S* 'orend)
    (S* -> ε)
    (S* -> S S*)))

;; each DFA has only one final state


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




