#lang racket

(require "automata.rkt")

(provide RE? CFG? CNF?
         RE->CFG CFG->CNF

         RE->DFA CFG->PDA)

(define (set-cons x s) (if (member x s) s (cons x s)))

(define (member* s ls)
  (cond
    [(eqv? ls s) #t]
    [(not (cons? ls)) #f]
    [else (or (member* s (car ls))
              (member* s (cdr ls)))]))


(define (more-terminals? es)
  (ormap
   (λ (x)
     (match x
       [',(? terminal?) #t]
       [else #f]))
   es))

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

;; the first symbol of the first line is taken to be the start symbol.



(define (terminal? x)
  (match x
    [''(,(symbol? x)) #t]
    [(? symbol?) #t]
    [else #f]))

(define (production-rule? x)
  (or (terminal? x)
      (and (list? x)
           (andmap terminal? x))))

(define ((CNF-production-rule? ε-ok?) x)
  (match x
    [`',(? symbol? s) #t]
    ['ε ε-ok?]
    [`(,(? symbol? P) ,(? symbol? Q)) #t]
    [else (displayln x) #f]))


(define (CFG? G)
  (match G
    ['() #t]
    [`((,S -> ,es ...) . ,r)
     (and (andmap production-rule? es)
          (CFG? r))]))

(define (CNF? G)
  (let ((S0 (caar G)))
    (let loop ((G G))
      (match G
        ['() #t]
        [`((,S -> ,es ...) . ,r)
         (and (andmap (CNF-production-rule? (eqv? S S0)) es)
              (loop r))]))))


;; conversion between grammars.
;; We can convert RE's to CFGs, and we can convert CFGs to RE's

(define (RE->CFG-fn S e)
  (match e
    [(? symbol? s) `((,S -> ',s))]
    [`(,(? RE? e1) *)
     (let ((G (RE->CFG-fn S e1)))
       (set-cons
        `(,S -> ε)
        (foldr
         (λ (x a)
           (match x
             [`(,P -> ε) a]
             [`(,P -> ',s) (set-cons `(,S -> ',s ,S) a)]
             [`(,P -> ,L) (if (eqv? L S) a (set-cons `(,S -> ,L) a))]
             [`(,P -> ,es ... ,L) (set-cons `(,S -> ,@es ,S) a)]
             [else (set-cons `(,S -> ,@(cddr x) ,S) a)]))
         '()
         G)))]
    [`(,(? RE? e1) U ,(? RE? e2))
     (let ((S1 (gensym 'S))
           (S2 (gensym 'S)))
       (let ((G1 (RE->CFG-fn S1 e1))
             (G2 (RE->CFG-fn S2 e2)))
         `((,S -> ,S1) (,S -> ,S2) ,@G1 ,@G2)))]
    [`(,(? RE? e1) • ,(? RE? e2))
     (let ((S1 (gensym 'S)))
       (let ((G1 (RE->CFG-fn S e1))
             (G2 (RE->CFG-fn S1 e2)))
         (set-union
          (map (λ (x)
                 (match x
                   [`(,P -> ε) `(,P -> ,S1)]
                   [`(,P -> ,xs ...) `(,P -> ,@xs ,S1)]))
               G1)
          G2)))]
    [`(,(? RE? e1) +) (RE->CFG-fn S `(,e1 • (,e1 *)))]
    [else (error  "Invalid RE!")]))

(define-syntax RE->CFG
  (syntax-rules ()
    ((_ e) (RE->CFG-fn 'S e))
    ((_ S e) (RE->CFG-fn S e))))


;; new start variable
;; eliminate epsilons
;; shorten rules (introduce symbols)
;; expand rules

(define (add-epsilon-subs-helper S ln)
  (cond
    [(null? ln) '(())]
    [else (let ((ans (add-epsilon-subs-helper S (cdr ln))))
            (if (eqv? S (car ln))
                `(,@(map (λ (x) (cons (car ln) x)) ans) ,@ans)
                (map (λ (x) (cons (car ln) x)) ans)))]))

(define ((add-epsilon-subs S) ln)
  (match ln
    [`(,P -> . ,es)
     `(,P -> . ,(foldr
                 (λ (ln a)
                   (match ln
                     ['ε (set-cons 'ε a)]
                     [(? symbol? s)
                      (if (eqv? P S) a
                          (if (eqv? s S)
                              (set-cons 'ε (set-cons s a))
                              (set-cons s a)))]
                     [`',(? symbol? s) (set-cons `',s a)]
                     [else (append (map (λ (x)
                                          (if (= (length x) 1) (car x) x))
                                        (add-epsilon-subs-helper S ln)) a)]))
                 '()
                 es))]))

(define (remove-epsilons S0 G acc)
  (match G
    ['() (reverse acc)]
    [`((,S -> . ,es) . ,r)
     (if (and (not (eqv? S S0)) (memv 'ε es))
         (let* ((es (remove 'ε es))
                (G (map
                    (add-epsilon-subs S)
                    `(,@(reverse acc) (,S -> . ,es) ,@r))))
           (remove-epsilons S0 G '()))
         (remove-epsilons S0 (cdr G) (cons (car G) acc)))]))

(define (fix-epsilons? S0 G)
  (and (member* 'ε G)
       (reverse (remove-epsilons S0 (reverse G) '()))))

(define (replace-in-G ln G)
  (foldr
   (λ (x a)
     (if
      (eqv? (car x) (car ln))
      (cons ln a)
      (cons x a)))
   '()
   G))

(define (find-and-fix-line ln G seen prevs Δ?)
  (match ln
    [`(,S -> ,es ...)
     (match es
       ;; got through everything -- did we actually change anything?
       ['() (and Δ? `(,@(reverse seen) (,S -> ,@(reverse prevs)) ,@G))]
       ;; the start symbol is allowed to have an epsilon transition
       ;; (we assume that by now epsilons have been removed elsewhere)
       [`(ε . ,es)
        (find-and-fix-line `(,S -> ,@es) G seen `(ε . ,prevs) Δ?)]
       ;; terminals are already CNF
       [`(',a . ,es)
        (find-and-fix-line `(,S -> ,@es) G seen `(',a . ,prevs) Δ?)]
       ;; split-rules are already CNF
       [`((,(? symbol? P) ,(? symbol? Q)) . ,es)
        (find-and-fix-line `(,S -> ,@es) G seen (cons `(,P ,Q) prevs) Δ?)]
       ;; UNIT RULES to eliminate
       [`(,(? symbol? P) . ,es)
        (if (eqv? S P)
            ;; if it's a self-ref we can just drop it
            (find-and-fix-line `(,S -> . ,es) G seen prevs #t)
            ;; otherwise we have work to do
            (let ((ln (assv P G)))
              (if ln
                  ;; we take every rule that this symbol has and give it to our current symbol as well
                  (find-and-fix-line `(,S -> ,@(reverse (cddr ln)) . ,es) G seen prevs #t)
                  ;; or if it has no way to succeed then we can forget about it
                  (find-and-fix-line `(,S -> . ,es) G seen prevs #t))))]
       [`((,s1) . ,es) (find-and-fix-line `(,S -> ,s1 . ,es) G seen prevs #t)]
       [`((,s1 . ,ss) . ,es)
        (match s1
          ;; if it's a terminal then we can make a new state
          [`',a
           (let ((A (gensym S)))
             (let ((A-ln `(,A -> ',a)))
               (find-and-fix-line `(,S -> (,A . ,ss) . ,es) `((,A -> ',a) . ,G) seen prevs #t)))]
          ;; if it's a state then we need to look at the two top symbols
          [(? symbol? P)
           (match ss
             [`(,(? symbol? Q) . ,ss)
              (let ((R (gensym S)))
                (find-and-fix-line
                 `(,S -> (,R . ,ss) . ,es)
                 (cons `(,R -> (,P ,Q)) G)
                 seen
                 prevs
                 #t))]
             [`(',a . ,ss)
              ;; here, we can do what we did above and then make a new CNF-valid rule
              (let ((Q (gensym S))
                    (R (gensym S)))
                (find-and-fix-line
                 `(,S -> (,R . ,ss) . ,es)
                 (append `((,R -> (,P ,Q)) (,Q -> ',a)) G)
                 seen
                 `((,P ,Q) . ,prevs)
                 #t))]
             
             [else (error (format "Invalid production rule symbols in ss ~s" ss))])]
          [else (error (format "Invalid production rule symbols in es ~s" es))])]
       [l (error 'find-and-fix (format "invalid rule `(~s -> ~s)" S l))])]))


(define (CFG->CNF G)
  (if (null? G)
      (error "No null grammars")
      (let* ((S0 (caar G))
             (new-S0 (gensym S0))
             (G  `((,new-S0 -> ,S0) . ,G))
             (G (let ((v (fix-epsilons? new-S0 G)))
                  (if v v G))))
        
        (let loop ((G G)
                   (acc '()))
          (cond
            [(null? G)
             (let ((G (reverse acc)))
               (if (CNF? G)
                   G
                   (begin (displayln "result is:")
                          (displayln G)
                          (displayln "start state is")
                          (displayln new-S0)
                          (error "not a CNF, but nothing to fix"))))]
            [else
             (let ((G2 (find-and-fix-line (car G) (cdr G) acc '() #f)))
                 (if G2
                     (loop G2 '())
                     (loop (cdr G) (cons (car G) acc))))])))))


;;;;;;;;;;;;;;;;;;;;;;;;
;; Automated generation of abstract machines from grammars

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
         (set-union (map (λ (F) `(,F ε ,S2)) F1) δ1 δ2)
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
;; CFGs and PDAs

(define (terminal-δs/push S2 S s δs γ new-γ)
  (if (eqv? #t γ)
      `((,S ,s ,S2 (pop on #t push (,new-γ))) . ,δs)
      `((,S ,s ,S2 (pop on ,γ push (,new-γ))) . ,δs)))

(define (terminal-δs/pop S2 S s δs γ)
  (if (eqv? #t γ)
      `((,S ,s ,S2 preserve-stack) . ,δs)
      `((,S ,s ,S2 (pop on ,γ push ())) . ,δs)))

(define (substate-δs S s s-F S2 δs γ)
  (if (eqv? #t γ)
      `((,S ε ,s preserve-stack)
        (,s-F ε ,S2 preserve-stack)
        ,@δs)
      `((,S ε ,s (pop on ,γ push (,γ)))
        (,s-F ε ,S2 (pop on ,γ push (,γ)))
        ,@δs)))

(define (rule->M F r A)
  'TODO
  #;(match r
    [`(,S0 -> ,e ,es ...)
     (let ((init-δs `()))
       (let loop ((S S0)
                  (es (cons e es))
                  (A '())
                  (δs init-δs)
                  (Σ '())
                  (γs `(,(gensym S0))))
         (match es
           ['() (Automaton S `(,S . ,F) `(,S . ,A) δs Σ `(,γs))]
           ['(ε) (Automaton S `(,S . ,F) `(,S . ,A) δs Σ `(,γs))]
           [`(',(? symbol? s))
            (let ((δs `((,S ,s ,S2 (pop on ,(car γs) push (,(car γs)))) . ,δs)))
                    (Automaton S `(,S2 . ,F) `(,S2 .  ,A) δs Σ `(,γs)))]
           [`(,(? symbol? S2))
            (let ((δs `((,S ,s ,S2 (pop on ,(car γs) push (,s))) . ,δs)))
                  (Automaton S `(,S2 . ,F) `(,S2 .  ,A) δs Σ `(,γs)))])
         (match (car es)
           ['ε
            (if (null? γs)
                (Automaton S0 `(,S . ,F) A δs Σ `(,γs))
                (error 'rule-m (format "Invalid production rule ~s" r)))]
           [',(? symbol? s)
            (let ((S2 (gensym S0)))
              (if (eqv? curr #t)
                  (let ((δs `((,S ,s ,S2 preserve-stack) . ,δs)))
                    (values Γ A δs Σ))
                  (let ((δs `((,S ,s ,S2 (pop on ,curr push (,s))) . ,δs)))
                    (values Γ A δs Σ))))]
           [(? symbol? s)
            (if (eqv? s S)
                (if (null? γs)
                    (values Γ A δs Σ)
                    (values Γ A δs Σ))
              (let ((s-f (begin (displayln s)
                                (car F))))
                (if (eqv? curr #t)
                    (values Γ A (set-cons `(,S ε ,s preserve-stack) δs) Σ)
                    (values Γ A (set cons `(,S ε ,s (pop on ,curr push (,curr))) δs) Σ))))]
           
           [else (error 'rule->M (format "invalid production rule tag ~s" e))])))]))
(define (rule->δ PDAs x)
  (let ((F (Automaton-final-states (cdr (assv (car x) PDAs)))))
    (match x
    [`(,S0 -> ε) (values '() '() `((,S0 ε ,F preserve-stack)) '())]
    [`(,S0 -> ',(? symbol? s)) (values '() '() `((,S0 ,s ,F preserve-stack)) `(,s))]
    [`(,S0 -> ,(? symbol? S)) (values '() '() `((,S0 ε ,S preserve-stack)) `())]
    [else
     (match (rule->M F x)
       [(Automaton S F A Δ Σ Γs) 'TODO]
       #;
     (let ((init-δs `()))
       (let loop ((S S0)
                  (es (cons e es))
                  (Γ '())
                  (A '())
                  (δs init-δs)
                  (Σ '())
                  (curr #t))
         (match es
           ['() (if (eqv? curr #t)
                    (let ((δs `((,S ε ,F preserve-stack) . ,δs)))
                      (values Γ A δs Σ))
                    (let ((δs `((,S ε ,F (pop on ,curr push ())) . ,δs)))
                      (values (set-cons curr Γ) A δs Σ)))]
           [`(ε)
            (if (eqv? curr #t)
                (let ((δs `((,S ε ,F preserve-stack) . ,δs)))
                  (values Γ A δs Σ))
                (let ((δs `((,S ε ,F (pop on ,curr push ())) . ,δs)))
                  (values (set-cons curr Γ) A δs Σ)))]
           [`(',(? symbol? s))
            (if (eqv? curr #t)
                (let ((δs `((,S ,s ,F preserve-stack) . ,δs)))
                  (values Γ A δs Σ))
                (let ((δs `((,S ,s ,F (pop on ,curr push ())) . ,δs)))
                  (values Γ A δs Σ)))]
           [`(,(? symbol? s))
            (if (eqv? s S)
                (if (eqv? curr #t)
                    (values Γ A δs #;(set-cons `(,S ε ,s preserve-stack) δs) Σ)
                    (values Γ A δs #;(set cons `(,S ε ,s (pop on ,curr push (,curr))) δs) Σ))
              (let ((s-f (begin (displayln s)
                                (car (Automaton-final-states (cdr (assv s PDAs)))))))
                (if (eqv? curr #t)
                    (values Γ A (set-cons `(,S ε ,s preserve-stack) δs) Σ)
                    (values Γ A (set cons `(,S ε ,s (pop on ,curr push (,curr))) δs) Σ))))]
           [`(',(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (Σ (set-cons s Σ)))
              (if (more-terminals? r)
                  (let* ((γ (gensym 'γ))
                         (Γ (set-cons γ Γ)))
                    (loop S2 r Γ A (terminal-δs/push S2 S s δs curr γ) Σ γ))
                  (loop S2 r Γ A (terminal-δs/pop S2 S s δs curr) Σ curr)))]
           [`(,(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (s-F (begin (displayln s)
                               (car (Automaton-final-states (cdr (assv s PDAs)))))))
              (loop S2 r Γ A (substate-δs S s s-F S2 δs curr) Σ curr))]))))])))

#;
(define (rule->δ PDAs x)
  (match x
    [`(,S0 -> ε)
     (let ((F (car (Automaton-final-states (cdr (assv S0 PDAs))))))
       (values '() '() `((,S0 ε ,F preserve-stack)) '()))]
    [`(,S0 -> ',(? symbol? s))
     (let ((F (car (Automaton-final-states (cdr (assv S0 PDAs))))))
       (values '() '() `((,S0 ,s ,F preserve-stack)) `(,s)))]
    [`(,S0 -> ,(? symbol? S))
     (let ((F (car (Automaton-final-states (cdr (assv S0 PDAs))))))
       (values '() '() `((,S0 ε ,S preserve-stack)) `()))]
    [`(,S0 -> ,e ,es ...)
     (let* ((F (car (Automaton-final-states (cdr (assv S0 PDAs)))))
            (init-δs `()))
       (let loop ((S S0)
                  (es (cons e es))
                  (Γ '())
                  (A '())
                  (δs init-δs)
                  (Σ '())
                  (curr #t))
         (match es
           ['() (if (eqv? curr #t)
                    (let ((δs `((,S ε ,F preserve-stack) . ,δs)))
                      (values Γ A δs Σ))
                    (let ((δs `((,S ε ,F (pop on ,curr push ())) . ,δs)))
                      (values (set-cons curr Γ) A δs Σ)))]
           [`(ε)
            (if (eqv? curr #t)
                (let ((δs `((,S ε ,F preserve-stack) . ,δs)))
                  (values Γ A δs Σ))
                (let ((δs `((,S ε ,F (pop on ,curr push ())) . ,δs)))
                  (values (set-cons curr Γ) A δs Σ)))]
           [`(',(? symbol? s))
            (if (eqv? curr #t)
                (let ((δs `((,S ,s ,F preserve-stack) . ,δs)))
                  (values Γ A δs Σ))
                (let ((δs `((,S ,s ,F (pop on ,curr push ())) . ,δs)))
                  (values Γ A δs Σ)))]
           [`(,(? symbol? s))
            (if (eqv? s S)
                (if (eqv? curr #t)
                    (values Γ A δs #;(set-cons `(,S ε ,s preserve-stack) δs) Σ)
                    (values Γ A δs #;(set cons `(,S ε ,s (pop on ,curr push (,curr))) δs) Σ))
              (let ((s-f (begin (displayln s)
                                (car (Automaton-final-states (cdr (assv s PDAs)))))))
                (if (eqv? curr #t)
                    (values Γ A (set-cons `(,S ε ,s preserve-stack) δs) Σ)
                    (values Γ A (set cons `(,S ε ,s (pop on ,curr push (,curr))) δs) Σ))))]
           [`(',(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (Σ (set-cons s Σ)))
              (if (more-terminals? r)
                  (let* ((γ (gensym 'γ))
                         (Γ (set-cons γ Γ)))
                    (loop S2 r Γ A (terminal-δs/push S2 S s δs curr γ) Σ γ))
                  (loop S2 r Γ A (terminal-δs/pop S2 S s δs curr) Σ curr)))]
           [`(,(? symbol? s) . ,r)
            (let* ((S2 (gensym S0))
                   (A (cons S2 A))
                   (s-F (begin (displayln s)
                               (car (Automaton-final-states (cdr (assv s PDAs)))))))
              (loop S2 r Γ A (substate-δs S s s-F S2 δs curr) Σ curr))])))]))

(define (get-states P)
  (foldr
   (λ (x a)
     (if (memv (car x) a)
         a
         (cons (car x) a)))
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
                       (let-values (((γ A a Σ1) (rule->δ PDAs x)))
                         (loop r
                               (append a δs)
                               (append γ Γ)
                               (set-union A All)
                               (set-union Σ Σ1)))]))))
      (let ((F (Automaton-final-states (cdr (assv S PDAs))))
            (A (set-union
                (foldr set-union '() (map Automaton-all-states (map cdr PDAs)))
                A))
            (δ (append
                (foldr append '() (map Automaton-transition-function (map cdr PDAs)))
                extra-δs))
            (Γ (list Γ)))
        (Automaton S F A δ Σ Γ)))))