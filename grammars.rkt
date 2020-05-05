#lang racket

(require "automata.rkt")

(provide
 RE? CFG? CNF?
 RE->CFG CFG->CNF
 RE->DFA CNF->PDA
 
 set-equal?)


(define (snoc x s) (foldr cons `(,x) s))

(define (set-cons x s)
  (if (member x s) s (cons x s)))
(define (set-union s1 s2)
  (foldr set-cons s2 s1))

(define (set-equal? s1 s2)
  (and (= (length s1) (length s2))
       (andmap (λ (x) (member x s2)) s1)
       (andmap (λ (x) (member x s1)) s2)))

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
    [`',(? symbol? x) #t]
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
    [else #f]))


(define (CFG? G)
  (match G
    ['() #t]
    [`((,S -> ,es ...) . ,r)
     (and (not (null? es))
          (andmap production-rule? es)
          (CFG? r))]))

(define (CNF? G)
  (let ((S0 (caar G)))
    (let loop ((G G))
      (match G
        ['() #t]
        [`((,S -> ,es ...) . ,r)
         (and (andmap (CNF-production-rule? (eqv? S S0)) es)
              (not (null? es))
              (loop r))]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; conversion between grammars.

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; RE -> CFG

(define (RE->CFG-fn S e)
  (match e
    [(? symbol? s) `((,S -> ',s))]
    [`(,(? RE? e1) U ,(? RE? e2))
     (let ((S1 (gensym 'S))
           (S2 (gensym 'S)))
       (let ((G1 (RE->CFG-fn S1 e1))
             (G2 (RE->CFG-fn S2 e2)))
         `((,S -> ,S1 ,S2) ,@G1 ,@G2)))]
    [`(,(? RE? e1) • ,(? RE? e2))
     (let ((S1 (gensym 'S))
           (S2 (gensym 'S)))
       (let ((G1 (RE->CFG-fn S1 e1))
             (G2 (RE->CFG-fn S2 e2)))
         `((,S -> (,S1 ,S2)) ,@G1 ,@G2)))]
    [`(,(? RE? e1) +) (RE->CFG-fn S `(,e1 • (,e1 *)))]
    [`(,(? RE? e1) *)
     (let ((G (RE->CFG-fn S e1)))
       (match G
         [`((,S -> ,es ...) . ,rs)
          `((,S -> ,@(set-cons
                   'ε
                   (foldr
                    (λ (x a)
                      (match x
                        ['ε a]
                        [`',s (set-cons `(',s ,S) a)]
                        [(? symbol? P) (set-cons `(,P ,S) a)]
                        [`(,es ... ,L)
                         (if (eqv? L S)
                             (set-cons x a)
                             (set-cons `(,@es ,L ,S) a))]))
                    '()
                    es)))
            . ,rs)]))]
    [else (error  "Invalid RE!")]))

;; users can declare a start symbol if they want
(define-syntax RE->CFG
  (syntax-rules ()
    ((_ e) (RE->CFG-fn 'S e))
    ((_ S e) (RE->CFG-fn S e))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CFG -> CNF

(define (add-epsilon-subs-helper S ln)
  (cond
    [(null? ln) '(())]
    [else (let ((ans (add-epsilon-subs-helper S (cdr ln))))
            (if (eqv? S (car ln))
                (append (map (λ (x) (cons (car ln) x)) ans) ans)
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
    ['() acc]
    [`((,S -> . ,es) . ,r)
     (if (and (not (eqv? S S0)) (memv 'ε es))
         (let* ((es (remove 'ε es))
                (G (map
                    (add-epsilon-subs S)
                    `(,@(reverse acc)
                      ,@(if (null? es) '() `((,S -> . ,es)))
                      ,@r))))
           (remove-epsilons S0 G '()))
         (remove-epsilons S0 (cdr G) (cons (car G) acc)))]))



(define (CNF->CNF* G ans prevs Δ?)
  (match G
    ['() (if (CNF? ans) ans (error "not a CNF, but nothing to fix"))]
    [`((,S ->) . ,G)
     (let ((G (if Δ? `(,@ans (,S -> . ,(reverse prevs)) . ,G) G))
           (ans (if Δ? '() (snoc `(,S -> . ,(reverse prevs)) ans))))
       (CNF->CNF* G ans '() #f))]
    [`((,S -> (,s1) . ,es) . ,G)
     (CNF->CNF* `((,S -> ,s1 . ,es) . ,G) ans prevs Δ?)]
    [`((,S -> ε . ,es) . ,G)
     (CNF->CNF* `((,S -> . ,es) . ,G) ans `(ε . ,prevs) Δ?)]
    [`((,S -> ',a . ,es) . ,G)
     (CNF->CNF* `((,S -> . ,es) . ,G) ans `(',a . ,prevs) Δ?)]
    [`((,S -> (,(? symbol? P) ,(? symbol? Q)) . ,es) . ,G)
     (CNF->CNF* `((,S -> . ,es) . ,G) ans (set-cons `(,P ,Q) prevs) Δ?)]
    [`((,S -> ,(? symbol? P) . ,es) . ,G)
     (cond
       [(eqv? S P) (CNF->CNF* `((,S -> . ,es) . ,G) ans prevs #t)]
       [(assv P (append ans G))
        =>
        (λ (ln)
          (CNF->CNF* `((,S -> ,@(cddr ln) . ,es) . ,G) ans prevs #t))]
       [else (CNF->CNF* `((,S -> . ,es) . ,G) ans prevs #t)])]
    [`((,S -> (',a . ,ss) . ,es) . ,G)
     (let ((A (gensym S)))
       (let ((G `((,S -> (,A . ,ss) . ,es) . ((,A -> ',a) . ,G))))
         (CNF->CNF* G ans prevs #t)))]
    [`((,S -> (,(? symbol? P) ,(? symbol? Q) . ,ss) . ,es) . ,G)
     (let ((R (gensym S)))
       (let ((G `((,S -> (,R . ,ss) . ,es) . ((,R -> (,P ,Q)) . ,G))))
         (CNF->CNF* G ans prevs #t)))]
    [`((,S -> (,(? symbol? P) ',a . ,ss) . ,es) . ,G)
     (let ((Q (gensym S))
           (R (gensym S)))
       (let ((G `((,S -> (,R . ,ss) . ,es) (,R -> (,P ,Q)) (,Q -> ',a) . ,G)))
         (CNF->CNF* G ans prevs #t)))]
    [else (error 'CFG->CNF (format "invalid rule: ~s" (car G)))]))

(define (CFG->CNF G)
  (if (null? G)
      (error "No null grammars")
      (let* ((S0 (caar G))
             (new-S0 (gensym S0))
             (G  `((,new-S0 -> ,S0) . ,G))
             (G (remove-epsilons new-S0 (reverse G) '())))
        (CNF->CNF* G '() '() #f))))


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

(define (grow S ρ r M)
  (let ((Sf (final-state S ρ)))
    (match M
      [(Automaton S0 F A δ Σ Γ)
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
         [else (error "unknown rule format")])])))

(define (init-M ρ)
  (let* ((S0 (caar ρ))
         (F `(,(final-state S0 ρ)))
         (A (foldr append '() ρ)))
    (Automaton S0 F A '() '() '(()))))

(define (CNF->PDA G)
  (let ((ρ (env (map car G))))
    (let go ((G G) (M (init-M ρ)))
      (match G
        ['() M]
        [`((,S ->) . ,G)
         (go G M)]
        [`((,S -> ,e ,es ...) . ,G)
         (go `((,S -> . ,es) . ,G)
             (grow S ρ e M))]))))