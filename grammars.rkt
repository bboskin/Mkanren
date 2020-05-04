#lang racket

(require "automata.rkt")

(provide RE? CFG? CNF?
         RE->CFG CFG->CNF

         RE->DFA CNF->PDA)

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
                    `(,@(reverse acc)
                      ,@(if (null? es) '() `((,S -> . ,es)))
                      ,@r))))
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
                   (error "not a CNF, but nothing to fix")))]
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
;; generating PDAs from CNFs

;; we maintain a list of many PDAs, each representing
;; a production rule state. They are then merged after all rules have
;; been processed
(define (init-PDAs G)
  (map
   (λ (x)
     (match x
       [`(,S -> ,es ...)
        (let ((F (gensym 'F)))
          (Automaton S `(,F) `(,S ,F) '() '() '(())))]))
   G))

(define (get-PDA S Ms)
  (let ((vs (filter (λ (x) (eqv? (Automaton-start-state x) S)) Ms)))
    (if vs (if (not (= 1 (length vs)))
               (error (format "~s automata associated to the ~s" (length vs) S))
               (car vs))
        (error 'get-PDA (format "No automaton with this start state ~s" S)))))

(define (set-PDA M Ms)
  (let ((S (Automaton-start-state M)))
    (foldr
     (λ (x a)
       (if (eqv? S (Automaton-start-state x))
           (cons M a)
           (cons x a)))
     '()
     Ms)))

(define (grow M r Ms)
  (match M
    [(Automaton S0 F A δ Σ `(,Γ))
     (match r
       ['ε (set-PDA (Automaton S0 F A `((,S0 ε ,(car F) preserve-stack) . ,δ) Σ `(,Γ)) Ms)]
       [`',a
        (let* ((δ (cons `(,S0 ,a ,(car F) preserve-stack) δ))
               (Σ (set-cons a Σ)))
          (set-PDA (Automaton S0 F A δ Σ  `(,Γ)) Ms))]
       [`(,(? symbol? P) ,(? symbol? Q))
        (match* ((get-PDA P Ms) (get-PDA Q Ms))
          [((Automaton Sp Fp Ap δp Σp Γp)
            (Automaton Sq Fq Aq δq Σq Γq))
           (let ((γ (gensym 'γ)))
             (let ((transition-S->P `(,S0 ε ,Sp (pop on #t push (,γ))))
                   (transition-P->Q `(,(car Fp) ε ,Sq (pop on ,γ push (,γ))))
                   (transition-Q->F `(,(car Fq) ε ,(car F) (pop on ,γ push ()))))

               (let ((new-δs (set-cons transition-S->P
                                       (set-cons transition-P->Q
                                                 (set-cons transition-Q->F δ)))))
               (let ((M (Automaton S0 F A new-δs Σ `(,(cons γ Γ)))))
                 (set-PDA M Ms)))))])]
       [else (error "unknown rule format")])]))

(define (line->PDAs ln Ms)
  (match ln
    [`(,S -> ,es ...)
     (foldr (λ (e a) (grow (get-PDA S a) e a)) Ms es)]))

(define (merge-PDAs M Ms)
  (foldr
   (λ (M1 Ma)
     (match* (M1 Ma)
       [((Automaton S1 F1 A1 δ1 Σ1 `(,Γ1))
         (Automaton Sa Fa Aa δa Σa `(,Γa)))
        (Automaton Sa Fa
                   (set-union A1 Aa)
                   (set-union δ1 δa)
                   (set-union Σ1 Σa)
                   `(,(set-union Γ1 Γa)))]))
   M
   Ms))

(define (CNF->PDA G)
  (let* ((Ms (foldr line->PDAs (init-PDAs G) G)))
    (merge-PDAs (get-PDA (caar G) Ms) Ms)))


