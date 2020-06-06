#lang racket

(require "basics.rkt")

(provide RE? CFG? CNF?
         RE->CFG CFG->CNF
         set-equal??
         G-Union
         G-Concatenation
         G-Intersection)

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
    [`((,S -> . ,es) . ,G)
     (and (not (null? es)) 
          (andmap production-rule? es)
          (CFG? G))]))

(define (CNF? G)
  (let ((S0 (caar G)))
    (let loop ((G G))
      (match G
        ['() #t]
        [`((,S -> ,es ...) . ,r)
         (and (andmap (CNF-production-rule? (eqv? S S0)) es)
              (not (null? es))
              (loop r))]))))

(define (extract-Σ G)
  (match G
    ['() '()]
    [`',a `(,a)]
    [`(,a . ,d) (set-union (extract-Σ a) (extract-Σ d))]
    [else '()]))

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

;; TODO : get rid of ininite loop for all grammars
;; (ctrex: (S -> 'a S))

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
                      (if (eqv? s S)
                          (set-cons 'ε (set-cons s a))
                          (set-cons s a))]
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
                    `(,@acc (,S -> . ,es) . ,r))))
           (remove-epsilons S0 G '()))
         (remove-epsilons S0 (cdr G) (snoc (car G) acc)))]))



(define (CNF->CNF* G ans prevs Δ?)
  (match G
    ['() (if (CNF? ans) ans (error (format "not a CNF, but nothing to fix ~s" ans)))]
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
       (let ((G `((,S -> (,A . ,ss) . ,es) (,A -> ',a) . ,G)))
         (CNF->CNF* G ans prevs #t)))]
    [`((,S -> (,(? symbol? P) ,(? symbol? Q) . ,ss) . ,es) . ,G)
     (let ((R (gensym S)))
       (let ((G `((,S -> (,R . ,ss) . ,es) (,R -> (,P ,Q)) . ,G)))
         (CNF->CNF* G ans prevs #t)))]
    [`((,S -> (,(? symbol? P) ',a . ,ss) . ,es) . ,G)
     (let ((Q (gensym S))
           (R (gensym S)))
       (let ((G `((,S -> (,R . ,ss) . ,es) (,R -> (,P ,Q)) (,Q -> ',a) . ,G)))
         (CNF->CNF* G ans prevs #t)))]
    [else (error 'CFG->CNF (format "invalid rule: ~s" (car G)))]))

(define (CFG->CNF G)
  (if (null? G) '()
      (if (not (CFG? G))
          (error (format "Not a valid grammars: ~s" G))
          (let* ((S0 (caar G))
                 (new-S0 (gensym S0))
                 (G (remove-epsilons new-S0 `((,new-S0 -> ,S0) ,@G) '())))
            (consolidate-again (consolidate-CNF (CNF->CNF* G '() '() #f)))))))

(define (consolidate-again G)
  (let loop ((G (cdr G))
             (ans (list (car G))))
    (match G
      ['() ans]
      [`((,S -> . ,rules) . ,G)
       (if (not (member* S (append ans G)))
           (consolidate-again (append ans G))
           (loop G (snoc `(,S -> . ,rules) ans)))])))



(define (consolidate-CNF-help S es G)
  (let loop ((G G)
             (acc '()))
    (match G
      ['() #f]
      [`((,P -> . ,es2) . ,G)
       (if (and (not (eqv? P S)) (set-equal?? es es2))
           (replace* P S (append acc G))
           (loop G `(,@acc (,P -> . ,es2))))])))

(define (consolidate-CNF G)
  (let loop ((G G)
             (acc '()))
    (match G
      ['() acc]
      [`((,S -> . ,es) . ,G)
       (cond
         [(consolidate-CNF-help S es (append acc (cons `(,S -> . ,es) G)))
          => (λ (G) (loop G '()))]
         [else (loop G `(,@acc (,S -> . ,es)))])])))





;;;;;;;;;;;;;;
;; set operations on grammars (no negation)

(define (G-Union G1 G2)
  (let ((G2 (rename-xs (map car G2) (λ (x) (symbol-append x 'b)) G2))
        (S0 (gensym 'Start)))
    `((,S0 -> ,(caar G1) ,(caar G2))
      ,@G1
      ,@G2)))

(define (G-Concatenation G1 G2)
  (let ((G2 (rename-xs (map car G2) (λ (x) (symbol-append x 'b)) G2))
        (S0 (gensym 'Start)))
    `((,S0 -> (,(caar G1) ,(caar G2)))
      ,@G1
      ,@G2)))

;;;;; Helpers for intersection

(define ((lookup b) x)
  (match x
    [(? terminal?) x]
    [(? symbol?)
     (let ((v (cadr (assv x b))))
       (if v (cadr v) x))]
    [`(,S1 ,S2) `(,((lookup b) S1) ,((lookup b) S2))]))

(define (apply-book G b)
  (map (λ (x) (map (lookup b) x)) G))

#|
(define (find-usable-rules G book)
  (let ((new (filter
              (λ (x)
                (match x
                  [`(,S -> ,rules ...)
                   (andmap
                    (λ (x)
                      (match x
                        ['ε #t]
                        [`',a #t]
                        [`(,S1 ...)
                         (andmap
                          (λ (x)
                            (or (eqv? x S) (assv x book)))
                          S1)]
                        [else #f]))
                    rules)]))
              G)))
    (values (set-difference G new)
            new)))

(define (trim G book dead Σ)
  (foldr
   (λ (x a)
     (match x
       [`(,S -> ,rules ...)
        (let ((keepers
               (if (memv S dead) '()
                   (filter
                    (λ (x)
                      (match x
                        ['ε #t]
                        [`',a (memv a Σ)]
                        [`(,S1 ...)
                         (andmap (λ (x) (not (memv x dead))) S1)]
                        [else #f]))
                    rules))))
          (displayln "With the deadlist:")
          (displayln dead)
          (displayln "and book")
          (displayln book)
          (displayln "converted")
          (displayln rules)
          (displayln "into")
          (displayln keepers)
          (if (null? keepers) a `((,S -> . ,keepers) . ,a)))]))
   '()
   G))

(define (merge g1 g2 r b dead)
  (match g1
      ['() (values r b g2 dead)]
      [`((,S -> . ,r1) . ,g1)
       (let-values
           (((this-r this-b this-dead g2-leftovers)
             (let loop ((ls g2)
                        (r r)
                        (b b)
                        (g2 '())
                        (dead dead))
               (match ls
                 ['() (values r b g2 dead)]
                 [`((,S2 -> ,r2 ...) . ,ls)
                  (displayln "the two options are: ")
                  (displayln `(,S2 -> . ,r2))
                  (displayln "and")
                  (displayln `(,S -> . ,r1))
                  (if (set-equal?? r1 (replace* S S2 r2))
                      (begin (displayln "yes")(values (set-cons `(,S -> . ,r1) r)
                              (set-cons `(,S ,S) (set-cons `(,S2 ,S) b))
                              (append g2 ls) 
                              dead))
                      (begin (displayln "no")(loop ls r b (cons`(,S2 -> . ,r2) g2) dead)))]))))
         (merge g1 g2-leftovers this-r this-b this-dead))]))



(define (make-rules G1 G2 rules book dead Σ)
  (displayln "MAKE-RULES")
  (let-values
      (((G1 G1-ready) (find-usable-rules G1 book))
       ((G2 G2-ready) (find-usable-rules G2 book)))
    (let ((G1t (trim G1 book dead Σ))
          (G2t (trim G2 book dead Σ))
          (G1-ready (trim G1-ready book dead Σ))
          (G2-ready (trim G2-ready book dead Σ)))
      (if (and (null? G1-ready) (null? G2-ready))
          (begin
            (displayln "no more to do")
            (values '() '() rules book dead))
          (let-values
              (((r b dead g2-leftovers) (merge G1-ready G2-ready rules book dead)))
            (let ((G1-ready (trim G1-ready book dead Σ))
                  (G2-ready (trim G2-ready book dead Σ)))
              (values (apply-book G1t b)
                      (apply-book (append g2-leftovers G2t) b)
                      (apply-book r b)
                      b
                      dead)))))))


(define (G-Intersection G1 G2)
  (let* ((G1 (CFG->CNF (rename-xs (map car G1) (λ (x) (symbol-append x 'a)) G1)))
         (G2 (CFG->CNF (rename-xs (map car G1) (λ (x) (symbol-append x 'a)) G2)))
         (S1 (caar G1))
         (S2 (caar G2))
         (Σ (set-intersection (extract-Σ G1) (extract-Σ G2))))
    (let loop ((G1 G1)
               (G2 G2)
               (rules '())
               (book '())
               (dead '()))
      (cond
        [(and (null? G1) (null? G2))
         (CFG->CNF (rules->grammar rules book S1 S2))]
        [else (call-with-values
               (λ () (make-rules G1 G2 rules book dead Σ))
               loop)]))))
|#




(define ((known? Σ book dead) r)
  (match r
    [`(,S -> . ,r)
     (andmap
      (λ (x)
        (match x
          ['ε #t]
          [`',a (memv a Σ)]
          [`(,(? symbol? s) ...)
           (or (ormap (member-of dead) s)
               (andmap (λ (x) (assv x `((,S) . ,book))) s))]))
      r)]))

(define incorporate 'TODO)
(define (G-Intersection G1-init G2-init)
  (let ((G1 (CFG->CNF G1-init))
        (G2 (CFG->CNF G2-init)))
    (let ((Σ (set-intersection (extract-Σ G1) (extract-Σ G2))))
      (let intersection ((book '())
                         (dead '())
                         (G1 G1)
                         (G2 G2))
        (match G1
          ['()
           (let ((S1 ((lookup book) (caar G1-init))))
             `((,(gensym 'S) -> ,S1) . ,G2))]
          [else
           (let* ((known (filter (known? Σ book dead) G1))
                  (unknown (set-difference G1 known)))
             (let-values (((new-book new-dead G2) (incorporate G2 book dead known)))
               
             (intersection new-book new-dead unknown G2)))])))))




(define (rules->grammar r b s1 s2)
  (let ((S1 (if (assv s1 b) ((lookup b) s1) #f))
        (S2 (if (assv s2 b) ((lookup b) s2) #f)))
    (if (and S1 S2)
        (let* ((ln1 (assv S1 r))
               (ln2 (assv S2 r))
               (S (gensym 'S))
               (G (remove ln1 (remove ln2 r))))
          ;; we should only need the path to S1 (right?) but leaving both for now
          `((,S ->
                ,@(if ln1 (cddr ln1) '())
                ,@(if ln2 (cddr ln2) '())) . ,G))
        '())))


