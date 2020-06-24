#lang racket

(require "basics.rkt")

(provide RE? CFG? CNF?
         RE->CFG CFG->CNF
         set-equal??
         G-Union
         G-Concatenation)

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
     (and (andmap production-rule? es)
          (CFG? G))]))

(define (CNF? G)
  (let ((S0 (caar G)))
    (let loop ((G G))
      (match G
        ['() #t]
        [`((,S -> ,es ...) . ,r)
         (and (andmap (CNF-production-rule? (eqv? S S0)) es)
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
          (error (format "Not a valid grammar: ~s" G))
          (let* ((S0 (caar G))
                 (new-S0 (gensym S0))
                 (G (map (λ (x) (match x
                                  [`(,S -> ,es ...)
                                   `(,S -> . ,(map (λ (x) (if (list? x)
                                                              (remove 'ε x)
                                                              x))
                                                   es))]))
                         G))
                 (G (remove-epsilons new-S0 `((,new-S0 -> ,S0) ,@G) '())))
            (organize-rules (consolidate-again (consolidate-CNF (CNF->CNF* G '() '() #f))))))))

(define (organize-rules G)
  (map
   (λ (x)
     (match x
       [`(,Sym -> . ,xs)
        (let ((S (filter (λ (x) (match x [`',x #t] [else #f])) xs))
              (R (filter (λ (x) (match x [`',x #f] [else #t])) xs)))
          `(,Sym -> . ,(append S R)))]))
   G))

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
;; set operations on grammars (no negation or intersection yet)

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

