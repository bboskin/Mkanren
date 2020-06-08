#lang racket

(provide Automaton
         Automaton-start-state
         Automaton-final-states
         Automaton-all-states
         Automaton-transition-function
         Automaton-alphabet
         Automaton-stack-alphabets
        
         terminal?
         run

         ;; basic basics
         id
         
         set-cons
         set-union
         set-difference
         set-intersection
         set-equal??
         to-set

         snoc
         member-of
         replace*
         member*
         powerset

         ;; variable name management
         symbol-append
         rename-xs


         ;; THE REST ARE FUNCTIONS TO hide again
         ;; stack function used in M-Intersection
         all-empty?
         check-stacks)



;; Here's a structure definition. We can use it to define finite-state automata.

(struct Automaton
  [start-state         ;; S
   final-states        ;; F
   all-states          ;; Q
   transition-function ;; δ
   alphabet            ;; Σ
   stack-alphabets]    ;; (a list of Γs, with one alphabet for each stack, so we can have as many stacks as we want without changing anything!)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; a function query-automaton
;; that, when given higher-order parameters,
;; provides a search algorithm for nPDAs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Variable names
(define (symbol-append s1 s2)
  (string->symbol
   (string-append
    (symbol->string s1)
    (symbol->string s2))))

;; to ensure separate namespaces

(define (rename-xs xs ext ls)
  (cond
    [(member ls xs) (ext ls)]
    [(cons? ls)
     (cons (rename-xs xs ext (car ls))
           (rename-xs xs ext (cdr ls)))]
    [else ls]))

;; Lists

(define (snoc x s) (foldr cons `(,x) s))
(define (member-of s) (λ (x) (member x s)))

(define (replace* old new x)
  (cond
    [(equal? x old) new]
    [(cons? x)
     (cons (replace* old new (car x))
           (replace* old new (cdr x)))]
    [else x]))

(define (member* x l)
  (or (equal? x l)
      (and (cons? l)
           (or (member* x (car l))
               (member* x (cdr l))))))

(define (powerset l)
  (foldr
   (λ (x P)
    (foldr
     (λ (l a) (append `((,x . ,l) ,l) a))
     '()
     P))
   '(())
   l))

;; Sets
(define (set-cons x s) (if (member x s) s (cons x s)))
(define (set-union s1 s2) (foldr set-cons s2 s1))
(define (set-difference s1 s2) (foldr remove s1 s2))
(define (set-intersection s1 s2) (filter (member-of s2) s1))
(define (set-equal?? s1 s2)
  (and (andmap (λ (x) (member x s2)) s1)
       (andmap (λ (x) (member x s1)) s2)))
(define (to-set ls)
  (foldr set-cons '() ls))


;; Stacks 
(define (stack-empty? k) (equal? k '(#f)))
(define (all-empty? ks) (andmap stack-empty? ks))


;; symbols allowed to part of Σ
(define (terminal? x)
  (and (not (eqv? x 'ε))
       (or (symbol? x)
           (member x '(0 1 2 3 4 5 6 7 8 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; frontier-based breadth-first search
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define id (λ (x) x))

(define ((final-state? F) s) (and (memv s F)))



;; new implementation of run
;; where δ is locally represented as nested hashtables


(define (make-condition instr)
  (match instr
    ['preserve-stack #t]
    [`(pop on #t push ,vs) #t]
    [`(pop on ,γ push ,vs) γ]))

(define ((subsumed-by c1) c2)
  (match* (c1 c2)
    [('() '()) #t]
    [(`(#t . ,d1) `(,a2 . ,d2)) ((subsumed-by d1) d2)]
    [(`(,a1 . ,d1) `(,a2 . ,d2))
     (and (eqv? a1 a2) ((subsumed-by d1) d2))]
    [(_ _) #f]))

(define (add-conditions PΓ S instrs h)
  (let ((conds (map make-condition instrs)))
    (let ((relevant (filter (subsumed-by conds) (if (null? PΓ) '(()) PΓ))))
      (begin
        (map (λ (conds)
               (let ((v? (hash-ref h conds (λ () #f))))
                 (if v?
                     (hash-set! h conds (cons `(,S . ,instrs) v?))
                     (hash-set! h conds `((,S . ,instrs))))))
             relevant)
        h))))

(define (δ->hash δ Γ)
  (let ((PΓ (all-combinations (map (λ (x) (cons #f x)) Γ))))
    (foldr
     (λ (x a)
       (match x
         [`(,S1 ,v, S2 . ,instrs)
          (let ((v? (hash-ref a `(,S1 ,v) (λ () #f))))
            (begin
              (if v?
                  (hash-set! a `(,S1 ,v)
                             (add-conditions PΓ S2 instrs v?))
                  (hash-set! a `(,S1 ,v)
                             (add-conditions
                              PΓ S2 instrs
                              (make-hash (map list PΓ)))))
              a))]))
     (make-hash)
     δ)))

(define (check-stacks ks ms)
  (match* (ks ms)
    [('() _) #f]
    [(`(,s . ,ks) `(pop on #t push ,vs))
     (append vs (cons s ks))]
    [(`(,s . ,ks) `(pop on ,γ push ,vs))
     (and (eqv? s γ) (append vs ks))]
    [(`(,s . ,ks) 'preserve-stack)
     (cons s ks)]))

(define ((apply-transitions U s δ ks acc) i)
  (let ((δ (let ((v? (hash-ref δ `(,s ,i) (λ () #f))))
             (if v?
                 (let ((v? (hash-ref v? (map car ks) (λ () #f))))
                   (if v? v? '()))
                 '()))))
    (foldr
     (λ (e a)
       (let ((new-stacks (map check-stacks ks (cdr e)))
             (new-acc (if U (map (λ (u a) (u s i a)) U acc) acc)))
         (cons `(,(car e) ,new-stacks ,new-acc) a)))
     '()
     δ)))


(define (visited? V) (λ (x) (hash-has-key? V x)))


(define (all-combinations ls)
  (cond
    [(null? ls) '()]
    [(null? (cdr ls)) (map list (car ls))]
    [else
     (let ((V (all-combinations (cdr ls))))
       (foldr
        (λ (e a)
          (append (map (λ (x) (cons e x)) V) a))
        '()
        (car ls)))]))


;; Visited is a hashset as well, and is now global within the loop
;; SORRY FOR SIDE-EFFECTS BUTS ITS SO MUCH FASTER
;; Now using separate queue for states derived from epsilons and other symbols


;; initializing/updating the frontier
(define (F0 S Γ I) `((,S ,(build-list (length Γ) (λ (_) '(#f))) ,I)))

(define (Fk A search)
  (λ (old L δ ε)
    (match search
      ['dfs (append (foldr append '() (map δ L)) ε old)]
      ['bfs (append old ε (foldr append '() (map δ L)))]
      ['shuff (append old (shuffle (append ε (foldr append '() (map δ L)))))])))

(define ((step Σ F? include? stop? f update-Q א U δ) Q A V)
  (match Q
    ['() (values '() '() '() A)]
    [`((,s ,ks ,(? stop?)) . ,Q) (values '() '() Q A)]
    [`(,(? (visited? V)) . ,Q) (values '() '() Q A)]
    [`((,s ,ks ,a) . ,Q)
     (begin
       (hash-set! V `(,s ,ks ,a) #t)
       (let ((A (if (and (F? s) (all-empty? ks) (include? a)) (f a A) A))
             (Q1n (foldr append '() (map (apply-transitions U s δ ks a) (א Σ a))))
             (Q2n ((apply-transitions #f s δ ks a) 'ε)))
         (values Q1n Q2n Q A)))]))

(define-syntax run
  (syntax-rules ()
    ((_ M I stop? A-stop? include? U b f א Π disp?)
     (match M
       [(Automaton S F A δ Σ Γ)
        (let* ((δ (δ->hash δ Γ))
               (update-Q (Fk A Π))
               (F? (final-state? F))
               (V (make-hash))
               (proceed (step Σ F? include? stop? f update-Q א U δ)))
          (let loop ((Q1 (F0 S Γ I))
                     (Q2 '())
                     (A b))
            (begin
              (if disp? (begin (displayln Q1) (displayln "")(displayln Q2)) void)
              
              (cond
                [(A-stop? A) A]
                [(and (null? Q1) (null? Q2)) A]
                [(null? Q1)
                 ;; epsilons are DFS
                 (let-values (((Q1n Q2n Q2 A) (proceed Q2 A V)))
                    (loop Q1n (append Q2 Q2n) A))]
                [else
                 ;; but symbols are BFS!
                 (let-values (((Q1n Q2n Q1 A) (proceed Q1 A V)))
                    (loop (append Q1 Q1n) (append Q2n Q2) A))]))))]))
    ((_ M I stop? A-stop? include? U b f א)
     (run M I stop? A-stop? include? U b f א 'bfs #f))
    ((_ M I stop? A-stop? include? U b f א disp?)
     (run M I stop? A-stop? include? U b f א 'bfs disp?))))
