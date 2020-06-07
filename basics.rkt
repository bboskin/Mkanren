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
(define (check-stacks ks ms)
  (match* (ks ms)
    [('() _) #f]
    [(`(,s . ,ks) `(pop on #t push ,vs))
     (append vs (cons s ks))]
    [(`(,s . ,ks) `(pop on ,γ push ,vs))
     (and (eqv? s γ) (append vs ks))]
    [(`(,s . ,ks) 'preserve-stack)
     (cons s ks)]))


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


;; initializing/updating the frontier
(define (F0 S Γ I) `((,S ,(build-list (length Γ) (λ (_) '(#f))) ,I)))

(define (Fk A search)
  (λ (old L δ ε)
    (match search
      ['dfs (append (foldr append '() (map δ L)) ε old)]
      ['bfs (append old ε (foldr append '() (map δ L)))]
      ['shuff (append old (shuffle (append ε (foldr append '() (map δ L)))))])))


#|
(define (update-epsilons s δ ks acc)
  (foldr
   (λ (t a)
     (match t
       [`(,s1 ε ,s2 . ,stack-conds)
        (if (and (eqv? s s1))
            (let ((new-stacks (map check-stacks ks stack-conds)))
              (if (andmap id new-stacks)
                  (cons `(,s2 ,new-stacks ,acc) a)
                  a))
            a)]
       [else a]))
   '()
   δ))

(define ((apply-transitions U δ s ks acc) i)
  (foldr
   (λ (t a)
     (match t
       [`(,s1 ε ,s2 . ,stack-conds) a]
       [`(,s1 ,(? terminal? v) ,s2 . ,stack-conds)
        (if (and (eqv? s s1) (eqv? i v))
            (let ((new-stacks (map check-stacks ks stack-conds))
                  (new-accs (map (λ (u a) (u s i a)) U acc)))
              (if (andmap id new-stacks)
                  `((,s2 ,new-stacks ,new-accs) . ,a)
                  a))
            a)]
       ;; users can define transitions using more general conditions
       ;; if they so desire. Automatically generated machines don't use this.
       [`(,s1 ,(? procedure? cond) ,s2 . ,stack-conds)
        (if (and (eqv? s s1) (cond i))
            (let ((new-stacks (map check-stacks ks stack-conds))
                  (new-accs (map (λ (u a) (u s i a)) U acc)))
              (if (andmap id new-stacks)
                  `((,s2 ,new-stacks ,new-accs) . ,a)
                  a))
            a)]))
   '()
   δ))


(define-syntax run
  (syntax-rules ()
    ((_ M I stop? A-stop? include? U b f א Π disp?)
     (match M
       [(Automaton S F A δ Σ Γ)
        (let ((update-Q (Fk A Π))
              (F? (final-state? F)))
          (let loop ((Q (F0 S Γ I)) (V '()) (A b))
            (begin
              (if disp? (displayln Q) void)
              (match Q
                ['() A]
                [(? (λ (x) (A-stop? A))) A]
                [`(,(? (member-of V)) . ,rest) (loop rest V A)]
                [`((,s ,ks ,(? stop?)) . ,rest) (loop rest V A)]
                [`((,s ,ks ,a) . ,Q)
                 (let ((V `((,s ,ks ,a) . ,V))
                       (A (if (and (F? s) (all-empty? ks) (include? a)) (f a A) A))
                       (Q (update-Q
                           Q
                           (א Σ a)
                           (apply-transitions U δ s ks a)
                           (update-epsilons s δ ks a))))
                   (loop Q V A))]))))]))
    ((_ M I stop? A-stop? include? U b f א)
     (run M I stop? A-stop? include? U b f א 'bfs #f))
    ((_ M I stop? A-stop? include? U b f א disp?)
     (run M I stop? A-stop? include? U b f א 'bfs disp?))))
|#




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

(define (δ->hash δ PΓ)
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
   δ))

(define (update-epsilons s δ ks acc)
  (let ((δ (let ((v? (hash-ref δ `(,s ε) (λ () #f))))
             (if v? (hash-ref v? (map car ks) (λ () #f)) '()))))
    (foldr
     (λ (e a)
       (match e
         [`(,s2 . ,stack-conds)
          (let ((new-stacks (map check-stacks ks stack-conds)))
                (cons `(,s2 ,new-stacks ,acc) a))]))
     '()
     (if δ δ '()))))

(define ((apply-transitions U δ s ks acc) i)
  (let ((δ (let ((v? (hash-ref δ `(,s ,i) (λ () #f))))
             (if v? (hash-ref v? (map car ks) (λ () #f)) '()))))
    (foldr
     (λ (x l)
       (match x
         [`(,s2 . ,stack-conds)
          (let ((new-stacks (map check-stacks ks stack-conds)))
            (let ((new-accs (map (λ (u a) (u s i a)) U acc)))
              (cons `(,s2 ,new-stacks ,new-accs) l)))]))
     '()
     (if δ δ '()))))


(define (visited? V)
  (λ (x) (hash-has-key? V x)))


(define (all-combinations ls)
  (cond
    [(null? ls) '()]
    [(null? (cdr ls)) (map list (car ls))]
    [else (let ((V (all-combinations (cdr ls))))
            (foldr
             (λ (e a)
               (append
                (map (λ (x) (cons e x)) V)
                a))
             '()
             (car ls)))]))
;; Visited is a hashset as well, and is now global withing the loop
;; SORRY FOR SIDE-EFFECTS BUTS ITS SO MUCH FASTER
(define-syntax run
  (syntax-rules ()
    ((_ M I stop? A-stop? include? U b f א Π disp?)
     (match M
       [(Automaton S F A δ Σ Γ)
        (let ((δ (δ->hash δ (all-combinations
                             (map (λ (x) (cons #f x)) Γ))))
              (update-Q (Fk A Π))
              (F? (final-state? F))
              (V (make-hash)))
          (let loop ((Q (F0 S Γ I)) (A b))
            (begin
              (if disp? (displayln Q) void)
              (match Q
                ['() A]
                [(? (λ (x) (A-stop? A))) A]
                [`(,(? (visited? V)) . ,rest) (loop rest A)]
                [`((,s ,ks ,(? stop?)) . ,rest) (loop rest A)]
                [`((,s ,ks ,a) . ,Q)
                 (begin
                   (hash-set! V `(,s ,ks ,a) #t)
                   (let ((A (if (and (F? s) (all-empty? ks) (include? a)) (f a A) A))
                         (Q (update-Q
                             Q
                             (א Σ a)
                             (apply-transitions U δ s ks a)
                             (update-epsilons s δ ks a))))
                     (loop Q A)))]))))]))
    ((_ M I stop? A-stop? include? U b f א)
     (run M I stop? A-stop? include? U b f א 'bfs #f))
    ((_ M I stop? A-stop? include? U b f א disp?)
     (run M I stop? A-stop? include? U b f א 'bfs disp?))))
