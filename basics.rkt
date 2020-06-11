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
         apply-instruction)

;; Here are some types that we will refer to and intend what we hope are
;; intuitive definitions.

#|
Any -- anything
Bool -- #t | #f
Symbol -- Racket symbol
Nat -- natural number
Letter -- Symbol | Nat | Boolean
Stack-Instruction -- 'preserve-stack | `(pop on ,Letter push ,(list Letter))
Transition -- `(,Symbol ,Letter ,Symbol . ,(List Stack-Instruction))

Set -- list of anything with no duplicates
List -- true list

Acc -- (List Any)
Stack -- '(#f) | (cons Letter Stack)
Frontier -- (List State)
Transition-Function -- (List Transition)
Tmap -- HashMap{equal?, (List Symbol) x HashMap{equal?, (list Stack x Symbol}}
(Maybe Type) -- #f | Type

|#

;; Here's a structure definition. We can use it to define finite-state automata.


(struct Automaton
  [start-state         ;; S : Symbol
   final-states        ;; F : (List Symbol)
   all-states          ;; Q : (List Symbol)
   transition-function ;; δ : (list Transition)
   alphabet            ;; Σ : (List Symbol)
   stack-alphabets]    ;; Γ : (List Stack)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; a function query-automaton
;; that, when given higher-order parameters,
;; provides a search algorithm for nPDAs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Variable names

;; symbol-append : Symbol x Symbol -> Symbol
(define (symbol-append s1 s2)
  (string->symbol
   (string-append
    (symbol->string s1)
    (symbol->string s2))))

;; to ensure separate namespaces

;; rename-xs : (List Symbol) x (-> Symbol Symbol) x List -> List
(define (rename-xs xs ext ls)
  (cond
    [(member ls xs) (ext ls)]
    [(cons? ls)
     (cons (rename-xs xs ext (car ls))
           (rename-xs xs ext (cdr ls)))]
    [else ls]))

;; Lists

;; snoc : List x List -> List
(define (snoc x s) (foldr cons `(,x) s))

;; member-of : List -> Any -> Bool
(define (member-of s) (λ (x) (member x s)))

;; replace* : Any x Any x List -> List
(define (replace* old new x)
  (cond
    [(equal? x old) new]
    [(cons? x)
     (cons (replace* old new (car x))
           (replace* old new (cdr x)))]
    [else x]))

;; member* : Any x List -> Bool
(define (member* x l)
  (or (equal? x l)
      (and (cons? l)
           (or (member* x (car l))
               (member* x (cdr l))))))

;; powerset : List-> List
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

;; set-cons : Any x Set -> Set
(define (set-cons x s) (if (member x s) s (cons x s)))

;; set-union : Set x Set -> Set
(define (set-union s1 s2) (foldr set-cons s2 s1))

;; set-difference : Set x Set -> Set
(define (set-difference s1 s2) (foldr remove s1 s2))

;; set-intersection : Set x Set -> Set
(define (set-intersection s1 s2) (filter (member-of s2) s1))

;; set-equal?? : Set x Set -> Bool
(define (set-equal?? s1 s2)
  (and (andmap (λ (x) (member x s2)) s1)
       (andmap (λ (x) (member x s1)) s2)))

;; to-set : Set -> List
(define (to-set ls)
  (foldr set-cons '() ls))


;;;; Stacks

;; empty-stack : Stack
(define empty-stack '(#f))

;; stack-empty? : Stack -> Bool
(define stack-empty? (λ (x) (equal? x empty-stack)))


;; all-empty? : (List Stack) -> Bool
(define all-empty? (λ (ks) (andmap stack-empty? ks)))

;; empty-stacks : Nat -> (List Stack)
(define (empty-stacks k) (build-list k (λ (_) empty-stack)))

;; terminal : Any -> Bool
;; symbols allowed to part of Σ
(define (terminal? x)
  (and (not (eqv? x 'ε))
       (or (symbol? x)
           (member x '(0 1 2 3 4 5 6 7 8 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;
;; frontier-based search : 2FS two-frontier search
;;;;;;;;;;;;;;;;;;;;;;;;


;; enqueue : Frontier x Frontier -> Frontier
(define (enqueue new old) (append old new))
;; push : Frontier x Frontier -> Frontier
(define (push new old) (append new old))

;; id : Any -> Any
(define id (λ (x) x))

;; final-state? : (List Symbol) x Symbol -> Boolean
(define ((final-state? F) s) (and (memv s F) #t))

;;  make-condition : Instruction -> Value
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

;; δ->hash : (list Transition) -> (List (List Symbol))
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

;; apply-instruction : Stack x Stack-Instruction-> Stack
(define (apply-instruction k i)
  (match i
    ['preserve-stack k]
    [`(pop on #t push ,vs) (append vs k)]
    [`(pop on ,γ push ,vs) (append vs (cdr k))]))



;; get-δ :
;; TMap x Symbol x Letter x (List Stack)
;;  -> (List `(,Symbol . ,(List Stack-Instruction)))
(define (get-δ δ s i ks)
  (cond
     [(hash-ref δ `(,s ,i) (λ () #f)) =>
      (λ (v?)
        (cond
          [(hash-ref v? (map car ks) (λ () #f)) => id]
          [else '()]))]
     [else '()]))

;; apply-transitions :
;; (List (Symbol x Letter x Acc -> Acc)) x Symbol x TMap x (List Stack) x Acc
;;    -> Letter -> (List State)

(define ((apply-transitions U s δ ks acc) i)
  (foldr
   (λ (e a)
     (let ((new-stacks (map apply-instruction ks (cdr e)))
           (new-acc (if U (map (λ (u a) (u s i a)) U acc) acc)))
       (if (andmap id new-stacks)
           (cons `(,(car e) ,new-stacks ,new-acc) a)
           a)))
   '()
   (get-δ δ s i ks)))


;; visited : HashMap{State x Bool} -> State -> Boolean
(define (visited? V) (λ (x) (hash-has-key? V x)))


;; all-combinations : (List (List Symbol)) -> (List (List Symbol))
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

(define ((step Σ F? include? stop? f א U δ) Q A V)
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
    ((_ M I stop? A-stop? include? U b f א)
     (run M I stop? A-stop? include? U b f א #f))
    ((_ M I stop? A-stop? include? U b f א disp?)
     (match M
       [(Automaton S F A δ Σ Γ)
        (let* ((δ (δ->hash δ Γ))
               (F? (final-state? F))
               (V (make-hash))
               (proceed (step Σ F? include? stop? f א U δ)))
          (let loop ((Qsym `((,S ,(empty-stacks (length Γ)) ,I)))
                     (Qε '())
                     (A b))
            (begin
              (if disp?
                  (begin (displayln Qsym) (displayln "")  (displayln Qε))
                  void)
              
              (cond
                [(A-stop? A) A]
                [(null? Qsym)
                 (if (null? Qε) A
                     (let-values (((Qsymn Qεn Qε A) (proceed Qε A V)))
                       (loop Qsymn (enqueue Qεn Qε) A)))]
                [else
                 (let-values (((Qsymn Qεn Qsym A) (proceed Qsym A V)))
                    (loop (push Qsymn Qsym) (push Qεn Qε) A))]))))]))))
