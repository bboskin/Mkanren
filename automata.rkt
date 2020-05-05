#lang racket

(provide Automaton

         Automaton-start-state
         Automaton-final-states
         Automaton-all-states
         Automaton-transition-function
         Automaton-alphabet
         Automaton-stack-alphabets
         
         find-words
         accept?
         find-words-only

         find-words/display
         accept?/display
         find-words-only/display


         terminal?)

;; Here's a structure definition. We can use it to define finite-state automata.

(struct Automaton
  [start-state         ;; S
   final-states         ;; F
   all-states          ;; Q
   transition-function ;; δ
   alphabet            ;; Σ
   stack-alphabets]    ;; (a list of Γs, with one alphabet for each stack)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; a function query-automaton
;; that, when given higher-order parameters,
;; provides a search algorithm for nPDAs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; Sets
(define (set-cons x s)
  (if (member x s) s (cons x s)))
(define (set-union s1 s2) (foldr set-cons s2 s1))

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

(define (Fk A δ U search)
  (λ (old L δ ε)
    (match search
      ['dfs (append (foldr set-union '() (map δ L)) ε old)]
      ['bfs (append old ε (foldr set-union '() (map δ L)))])))



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
  (syntax-rules (display)
    ((_ M I stop? go? U b f א Π disp?)
     (match M
       [(Automaton S F A δ Σ Γ)
        (let ((T (F0 S Γ I))
              (update-T (Fk A δ U Π))
              (F? (final-state? F)))
          (let loop ((T T)
                     (V '()))
            (begin
              (if disp? (displayln T) void)
              (match T
                ['() b]
                [`((,s ,ks ,(? stop?)) . ,rest) (loop rest V)]
                [`((,s ,ks ,a) . ,rest)
                 (if (member `(,s ,ks ,a) V)
                     (loop rest V)
                     (let ((rec (λ ()
                                  (loop (update-T
                                         rest
                                         (א Σ a)
                                         (apply-transitions U δ s ks a)
                                         (update-epsilons s δ ks a))
                                        (cons `(,s ,ks ,a) V)))))
                       (if (and (F? s) (all-empty? ks) (go? a))
                           (f a rec)
                           (rec))))]))))]))
((_ M I stop? go? U b f א)
     (run M I stop? go? U b f א 'bfs #f))
    ((_ M I stop? go? U b f א display)
     (run M I stop? go? U b f א 'bfs #t))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; the standard query to check if a machine M accepts a word w
(define (accept? M w)
  (run
   M
   `(,w)
   (λ (_) #f)
   (λ (a) (null? (car a)))
   (list
    (λ (_1 _2 acc) (cdr acc)))
   #f
   (λ (_1 _2) #t)
   (λ (_ a) (if (null? (car a)) '() (list (caar a))))))

(define (accept?/display M w)
  (run
   M
   `(,w)
   (λ (_) #f)
   (λ (a) (null? (car a)))
   (list
    (λ (_1 _2 acc) (cdr acc)))
   #f
   (λ (_1 _2) #t)
   (λ (_ a) (if (null? (car a)) '() (list (caar a))))
   display))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; a query to get all members of a machine M's language with length up to (or equal to) k
(define (find-words M k)
  (run
   M
   '(())
   (λ (a) (> (length (car a)) k))
   (λ (a) #t)
   (list (λ (_ i a) (cons i a)))
   '()
   (λ (a ans) (let ((w (reverse (car a)))
                    (ans (ans)))
                (if (member w ans)
                    ans
                    (cons w ans))))
   (λ (Σ _) Σ)))

(define (find-words/display M k)
  (run
   M
   '(())
   (λ (a) (> (length (car a)) k))
   (λ (a) #t)
   (list (λ (_ i a) (cons i a)))
   '()
   (λ (a ans) (let ((w (reverse (car a)))
                    (ans (ans)))
                (if (member w ans)
                    ans
                    (cons w ans))))
   (λ (Σ _) Σ)
   display))

(define (find-words-only M k)
  (filter (λ (x) (= (length x) k))
          (find-words M k)))

(define (find-words-only/display M k)
  (filter (λ (x) (= (length x) k))
          (find-words/display M k)))


