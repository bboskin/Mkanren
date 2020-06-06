#lang racket

(require "grammars.rkt"
         "automata.rkt"
         "basics.rkt"
         "queries.rkt"
         "G-to-M.rkt"
         "draw-automata.rkt"
         2htdp/universe)

(provide (all-defined-out))
;;;; stuff to do with number processing

#|
RE -> 'a
     RE U RE
     RE • RE
     (RE)*
     (RE)+
|#


(define even?/RE '(O U ((I • ((O U I) *)) • O)))
(define odd?/RE '((I • ((O U I) *)) • I))

;(define number?/DFA (RE->DFA number?/RE))
(define even?/DFA (RE->DFA even?/RE))
(define odd?/DFA (RE->DFA odd?/RE))

;; stuff to do with boolean logic

#|
;; keeping track of minimization progress

;; PRE any minimization efforts
> (length (Automaton-all-states Val-of))
182
> (length (Automaton-transition-function Val-of))
381
>

;; AFTER CNF minimization efforts
> (length (Automaton-all-states Val-of))
70
> (length (Automaton-transition-function Val-of))
262

;; AFTER PDA minimization efforts
> (length (Automaton-all-states (minimize-PDA Val-of)))
43
(length (Automaton-transition-function (minimize-PDA Val-of)))
262
|#





(define val-of
  '((True ->
          't
          ('not False)
          ('andbegin True* 'andend)
          ('orbegin Value* True Value* 'orend))
    
    (True* -> ε (True True*))

    (False ->
           'f
           ('not True)
           ('andbegin Value* False Value* 'andend)
           ('orbegin False* 'orend))
    (False* -> ε (False False*))
    (Value -> True False)
    (Value* -> ε (Value Value*))))

(define Val-of (CNF->PDA (CFG->CNF val-of)))
(define Val-of/min (minimize-PDA Val-of))



(define Eng
  '((P -> (Subject VerbPhrase))
    (Subject -> (Adjective* ProperNoun) (Article Adjective* Noun))
    (Adjective* -> ε (Adjective Adjective*))
    (Adjective -> 'big 'small 'beautiful 'sad 'melancholy 'green)
    (ProperNoun -> 'Ben 'Benzo 'Google 'God)
    (Noun -> 'love 'movie 'graph 'city)
    (VerbPhrase -> Verb (Adverb Verb) (Verb Article Noun))
    (Adverb -> 'fastly 'wonderfully 'greasily)
    (Verb -> 'is 'knows 'bakes)
    (Article -> 'the)))

(define Eng/PDA (CNF->PDA (CFG->CNF Eng)))
(define Eng/min (minimize-PDA (CNF->PDA (CFG->CNF Eng))))


;; LOL this is just palindrome!  I need to implement turing machines
;; for this (at least linearly bounded)
(define Double
  (Automaton
   'S
   '(S)
   '(S)
   '(;; counting the first half
     (S a S (pop on #t push (a)))
     (S b S (pop on #t push (b)))
     (S c S (pop on #t push (c)))
     ;; popping the 2nd half
     (S a S (pop on a push ()))
     (S b S (pop on b push ()))
     (S c S (pop on c push ()))
     )
   '(a b c)
   '((a b c))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shit relating to Jack's paper

#|
Relevant datatypes as we progress through our function.

CDR: A list of the form `(CDR (,Eid . ,Value) ...)


CDRTree: A nested list of the form
      '()                    null
    |  `(,CDR ...)           CDRs
    | `((,Eid) . ,CDRTree)   idTree
    | `((,Value) . ,CDRTree) valTreeT
    | `(,CDRTree ...)        TListT



ValTree: A nested list of the form
      Value                
    | `(,Value ...)       Values
    | `((,Eid) . ,ValTree)   idTreeV
    | `((,Value) . ,ValTree) valTreeV
    | `(,Tree ...)        TListV


Value: A number, symbol, or `(,Value ...)

Eid: symbol describing a field of CDR

|#


;; taking known words into helper functions
;; (this function defines the known helpers)

(define FN-TAGS
  `(;; filter ops
    (zero-minutes? ,(λ (x) (eqv? (cdr (assv 'dur (cdr x))) 0)))
    (voicemail? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x)))
                              (cdr (assv 'recipient-id (cdr x))))))
    (half-hour? ,(λ (x) (>= (cdr (assv 'dur (cdr x))) 30)))
    (jack? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x))) 'Jack)))
    (ben? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x))) 'Ben)))
    (Michigan? (λ (x) (memv (cdr (assv 'loc (cdr x)))
                            `(Ann-Arbor Detroit DairyTown KerryTown))) )
    
    ;; reduce ops
    (+ ,(λ (x) (foldr + 0 x)))
    (* ,(λ (x) (foldr * 1 x)))
    (mean ,(λ (xs) (/ (foldr + 0 xs) (length xs))) 0)
    (length ,length 0)
    (set ,(λ (x) (foldr set-cons '() x)) ())))

(define FILTER-OPS
  '(zero-minutes?
    voicemail?
    half-hour?
    ;jack?
    ;ben?
    ;Michigan?
    ))
(define REDUCE-OPS
  '(length set))

(define (tag->function t)
  (let ((f (assv t FN-TAGS)))
    (if f (cadr f) #f)))


;; making random data
(define CALLERS
  '(Ben Jack Brian Aaron
        Ellington Matt Cole Shane
        Tessa Terra
        Trudi Doly Karen Sonya
        CBreeze JJ))

(define LOCS
  '(Albany Oakland El-Cerrito San-Francisco Los-Angeles Forestville
           Detroit Ann-Arbor KerryTown DairyTown
           Boston Allston Cambridge Somerville))

(define (random-date)
  (cons (add1 (random 12))
        (add1 (random 29))))

(define (random-time)
  (cons (add1 (random 12))
        (add1 (random 60))))

(define DUR-MAX 10)


(define (random-CDR _)
  `(CDR
    (caller-id . ,(list-ref CALLERS (random (length CALLERS))))
    (recipient-id . ,(list-ref CALLERS (random (length CALLERS))))
    (date . ,(random-date))
    (time . ,(random-time))
    (dur . ,(random  DUR-MAX))
    (loc . ,(list-ref LOCS (random (length LOCS))))))


(define FIELDS
  (map car (cdr (random-CDR #f))))
(define field? (λ (x) (memv x FIELDS)))
(define (random-CDRs k)
  (build-list k random-CDR))


(define Eid? (member-of FIELDS))

(define Value?
  (λ (x)
    (or (number? x)
        (symbol? x)
        (null? x)
        (and (cons? x)
             (not (cons? (car x)))
             (not (Label? (car x)))
             (not (cons? (cdr x)))))))

(struct Label [v]
  #:transparent)

(define CDR?
  (λ (x)
    (and (cons? x)
         (eqv? (car x) 'CDR)
         (andmap cons? (cdr x)))))

(define CDRs (random-CDRs 20))

(define Feature
  (CNF->PDA
   (CFG->CNF
    `((Feature -> (Filter* G Reduce+))
      (Filter* -> ε ('filter FilterOp Filter*))
      (Reduce+ -> ('reduce ReduceOp) ('reduce ReduceOp Reduce+))
      (G -> ('select Eid) ('map Eid G 'reduce ReduceOp))
      (FilterOp -> . ,(map (λ (x) `',x) FILTER-OPS))
      (ReduceOp -> . ,(map (λ (x) `',x) REDUCE-OPS))
      (Eid -> . ,(map (λ (x) `',x) FIELDS))))))

;; Filter is just filter, but it takes a tag instead of a λ

;; Because of what we know about where it sits in the grammar,
;; Filter : Eid x CDRs -> CDRs
(define (Filter f t)
  (let ((f (tag->function f)))
    (filter f t)))


;; Map : CDRTree -> CDRTree

(define (add-to-group v a l)
  (match l
    ['() `((,(Label v) ,a))]
    [`((,(Label v2) . ,es) . ,l)
     (cond
       [(eqv? v v2) `((,(Label v) ,a . ,es) . ,l)]
       [else `((,(Label v2) . ,es) . ,(add-to-group v a l))])]))

(define (group-by eid o)
  (match o
    ['() `()]
    [`(,a . ,o)
     (add-to-group (cdr (assv eid (cdr a))) a (group-by eid o))]))

(define ((Map eid) o)
  (match o
    ['() '()]
    [`(,(? CDR? cdrs) ...)
     `(,(Label eid) . ,(group-by eid cdrs))]
    [`(,(? Label? e) . ,T)
     `(,e . ,((Map eid) T))]
    [`(,T ...) (map (Map eid) T)]))

;; Select : CDRTree -> ValTree
(define ((Select eid) o)
  (match o
    ['() '()]
    [`(,(? CDR? cdrs) ...)
     (map (λ (c) (cdr (assv eid (cdr c)))) cdrs)]
    [`(,(? Label? e) . ,T) `(,e . ,((Select eid) T))]
    [`(,T ...) (map (Select eid) T)]))



;; Reduce : ValTree -> ValTree
(define ((Reduce f) o)
  (match o
    ['() '()]
    [(? Value? v) (f `(,v))]
    [`(,(? Value? v) ...) (f v)]
    
    [`(,(? Label? e) ,(? Label? e2) ,(? Value? v) ...) (f v)]
    [`(,(? Label? e) ,(? Value? v) ...) (f v)]
    [`(,(? Label? e) . ,(? Value? v)) (f `(,v))]
    [`(,(? Label? e) . ,T) `(,e . ,((Reduce f) T))]
    
    [`(,T ...) (map (Reduce f) T)])) 



(define (apply-word w ls)
  (match w
    ['() ls]
    [`(filter ,t ,w ...)  (apply-word w (Filter t ls))]
    [`(map ,t ,w ...)    (apply-word w ((Map t) ls))]
    [`(select ,t ,w ...) (apply-word w ((Select t) ls))]
    [`(reduce ,f ,w ...)  (let ((f (tag->function f)))
                            (apply-word w ((Reduce f) ls)))]
    [else                 (error "Invalid word")]))


(define (apply-words ws)
  (map (λ (x) (apply-word x CDRs))
       ws))

;;;;;;
(require 2htdp/image)
(require 2htdp/universe)

(define SQUARE-SIZE 10)
(define (draw-value v)
  (cond
    [(number? v) (square SQUARE-SIZE "solid" "yellow")]
    [(symbol? v) (square SQUARE-SIZE "solid" "red")]
    [else (square SQUARE-SIZE "solid" "blue")]))

(define (draw-label _)
  (square SQUARE-SIZE "solid" "brown"))

(define (draw-CDR v)
  (square SQUARE-SIZE "solid" "black"))

(define (draw-tree T)
  (match T
    ['() empty-image]
    [(? Value? v) (draw-value v)]
    [`(,(? Value? v) ...)
     (foldr (λ (x a)
              (beside (draw-value x) a))
            empty-image
            T)]
    [`(,(? CDR? c) ...)
     (foldr (λ (x a)
              (beside (draw-CDR x) a))
            empty-image
            T)]
    [`(,(? Label? e) . ,T)
     (above (draw-label e)
            (draw-tree T))]
    
    [`(,T ...) (foldr (λ (x a)
                        (beside (draw-tree x) a))
                      empty-image
                      T)]))

(define (step W)
  (match W
    [`(,ls ()) (list ls '())]
    [`(,ls (filter ,t ,w ...))
     (list (Filter t ls) w)]
    [`(,ls (map ,t ,w ...))
     (list ((Map t) ls) w)]
    [`(,ls (select ,t ,w ...))
     (list ((Select t) ls) w)]
    [`(,ls (reduce ,f ,w ...))
     (let ((f (tag->function f)))
       (list ((Reduce f) ls) w))]
    [else (error "Invalid word")]))

(define (animate-eval w)
  (big-bang `(,CDRs ,w)
    [on-tick step 1]
    [to-draw (λ (x)
               (overlay (draw-tree (car x))
                        (empty-scene 500 500)))]))


