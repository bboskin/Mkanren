#lang racket

(require
  "basics.rkt"
  "queries.rkt"
  "G-to-M.rkt"
  "grammars.rkt")


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

;; data/functions to work up to defining
;; the automaton, which generates features

(define FILTER-FNS
  `((zero-minutes? ,(λ (x) (eqv? (cdr (assv 'dur (cdr x))) 0)))
    (voicemail? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x)))
                              (cdr (assv 'recipient-id (cdr x))))))
    (half-hour? ,(λ (x) (>= (cdr (assv 'dur (cdr x))) 30)))
    (jack? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x))) 'Jack)))
    (ben? ,(λ (x) (eqv? (cdr (assv 'caller-id (cdr x))) 'Ben)))
    (Michigan? ,(λ (x) (memv (cdr (assv 'loc (cdr x)))
                            `(Ann-Arbor Detroit DairyTown KerryTown))) )))

(define REDUCE-FNS
  `((+ ,(λ (x) (foldr + 0 x)) Nats Nat)
    (* ,(λ (x) (foldr * 1 x)) Nats Nat)
    (mean ,(λ (xs) (if (null? xs) 0 (/ (foldr + 0 xs) (length xs))))
          Nats Nat)
    (length ,length Set Nat)
    (set ,(λ (x) (foldr set-cons '() x)) Set Set)))

(define FNS (append FILTER-FNS REDUCE-FNS))

(define FILTER-OPS (map car FILTER-FNS))

(define REDUCE-NATS->NAT-OPS
  (map car
       (filter (λ (x) (equal? (cddr x) `(Nats Nat))) REDUCE-FNS)))
(define REDUCE-SET->NAT-OPS
  (map car
       (filter (λ (x) (equal? (cddr x) `(Set Nat))) REDUCE-FNS)))
(define REDUCE-SET->SET-OPS
  (map car
       (filter (λ (x) (equal? (cddr x) `(Set Set))) REDUCE-FNS)))

(define (tag->function t)
  (let ((f (assv t FNS)))
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

(define DUR-MAX 45)


(define (random-CDR _)
  `(CDR
    (caller-id . ,(list-ref CALLERS (random (length CALLERS))))
    (recipient-id . ,(list-ref CALLERS (random (length CALLERS))))
    (date . ,(random-date))
    (time . ,(random-time))
    (dur . ,(+ 15 (random  DUR-MAX)))
    (loc . ,(list-ref LOCS (random (length LOCS))))))


(define FIELDS (map car (cdr (random-CDR #f))))
(define NATFIELDS '(dur))

(define field? (λ (x) (memv x FIELDS)))
(define (random-CDRs k)
  (build-list k random-CDR))


(define Eid? (member-of FIELDS))

(define pr?
  (λ (x)
    (and (cons? x)
         (number? (car x))
         (number? (cdr x)))))
(define Value?
  (λ (x)
    (and (not (Label? x))
         (or (number? x)
             (symbol? x)
             (pr? x)
             (and (list? x)
                  (or (andmap number? x)
                      (andmap symbol? x)
                      (andmap pr? x)))))))

(struct Label [v] #:transparent)

(define CDR?
  (λ (x)
    (and (cons? x)
         (eqv? (car x) 'CDR)
         (andmap cons? (cdr x)))))

(define CDRs (random-CDRs 50))



(define Feature
  (CNF->PDA
   (CFG->CNF
    `((Feature ->
               (Filter* GNats ReduceNats->Nat)
               (Filter* GSet ReduceSet->Nat))
      (Filter* -> ε (Filter Filter*))
      (GNats -> SelectNats
             (Map GNats ReduceNats->Nat)
             (Map GSet ReduceSet->Nat))
      (GSet -> Select
            (Map GSet ReduceSet->Set)
            (Map GNats ReduceSet->Set))
      (SelectNats -> . ,(map (λ (x) `',(symbol-append 'select x)) NATFIELDS))
      (Select -> . ,(map (λ (x) `',(symbol-append 'select x)) FIELDS))
      (Map -> . ,(map (λ (x) `',(symbol-append 'map x)) FIELDS))
      (Filter -> . ,(map (λ (x) `',(symbol-append 'filter x)) FILTER-OPS))
      (ReduceNats->Nat -> . ,(map (λ (x) `',(symbol-append 'reduce x)) REDUCE-NATS->NAT-OPS))
      (ReduceSet->Nat -> . ,(map (λ (x) `',(symbol-append 'reduce x)) REDUCE-SET->NAT-OPS))
      (ReduceSet->Set -> . ,(map (λ (x) `',(symbol-append 'reduce x)) REDUCE-SET->SET-OPS))))))


#|
Documentation on speed development

Before Σ reduction
> (time (take-words Feature 100))
cpu time: 192744 real time: 192304 gc time: 12664

After Σ reduction:
> (time (take-words Feature 100))
cpu time: 56639 real time: 53815 gc time: 8676

After converting δ and V to hashmaps for run
> (time (take-words Feature 100))
cpu time: 18519 real time: 20098 gc time: 7418
> (time (length (apply-words (take-words Feature 500))))
cpu time: 40639 real time: 42321 gc time: 16601
500

After adding stack conditions to hashmap
> (time (length (apply-words (take-words Feature 100))))
cpu time: 15848 real time: 16470 gc time: 6077
100
> (time (length (apply-words (take-words Feature 500))))
cpu time: 31778 real time: 33655 gc time: 12394
500
> (time (random-word Feature 4))
cpu time: 22263 real time: 23945 gc time: 7826
'(filterMichigan? filtervoicemail? selectdur reducemean)
> (time (random-word Feature 4))
cpu time: 11421 real time: 14591 gc time: 5576
'(maprecipient-id selectcaller-id reduceset reducelength)
> (time (take-words Feature 750))
cpu time: 4603030 real time: 4528962 gc time: 3597575

After splitting up queue
> (time (length (apply-words (take-words Feature 100))))
cpu time: 3700 real time: 4473 gc time: 1926

> (time (length (apply-words (take-words Feature 500))))
cpu time: 13710 real time: 16123 gc time: 6776
500
> (time (begin (length (apply-words (take-words Feature 750))) #t))
cpu time: 688109 real time: 715061 gc time: 502244
> (time (begin (length (apply-words (take-words Feature 1000))) #t))
cpu time: 884246 real time: 915357 gc time: 664900


Making epsilons DFS. Time has gotten SUPER SMALL wtf

> (time (begin (apply-words (take-words Feature 500)) #t))
cpu time: 1883 real time: 1895 gc time: 587
> (time (length (apply-words (take-words Feature 1000))))
cpu time: 221361 real time: 215320 gc time: 94911
1000

Cleaning up search more -- everything is DFS
expanded state came from a symbol generated, otherwise BFS

>  (time (begin (apply-words (take-words Feature 1000)) #t))
cpu time: 101509 real time: 101149 gc time: 41087
#t
>  (time (begin (apply-words (take-words Feature 500)) #t))
cpu time: 1082 real time: 1065 gc time: 86
#t


> (time (random-word Feature 5))
cpu time: 25207 real time: 26206 gc time: 8253
'(maprecipient-id maptime selectdur reducelength reduceset reducelength)

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation of CDRs using Features

;; helpers for map
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


;; Filter : Eid x CDRs -> CDRs
(define (Filter f t)
  (filter (tag->function f) t))

;; Map : CDRTree -> CDRTree
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
    [(? Value? v) (if (not (list? v)) (f `(,v)) (f v))]
    [`(,(? Value? v) ...) (f v)]
    [`(,(? Label? e) ,(? Value? v) ...) (f v)]
    [`(,(? Label? e) . ,(? Value? v)) (f `(,v))]
    [`(,(? Label? e) ,(? Label? e2) ,(? Value? v) ...) (f v)]
    [`(,(? Label? e)
       (,(? Label? l) ,(? Value? v) ,vs ...)
       ...)
     (map f (cons v vs))]
    [`(,(? Label? e)
       (,(? Label? l1) ,(? Label? l2) ,(? Value? vs) ...)
       ...)
     `(,e . ,(map (λ (x) (f (cddr x))) (cdr o)))]
    [`(,(? Label? e) . ,T) `(,e . ,((Reduce f) T))]
    [`(,T ...) (map (Reduce f) T)])) 



;; putting it all together

(define (filterword? x)
  (and (symbol? x)
       (let ((x (symbol->string x)))
         (and (>= (string-length x) 6)
              (string=? (substring x 0 6) "filter")))))
(define (reduceword? x)
  (and (symbol? x)
       (let ((x (symbol->string x)))
         (and (>= (string-length x) 6)
              (string=? (substring x 0 6) "reduce")))))
(define (selectword? x)
  (and (symbol? x)
       (let ((x (symbol->string x)))
         (and (>= (string-length x) 6)
              (string=? (substring x 0 6) "select")))))
(define (mapword? x)
  (and (symbol? x)
       (let ((x (symbol->string x)))
         (and (>= (string-length x) 3)
              (string=? (substring x 0 3) "map")))))

(define (apply-word w ls)
  (match w
    ['() ls]
    [`(,(? filterword? f) . ,w)
     (let ((t (string->symbol (substring (symbol->string f) 6))))
       (apply-word w (Filter t ls)))]
    [`(,(? mapword? f) . ,w)
     (let ((t (string->symbol (substring (symbol->string f) 3))))
       (apply-word w ((Map t) ls)))]
    [`(,(? selectword? f) . ,w)
     (let ((t (string->symbol (substring (symbol->string f) 6))))
       (apply-word w ((Select t) ls)))]
    [`(,(? reduceword? f) . ,w)
     (let ((f (tag->function (string->symbol (substring (symbol->string f) 6)))))
       (apply-word w ((Reduce f) ls)))]
    [else (error (format "Invalid word ~s" w))]))

(define (apply-words ws)
  (map (λ (x) (begin (apply-word x CDRs))) ws))

(define (eval w) (apply-word w CDRs))

;;;;;;;;;;;;;;;;
;; animation

(require 2htdp/image)
(require 2htdp/universe)

(define SQUARE-SIZE 5)
(define SCREEN-SIZE 1000)
(define (draw-value v)
  (cond
    [(number? v) (square SQUARE-SIZE "solid" "yellow")]
    [(symbol? v) (square SQUARE-SIZE "solid" "red")]
    [else (square SQUARE-SIZE "solid" "blue")]))

(define (draw-label _)
  (rectangle SQUARE-SIZE (* 2 SQUARE-SIZE) "solid" "brown"))

(define (draw-blank)
  (square SQUARE-SIZE "solid" "white"))
(define (draw-CDR v)
  (square SQUARE-SIZE "solid" "black"))

(define (draw-tree T)

  (match T
    [#f empty-image]
    ['() empty-image]
    [(? Value? v) (draw-value v)]
    [(? CDR? c) (draw-CDR c)]
    [`(,(? Label? e) . ,T)
     (above (draw-label e)
            (draw-tree T))]
    [`(,T ...)
     (foldr (λ (x a)
              (beside (draw-tree x) (draw-blank) a))
            empty-image
            T)]))

(define (step/draw W)
  (match W
    [`(,ls ()) (list ls '())]
    [`(,ls (,(? filterword? f) . ,w))
     (let ((t (string->symbol (substring (symbol->string f) 6))))
       (list (Filter t ls) w))]
    [`(,ls (,(? mapword? f) . ,w))
     (let ((t (string->symbol (substring (symbol->string f) 3))))
       (list ((Map t) ls) w))]
    [`(,ls (,(? selectword? f) . ,w))
     (let ((t (string->symbol (substring (symbol->string f) 6))))
       (list ((Select t) ls) w))]
    [`(,ls (,(? reduceword? f) . ,w))
     (let ((f (tag->function (string->symbol (substring (symbol->string f) 6)))))
       (list ((Reduce f) ls) w))]
    [else (error "Invalid word")]))


(define (draw-word w)
  (text
   (foldr (λ (x a) (string-append (symbol->string x) "" a)) "" w)
   12
   "black"))

(define (animate-eval w)
  (car (big-bang `(,CDRs ,w)
    [on-key (λ (x i) (step/draw x))]
    [to-draw (λ (x)
               (overlay
                (above
                 (draw-word (cadr x))
                 (rectangle 50 50 "solid" "white")
                 (draw-tree (car x)))
                (empty-scene SCREEN-SIZE SCREEN-SIZE)))])))




;;;;;;;;;;;;;;;;;;;;;;
;; Old grammars kept for posterity

#;
(define REDUCE-OPS (map car REDUCE-FNS))

#;
(define Feature-notypes
  (CNF->PDA
   (CFG->CNF
    `((Feature -> (Filter* G Reduce+))
      (Filter* -> ε ('filter FilterOp Filter*))
      (Reduce+ -> ('reduce ReduceOp) ('reduce ReduceOp Reduce+))
      (G -> ('select Eid) ('map Eid G 'reduce ReduceOp))
      (FilterOp -> . ,(map (λ (x) `',x) FILTER-OPS))
      (ReduceOp -> . ,(map (λ (x) `',x) REDUCE-OPS))
      (Eid -> . ,(map (λ (x) `',x) FIELDS))))))

#;(define Feature-2x
  (CNF->PDA
   (CFG->CNF
    `((Feature ->
               (Filter* GNats 'reduce ReduceNats->NatOp)
               (Filter* GSet 'reduce ReduceSet->NatOp))
      (Filter* -> ε ('filter FilterOp Filter*))
      (GNats ->
            ('select EidNat)
            ('map Eid GNats 'reduce ReduceNats->NatOp)
            ('map Eid GSet 'reduce ReduceSet->NatOp))
      
      (GSet ->
            ('select Eid)
            ('map Eid GSet 'reduce ReduceSet->SetOp)
            ('map Eid GNats 'reduce ReduceSet->SetOp))
      
      
      (FilterOp -> . ,(map (λ (x) `',x) FILTER-OPS))
      (ReduceNats->NatOp -> . ,(map (λ (x) `',x) REDUCE-NATS->NAT-OPS))
      (ReduceSet->NatOp -> . ,(map (λ (x) `',x) REDUCE-SET->NAT-OPS))
      (ReduceSet->SetOp -> . ,(map (λ (x) `',x) REDUCE-SET->SET-OPS))
      (EidNat -> . ,(map (λ (x) `',x) NATFIELDS))
      (Eid -> . ,(map (λ (x) `',x) FIELDS))))))