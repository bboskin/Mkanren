#lang racket


(require "interface.rkt"
         "draw-automata.rkt")

(provide defrel)

#|

Types used in the file

- Input : Letter U (List Letter)

|#

;; succ : Automaton
(define succ
  (let ((s (gensym 'S)))
    (Automaton s `(,s) `(,s) '() '() '())))

;; fail : Automaton
(define fail
  (let ((s (gensym 'S)))
    (Automaton s '() `(,s) '() '() '())))

;; a wrapper for quick determining whether something is
;; an automaton or a grammar
(struct Grammar [g]) ;; g is just some CFG

;; GuM : Grammar U Automaton

#;
;; ->M : GuM -> Automaton
(define ->M
  (λ (x)
    (match x
      [(? Grammar?) (CNF->PDA (CFG->CNF x))]
      [(? Automaton?) x]
      [else (error 'disj (format "invalid argument to disj"))])))

;; conj : GuM ... -> Automaton
(define-syntax conj
  (syntax-rules ()
    [(_) succ]
    [(_ e1 es ...)
     (M-Intersection (->M e1) (conj es ...))]))



;; ->M : GuM -> Automaton
(define ->M
  (λ (x)
    (match x
      [(? Grammar?) (CNF->PDA (CFG->CNF x))]
      [(? Automaton?) x]
      [else (error 'disj (format "invalid argument to disj"))])))

;; eval-tree : Symbol x (List (cons Symbol Automaton)) -> Exp -> CFG
(define ((eval-tree name) T)
  (match T
    [`(== '(,v)) `((,name -> ',v))]
    [`(== '(,v ...)) `((,name -> (',v ...)))]
    [`(== ',v) `((,name -> ',v))]
    ['ε `((,name -> ε))]
    [(? symbol? y)
     (if (eqv? y name)
         `((,name -> ,name))
         `((,name -> ,y)))]
    [(? Automaton? A) A]
    [`(split ,es ...)
     (let ((G (append-map (eval-tree name) es)))
       (displayln G)
       `((,name -> . ,(cart-prod* (map cddr G)))))]
    [`(disj ,e ...)
     (let ((G (append-map (λ (x) ((eval-tree name) x)) e)))
       `((,name -> .
                ,(foldr set-union '()
                        (cons (map caddr G) (map cddr G))))))]
    [`(conj ,e ...)
     (let ((gums (map (λ (x) ((eval-tree name) x)) e)))
       (match gums
         [`(,e) e]
         [`(,e ...) `((intersection ,@e ...))]))]
    [`(conde ,es ...)
     `((,name -> . ,(append-map cddr (append-map (λ (x) ((eval-tree name) (cons 'conj x))) es))))]))


(define DICTIONARY '())

(struct Relation [G? A] #:transparent)


(define (lookup-all ls dict)
  (cond
    [(assv ls dict) => (λ (x) (Relation-G? (cdr x)))]
    [(cons? ls) (set-union (lookup-all (car ls) dict)
                        (lookup-all (cdr ls) dict))]
    [else '()]))

(define-syntax defrel
  (syntax-rules ()
    [(_ name body)
     (begin
       (define G ((eval-tree 'name) 'body))
       (set! G (append G (lookup-all G DICTIONARY)))
       (define A (CNF->PDA (CFG->CNF G)))
       (define name (Relation G A)))]))

;; version 1
#;
(defrel numbero
  (conde
   [(== '(z))]
   [(== '(o))]
   [(split (== '(o)) numbero)]
   [(split (== '(z)) numbero)]))


;; version 2


(defrel digito
  (conde
   [(== 'o)]
   [(== 'z)]))

(set! DICTIONARY `((digito . ,digito) . ,DICTIONARY))

(defrel ends-in-1o
  (conde
   [(== 'o)]
   [(split digito ends-in-1o)]))

(set! DICTIONARY `((ends-in-1o . ,ends-in-1o) . ,DICTIONARY))

(defrel numbero
  (conde
   [(== 'z)]
   [ends-in-1o]))

(set! DICTIONARY `((numbero . ,numbero) . ,DICTIONARY))


(defrel eveno
  (conde
   [(== 'z)]
   [(split (== 'z) ends-in-1o)]))

(set! DICTIONARY `((eveno . ,eveno) . ,DICTIONARY))

(defrel gt3o
  (conde
   [(split (== '(o)) (== '(o)))]
   [(split digito gt3o)]))

(set! DICTIONARY `((gt3o . ,gt3o) . ,DICTIONARY))


(defrel 4o (split (== 'z) (== 't) (== 'o)))

(set! DICTIONARY `((4o . ,4o) . ,DICTIONARY))

#|
;; why are these valeus different? gotta figure that out


> (find-words (CNF->PDA (CFG->CNF '((4o -> ('a 'b 'c))))) 40)
'((a b c))
> (find-words (CNF->PDA (CFG->CNF '((4o -> ('z 'z 'o))))) 40)

|#
#;
(defrel lt5o
  (disj
   (split (== '(z)) (== '(z)) (== '(o)))
   (split (== '(z)) (== '(o)) (== '(o)))
   (split (== '(o)) (== '(o)) (== '(o)))
   (split (== '(o)) (== '(z)) (== '(o)))
   (split (== '(o)) (== '(z)) (== '(o)))
   (split (== '(o)) (== '(o)))
   (split (== '(z)) (== '(o)))
   (split (== '(o)))
   (split (== '(z)))))

#;
(set! DICTIONARY `((lt5o . ,lt5o) . ,DICTIONARY))

#|

> numbero
(Relation
 '((numbero -> 'z ends-in-1o)
   (ends-in-1o -> 'z (digito ε)
   (digito ends-in-1o))
   (digito -> 'o 'z)
   (digito -> 'o 'z))
 (Automaton
  'numbero389589
  '(numbero389589F)
  '(numbero389589 numbero389589F digito digitoF digito digitoF)
  '((digito z digitoF preserve-stack)
    (digito o digitoF preserve-stack)
    (numbero389589 ε digito (pop on #t push (γ389590)))
    (digitoF ε numbero389589 (pop on γ389590 push (γ389590)))
    (numbero389589F ε numbero389589F (pop on γ389590 push ()))
    (numbero389589 o numbero389589F preserve-stack)
    (numbero389589 z numbero389589F preserve-stack))
  '(o z)
  '((γ389590))))

|#
