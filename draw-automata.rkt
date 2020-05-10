#lang racket


(require 2htdp/image "basics.rkt")

(provide draw-automaton
         make-PDA-dance)

(define SCENE-HEIGHT 900)
(define SCENE-WIDTH 960)
(define (LAYER-DIST k) (/ SCENE-HEIGHT (add1 k)))
(define BORDER-BUFFER 0)
(define STATE-SIZE 20)
(define FONT-SIZE 12)

(define (draw-start-state S)
  (overlay (circle STATE-SIZE "outline" "red")
           (circle STATE-SIZE "solid" "white")))

(define (draw-final-start-state S)
  (overlay (circle STATE-SIZE "outline" "red")
           (circle (* 4 (/ STATE-SIZE 5)) "outline" "black")
           (circle STATE-SIZE "solid" "white")))

(define (draw-final-state S)
  (overlay
   (circle STATE-SIZE "outline" "black")
   (circle (* 4 (/ STATE-SIZE 5)) "outline" "black")
   (circle STATE-SIZE "solid" "white")))

(define (draw-state S)
  (overlay
   (circle STATE-SIZE "outline" "black")
   (circle STATE-SIZE "solid" "white")))


(define (draw-transition from to I)
  (if (equal? from to)
      (place-image/align
       (ellipse 40 50 "outline" "black")
        (car from)(cadr from) "center" 
        "bottom"
        I)
      (add-line
       I
       (car from) (cadr from)
       (car to) (cadr to)
       "black")))


(define (reachable-from δ l)
  (foldr
   (λ (x a)
     (if (and (memv (car x) l) (eqv? (cadr x) 'ε))
         (cons (caddr x) a)
         a))
   '()
   δ))


;; for now, implementing a naive algorithm to get things off the ground
(define (arrange-states S A δ)
  (let loop ((undrawn (remove S A))
             (curr-layer `(,S)))
    (cond
      [(null? undrawn) `(,curr-layer)]
      ;; if there are unreachable states!
      [(null? curr-layer) `(,undrawn)]
      [else
       (let ((next-layer
              (foldr (λ (x a)
                       (if (and (memv (car x) curr-layer)
                                (memv (caddr x) undrawn))
                           (set-cons (caddr x) a)
                           a))
                     `()
                     δ)))
         (let ((undrawn (set-difference undrawn next-layer)))
           `(,curr-layer . ,(loop undrawn next-layer))))])))

(define (make-coords cols k0 k)
  (match cols
    ['() '()]
    [`(,as . ,c)
     (let ((cs (map cons
                    as
                    (build-list
                     (length as)
                     (λ (i)
                       (list (+ BORDER-BUFFER (* k (/ SCENE-HEIGHT k0)))
                             (+ BORDER-BUFFER  (* (add1 i) (LAYER-DIST (add1 (length as)))))))))))
       (append cs (make-coords c k0 (add1 k))))]))



(define (draw-states S F coords I)
  (foldr
   (λ (c i)
     (match c
       [`(,n ,x ,y)
        (cond
          [(and (eqv? n S) (memv n F)) (place-image (draw-final-start-state (symbol->string n))  x y i)]
          [(eqv? n S) (place-image (draw-start-state (symbol->string n)) x y i)]
          [(memv n F) (place-image (draw-final-state (symbol->string n))  x y i)]
          [else (place-image (draw-state (symbol->string n)) x y i)])]))
   I
   coords))

(define (draw-transitions coords δ I)
  (foldr
   (λ (x a)
     (match x
       [`(,S1 ,on ,S2 . ,rs)
        (let ((c1 (assv S1 coords))
              (c2 (assv S2 coords)))
          (if (and c1 c2)
              (draw-transition (cdr c1) (cdr c2) a)
              (if c1
                  (error (format "no value for ~s" S2))
                  (error (format "no value for ~s" S1)))))]))
   I
   δ))

(define (draw-automaton M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let* ((cols (arrange-states S A δ))
            (coords (make-coords cols (length cols) 1)))
       (draw-states
         S F coords
         (draw-transitions
          coords
          δ
          (empty-scene SCENE-WIDTH SCENE-HEIGHT))))]))




;;;;;;;;;;;;;
;; animation

(require 2htdp/universe)


(define (shuffle-one ls k)
  (cond
    [(null? ls) '()]
    [(zero? k) (cons (shuffle (car ls)) (cdr ls))]
    [else (cons (car ls) (shuffle-one (cdr ls) (sub1 k)))]))

(define (move-one-forward ls k)
  (cond
    [(null? ls) '()]
    [(zero? k)
     (if (null? (car ls))
         (move-one-forward (cdr ls) 0)
         (if (null? (cdr ls))
             (list* (cdar ls) (list (caar ls)) (cdr ls))
             (list* (cdar ls) (cons (caar ls) (cadr ls)) (cddr ls))))]
    [else (cons (car ls) (move-one-forward (cdr ls) (sub1 k)))]))

(define (move-one-back ls k)
  (cond
    [(null? ls) '()]
    [(zero? k)
     (if (null? (car ls))
         (move-one-back (cdr ls) 0)
         (list* (list (caar ls)) (cdar ls) (cdr ls)))]
    [else (cons (car ls) (move-one-back (cdr ls) (sub1 k)))]))

(define (mutate ls)
  (match (random 3)
    [0 (shuffle-one ls (random (length ls)))]
    [1 (move-one-back ls (random (length ls)))]
    [2 (move-one-forward ls (random (length ls)))]))

(define (draw-arrangement S F δ)
  (λ (cols)
    (let ((coords (make-coords cols (length cols) 1)))
      (draw-states
         S F coords
         (draw-transitions
          coords
          δ
          (empty-scene SCENE-WIDTH SCENE-HEIGHT))))))


(define (make-PDA-dance M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (big-bang (arrange-states S A δ)
       [on-tick mutate .3]
       [to-draw (draw-arrangement S F δ)])]))
