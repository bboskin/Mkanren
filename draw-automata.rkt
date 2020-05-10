#lang racket


(require 2htdp/image
         "basics.rkt"
         "grammar-tests.rkt")

(define SCENE-HEIGHT 400)
(define SCENE-WIDTH 560)
(define (LAYER-DIST k) (/ SCENE-HEIGHT (add1 k)))
(define BORDER-BUFFER 0)
(define STATE-SIZE 20)
(define FONT-SIZE 12)

(define (draw-start-state S)
  (overlay (text S FONT-SIZE "black")
           (circle STATE-SIZE "outline" "red")
           (circle STATE-SIZE "solid" "white")))

(define (draw-final-start-state S)
  (overlay (text S FONT-SIZE "black")
           (circle STATE-SIZE "outline" "red")
           (circle (* 4 (/ STATE-SIZE 5)) "outline" "black")
           (circle STATE-SIZE "solid" "white")))

(define (draw-final-state S)
  (overlay
   (text S FONT-SIZE "black")
   (circle STATE-SIZE "outline" "black")
   (circle (* 4 (/ STATE-SIZE 5)) "outline" "black")
   (circle STATE-SIZE "solid" "white")))

(define (draw-state S)
  (overlay
   (text S FONT-SIZE "black")
   (circle STATE-SIZE "outline" "black")
   (circle STATE-SIZE "solid" "white")))


(define (draw-transition from to I)
  (add-line
    I
    (car from) (cadr from)
    (car to) (cadr to)
    "black"))


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
      ;; unreachable states!
      [(null? curr-layer) (loop '() undrawn)]
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
        (displayln n)
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
        (let ((c1 (cdr (assv S1 coords)))
              (c2 (cdr (assv S2 coords))))
          (draw-transition c1 c2 a))]))
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


(require 2htdp/universe)

(big-bang (list Bool/PDA Bool/min)
    [to-draw (λ (x) (above (draw-automaton (car x))
                           (draw-automaton (cadr x))))])