#lang racket


(require 2htdp/image "basics.rkt" "examples.rkt")

(provide draw-automaton
         make-PDA-dance)

(define SCENE-HEIGHT 900)
(define SCENE-WIDTH 960)
(define (LAYER-DIST k) (/ SCENE-HEIGHT (add1 k)))
(define BORDER-BUFFER 0)
(define STATE-SIZE 20)
(define FONT-SIZE 12)


(define TEXT-COLOR "black")
(define Δ-FONT-SIZE 8)
(define Δ-raise 10)
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


(define (format-transition x)
  (match x
    [`(,S1 ,a ,S2) (symbol->string a)]
    [`(,S1 ,a ,S2 preserve-stack) (symbol->string a)]
    [`(,S1 #t ,S2 (pop on ,b push ,vs))
     (format-transition `(,S1 Σ ,S2 (pop on ,b push ,vs)))]
    [`(,S1 ,a ,S2 (pop on #t push ,vs))
     (format-transition `(,S1 Σ ,S2 (pop on Γ push ,vs)))]
    [`(,S1 ,a ,S2 (pop on ,b push ()))
     (string-append (symbol->string a) "/ pop on " (symbol->string b))]
    [`(,S1 ,a ,S2 (pop on ,b push ,vs))
     (string-append
      (symbol->string a)
      "/"
      (symbol->string b)
      "->"
      (symbol->string (foldl (λ (x a) (symbol-append a x)) (car vs) (cdr vs))))]))


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


(define (make-label es)
  (foldr
   (λ (x a) (above (text (format-transition x) Δ-FONT-SIZE TEXT-COLOR) a))
   empty-image
   es))

(define (draw-transition c1 c2 I δ? es)
  (let* ((mid-x (/ (+ (car c1) (car c2)) 2))
         (mid-y (/ (+ (cadr c1) (cadr c2)) 2))
         (hyp (sqrt (+ (sqr (- (car c1) (car c2)))
                       (sqr (- (cadr c1) (cadr c2))))))
         (opp (abs (- (cadr c1) (cadr c2))))
         (θ (if (zero? hyp) 0 (asin (/ opp hyp)))))
    (place-image
       (make-label es)
       mid-x mid-y
       (if (< (car c1) (car c2))
           (scene+curve I
                        (car c1) (cadr c1) 30 1/3
                        (car c2) (cadr c2) -30 1/3
                        "black")
           (scene+curve I
                        (car c1) (cadr c1) -60 1/4
                        (car c2) (cadr c2) 60 1/4
                        "red")))))

(define (draw-transitions δ? coords δ I)
  (let loop ((δ δ)
             (I I))
    (cond
      [(null? δ) I]
      [else
       (let* ((s1 (caar δ))
              (s2 (caddar δ))
              (es (filter (λ (x) (and (eqv? (car x) s1) (eqv? (caddr x) s2)))
                          δ))
              (δ (filter (λ (x) (or (not (eqv? (car x) s1))
                                    (not (eqv? (caddr x) s2))))
                         δ)))
         (let ((c1 (cdr (assv s1 coords)))
               (c2 (cdr (assv s2 coords))))
           (loop δ (draw-transition c1 c2 I δ? es))))])))



(define ((draw-automaton δ?) M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (let* ((cols (arrange-states S A δ))
            (coords (make-coords cols (length cols) 1)))
       (draw-states
         S F coords
         (draw-transitions
          δ?
          coords
          δ
          (empty-scene SCENE-WIDTH SCENE-HEIGHT))))]))

(define-syntax draw-in-window
  (syntax-rules ()
    [(_ e δ?)
     (big-bang e
       [to-draw (draw-automaton δ?)])]))


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
          #f
          coords
          δ
          (empty-scene SCENE-WIDTH SCENE-HEIGHT))))))


(define (make-PDA-dance M)
  (match M
    [(Automaton S F A δ Σ Γ)
     (big-bang (arrange-states S A δ)
       [on-tick mutate .3]
       [to-draw (draw-arrangement S F δ)])]))

