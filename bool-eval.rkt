#lang racket

(require "automata.rkt")
(provide Bool
         Val-of
         
         Logic-Terms
         Logic-Term?
         term?
         var?

         p-true
         all-true
         none-true)

(define Vars '(p #;q))
(define (var? x) (and (memv x Vars) #t))
(define Terms '(not andbegin andend orbegin orend))
(define (term? x) (and (memv x Terms) #t))
(define Logic-Terms (append Vars Terms))
(define (Logic-Term? x) (memv x Logic-Terms))


(define not? (λ (x) (eqv? x 'not)))
(define andbegin? (λ (x) (eqv? x 'andbegin)))
(define andend? (λ (x) (eqv? x 'andend)))
(define orbegin? (λ (x) (eqv? x 'orbegin)))
(define orend? (λ (x) (eqv? x 'orend)))




;;;;;;;;;;;;;;;;;;;;;;;
;; Just the grammar
;; with and, or, not, and a finite number of variables.

(define Bool
  (Automaton
   'One
   '(F)
   '(One Many OneP F)
   `((One ,var? F preserve-stack)
     (One ,not? One preserve-stack)
     (One ,andbegin? Many (pop on #f push (A #f)))
     (One ,orbegin? Many (pop on #f push (O #f)))
     (Many ,not? OneP preserve-stack)
     (Many ,var? Many preserve-stack)
     (Many ,andbegin? Many (pop on A push (A A)))
     (Many ,andbegin? Many (pop on O push (A O)))
     (Many ,orbegin? Many (pop on A push (O A)))
     (Many ,orbegin? Many (pop on O push (O O)))
     (Many ,andend? Many (pop on A push ()))
     (Many ,andend? F (pop on A push ()))
     (Many ,orend? Many (pop on O push ()))
     (Many ,orend? F (pop on O push ()))
     (OneP ,not? OneP preserve-stack)
     (OneP ,var? Many preserve-stack)
     (OneP ,andbegin? Many (pop on A push (A A)))
     (OneP ,andbegin? Many (pop on O push (A O)))
     (OneP ,orbegin? Many (pop on A push (O A)))
     (OneP ,orbegin? Many (pop on O push (O O))))
   Logic-Terms
   '((A O))))


;;;;;;;;;;;;;;;;;;;;;;;
;; let's start thinking about
;; satisfiability!


(define (make-env xs t)
  (Automaton
   'S
   '(F)
   '(S F)
   (map (λ (t) `(S ,(λ (x) (eqv? x t)) F)) t)
   xs
   '()))

(define p-true (make-env '(p q) '(p)))
(define all-true (make-env '(p q) '(p q)))
(define none-true (make-env '(p q) '()))
(define ((var-true? ρ) x) (and (var? x) (accept? ρ (list x))))
(define ((var-false? ρ) x) (and (var? x) (not (accept? ρ (list x)))))
(define (Val-of ρ)
  (let ((var-true? (var-true? ρ))
        (var-false? (var-false? ρ)))
    (Automaton
     'I-t
     '(F)
     '(I-t I-f F
           P-s P-f
           Nor Or Nand And
           Nor-One-t Nor-One-f Nor-succ Nor-succ-One
           Or-One-t Or-One-f Or-succ Or-succ-One
           Nand-One-t Nand-One-f Nand-fail
           And-One-t And-One-f And-fail)
     `(;;;;;;;;;;;;;;;;;;;;;;
       ;; epsilon transitions
       
       (P-f ε Nor (pop on Of push (Of)))
       (P-f ε Or (pop on Ot push (Ot)))
       (P-f ε Nor-succ (pop on Ofs push (Ofs)))
       (P-f ε Or-succ (pop on Ots push (Ots)))
       (P-f ε Nand-fail (pop on Af push (Aff)))
       (P-f ε And-fail (pop on At push (Atf)))
       (P-f ε Nand-fail (pop on Aff push (Aff)))
       (P-f ε And-fail (pop on Atf push (Atf)))
       
       (P-s ε Or-succ (pop on Ot push (Ots)))
       (P-s ε Nor-succ (pop on Of push (Ofs)))
       (P-s ε Or-succ (pop on Ots push (Ots)))
       (P-s ε Nor-succ (pop on Ofs push (Ofs)))
       (P-s ε And (pop on At push (At)))
       (P-s ε Nand (pop on Af push (Af)))
       (P-s ε And-fail (pop on Atf push (Atf)))
       (P-s ε Nand-fail (pop on Aff push (Aff)))
       
       (Or ε Or-succ (pop on Ots push (Ots)))
       (Nor ε Nor-succ (pop on Ofs push (Ofs)))
       (And ε And-fail (pop on Atf push (Atf)))
       (Nand ε Nand-fail (pop on Aff push (Aff)))

       (P-s ε F (pop on #f push (#f)))

       ;; Intro states
       (I-t ,not? I-f preserve-stack)
       (I-t ,var-true? P-s preserve-stack)
       (I-t ,var-false? P-f preserve-stack)
       (I-t ,orbegin? Or (pop on #f push (Ot #f)))
       (I-t ,andbegin? And (pop on #f push (At #f)))

       (I-f ,not? I-t preserve-stack)
       (I-f ,var-false? P-s preserve-stack)
       (I-f ,var-true? P-f preserve-stack)
       (I-f ,orbegin? Nor (pop on #f push (Of #f)))
       (I-f ,andbegin? Nand (pop on #f push (Af #f)))

       
       
       ;; or
       (Or ,var-true? Or-succ (pop on Ot push (Ots)))
       (Or ,var-false? Or preserve-stack)
       (Or ,not? Or-One-f preserve-stack)
       (Or ,orbegin? Or (pop on Ot push (Ot Ot)))
       (Or ,andbegin? And (pop on Ot push (At Ot)))
       (Or ,orend? P-f (pop on Ot push ()))

       (Or-succ ,not? Or-succ-One preserve-stack)
       (Or-succ ,var? Or-succ preserve-stack)
       (Or-succ ,orbegin? Or (pop on Ots push (Ot Ots)))
       (Or-succ ,andbegin? And (pop on Ots push (At Ots)))
       (Or-succ ,orend? P-s (pop on Ots push ()))
       
       (Or-One-t ,not? Or-One-f preserve-stack)
       (Or-One-t ,var-true? Or-succ (pop on Ot push (Ots)))
       (Or-One-t ,var-false? Or preserve-stack)
       (Or-One-t ,orbegin? Or (pop on Ot push (Ot Ot)))
       (Or-One-t ,andbegin? And (pop on Ot push (At Ot)))

       (Or-One-f ,not? Or-One-t preserve-stack)
       (Or-One-f ,var-false? Or-succ (pop on Ot push (Ots)))
       (Or-One-f ,var-true? Or preserve-stack)
       (Or-One-f ,orbegin? Nor (pop on Ot push (Of Ot)))
       (Or-One-f ,andbegin? Nand (pop on Ot push (Af Ot)))
       
       (Or-succ-One ,not? Or-succ-One preserve-stack)
       (Or-succ-One ,not? Or-succ-One preserve-stack)
       (Or-succ-One ,var? Or-succ preserve-stack)
       (Or-succ-One ,orbegin? Or-succ (pop on Ots push (Ots Ots)))
       (Or-succ-One ,andbegin? And (pop on Ots push (At Ots)))
       
       ;; negated or
       (Nor ,var-true? Nor-succ (pop on Of push (Ofs)))
       (Nor ,var-false? Nor preserve-stack)
       (Nor ,not? Nor-One-f preserve-stack)
       (Nor ,orbegin? Or (pop on Of push (Ot Of)))
       (Nor ,andbegin? And (pop on Of push (At Of)))
       (Nor ,orend? P-s (pop on Of push ()))
       
       (Nor-succ ,var? Nor-succ preserve-stack)
       (Nor-succ ,not? Nor-succ-One preserve-stack)
       (Nor-succ ,orbegin? Or (pop on Ofs push (Ot Ofs)))
       (Nor-succ ,andbegin? And (pop on Ofs push (At Ofs)))
       (Nor-succ ,orend? P-f (pop on Ofs push ()))
       
       (Nor-succ-One ,not? Nor-succ-One preserve-stack)
       (Nor-succ-One ,not? Nor-succ-One preserve-stack)
       (Nor-succ-One ,var? Nor-succ preserve-stack)
       (Nor-succ-One ,orbegin? Or (pop on Ofs push (Ot Ofs)))
       (Nor-succ-One ,andbegin? And (pop on Ofs push (At Ofs)))
       
       (Nor-One-f ,var-false? Nor-succ (pop on Of push (Ofs)))
       (Nor-One-f ,var-true? Nor preserve-stack)
       (Nor-One-f ,not? Nor-One-t preserve-stack)
       (Nor-One-f ,orbegin? Nor (pop on Of push (Of Of)))       
       (Nor-One-f ,andbegin? Nand (pop on Of push (Af Of)))
       
       (Nor-One-t ,var-true? Nor-succ (pop on Of push (Ofs)))
       (Nor-One-t ,var-false? Nor preserve-stack)
       (Nor-One-t ,not? Nor-One-f preserve-stack)
       (Nor-One-t ,orbegin? Nor (pop on Of push (Of Ot)))
       (Nor-One-t ,andbegin? Nand (pop on Of push (Af Ot)))
       
       ;; and
       
       (And ,var-true? And preserve-stack)
       (And ,var-false? And-fail (pop on At push (Atf)))
       (And ,not? And-One-f preserve-stack)
       (And ,orbegin? Or (pop on At push (Ot At)))
       (And ,andbegin? And (pop on At push (At At)))
       (And ,andend? P-s (pop on At push ()))
       
       (And-fail ,not? And-fail-One preserve-stack)
       (And-fail ,var? And-fail preserve-stack)
       (And-fail ,orbegin? Or (pop on Atf push (Ot Atf)))
       (And-fail ,andbegin? And (pop on Atf push (At Atf)))
       (And-fail ,andend? P-f (pop on Atf push ()))
       
       (And-One-t ,not? And-One-f preserve-stack)
       (And-One-t ,var-true? And preserve-stack)
       (And-One-t ,var-false? And-fail (pop on At push (Atf)))
       (And-One-t ,orbegin? Or (pop on At push (Ot At)))
       (And-One-t ,andbegin? And (pop on At push (At At)))

       (And-One-f ,not? And-One-t preserve-stack)
       (And-One-f ,var-false? And preserve-stack)
       (And-One-f ,var-true? And-fail (pop on At push (Atf)))
       (And-One-f ,orbegin? Nor (pop on At push (Of At)))
       (And-One-f ,andbegin? Nand (pop on At push (Af At)))
       
       (And-fail-One ,not? And-fail-One preserve-stack)
       (And-fail-One ,not? And-fail-One preserve-stack)
       (And-fail-One ,var? And-fail preserve-stack)
       (And-fail-One ,orbegin? Or (pop on Atf push (Ot Atf)))
       (And-fail-One ,andbegin? And (pop on Atf push (At Atf)))
       
       ;; negated and
       (Nand ,var-true? Nand preserve-stack)
       (Nand ,var-false? Nand-fail (pop on Af push (Aff)))
       (Nand ,not? Nand-One-f preserve-stack)
       (Nand ,orbegin? Or (pop on Af push (Ot Af)))
       (Nand ,andbegin? And (pop on Af push (At Af)))
       (Nand ,andend? P-f (pop on Af push ()))
       
       (Nand-fail ,not? Nand-fail-One preserve-stack)
       (Nand-fail ,var? Nand-fail preserve-stack)
       (Nand-fail ,orbegin? Or (pop on Aff push (Ot Aff)))
       (Nand-fail ,andbegin? And (pop on Aff push (At Aff)))
       (Nand-fail ,andend? P-s (pop on Aff push ()))
       
       (Nand-One-t ,not? Nand-One-f preserve-stack)
       (Nand-One-t ,var-true? Nand preserve-stack)
       (Nand-One-t ,var-false? Nand-fail (pop on Af push (Aff)))
       (Nand-One-t ,orbegin? Or (pop on Af push (Ot Af)))
       (Nand-One-t ,andbegin? And (pop on Af push (At Af)))

       (Nand-One-f ,not? Nand-One-t preserve-stack)
       (Nand-One-f ,var-false? Nand preserve-stack)
       (Nand-One-f ,var-true? Nand-fail (pop on Af push (Aff)))
       (Nand-One-f ,orbegin? Nor (pop on Af push (Of Af)))
       (Nand-One-f ,andbegin? Nand (pop on Af push (Af Af)))
       
       (Nand-fail-One ,not? Nand-fail-One preserve-stack)
       (Nand-fail-One ,not? Nand-fail-One preserve-stack)
       (Nand-fail-One ,var? Nand-fail preserve-stack)
       (Nand-fail-One ,orbegin? Or (pop on Aff push (Ot Aff)))
       (Nand-fail-One ,andbegin? And (pop on Aff push (At Aff))))
     Logic-Terms
     '((Ot Of At Af Ots Ofs Atf Aff)))))


(define p? (λ (x) (eqv? x 'p)))
(define q? (λ (x) (eqv? x 'q)))

(define Sat?
  (let ()
    (Automaton
     'I-t
     '(F)
     '(I-t I-f F
           P-s P-f
           Nor Or Nand And
           Nor-One-t Nor-One-f Nor-succ Nor-succ-One
           Or-One-t Or-One-f Or-succ Or-succ-One
           Nand-One-t Nand-One-f Nand-fail
           And-One-t And-One-f And-fail)
     `(;; transitions with variables
       (I-t ,p? P-s preserve-stack (pop on #f push (pT)))
       (I-t ,p? P-f preserve-stack (pop on #f push (pF)))
       (I-t ,q? P-s preserve-stack (pop on #f push (qT)))
       (I-t ,q? P-f preserve-stack (pop on #f push (qF)))

       (I-f ,p? P-f preserve-stack (pop on #f push (pT)))
       (I-f ,p? P-s preserve-stack (pop on #f push (pF)))
       (I-f ,q? P-f preserve-stack (pop on #f push (qT)))
       (I-f ,q? P-s preserve-stack (pop on #f push (qF)))

       ;; its gonna be fun...
       (Or ,p? Or-succ (pop on Ot push (Ots)) (pop on #f push (pT)))
       (Or ,p? Or (pop on Ot push (Ots)) (pop on #f push (pF)))
       (Or ,p? Or-succ (pop on Ot push (Ots)) (pop on ϵ push (pT)))
       (Or ,p? Or (pop on Ot push (Ots)) (pop on ϵ push (pF)))
       (Or ,p? Or-succ (pop on Ot push (Ots)) (pop on pT push (pT)))
       (Or ,p? Or (pop on Ot push (Ots)) (pop on pF push (pF)))
       (Or ,p? Or-succ (pop on Ot push (Ots)) (pop on qT push (pTqT)))
       (Or ,p? Or (pop on Ot push (Ots)) (pop on pF push (pF)))
       
       






       ;;;;;;;;;;;;;;;;;;;;;;
       ;; epsilon transitions
       
       (P-f ε Nor (pop on Of push (Of)) preserve-stack)
       (P-f ε Or (pop on Ot push (Ot)) preserve-stack)
       (P-f ε Nor-succ (pop on Ofs push (Ofs)) preserve-stack)
       (P-f ε Or-succ (pop on Ots push (Ots)) preserve-stack)
       (P-f ε Nand-fail (pop on Af push (Aff))  preserve-stack)
       (P-f ε And-fail (pop on At push (Atf)) preserve-stack)
       (P-f ε Nand-fail (pop on Aff push (Aff)) preserve-stack)
       (P-f ε And-fail (pop on Atf push (Atf)) preserve-stack)
       
       (P-s ε Or-succ (pop on Ot push (Ots)) preserve-stack)
       (P-s ε Nor-succ (pop on Of push (Ofs)) preserve-stack)
       (P-s ε Or-succ (pop on Ots push (Ots)) preserve-stack)
       (P-s ε Nor-succ (pop on Ofs push (Ofs)) preserve-stack)
       (P-s ε And (pop on At push (At)) preserve-stack)
       (P-s ε Nand (pop on Af push (Af)) preserve-stack)
       (P-s ε And-fail (pop on Atf push (Atf)) preserve-stack)
       (P-s ε Nand-fail (pop on Aff push (Aff)) preserve-stack)
       
       (Or ε Or-succ (pop on Ots push (Ots)) preserve-stack)
       (Nor ε Nor-succ (pop on Ofs push (Ofs)) preserve-stack)
       (And ε And-fail (pop on Atf push (Atf)) preserve-stack)
       (Nand ε Nand-fail (pop on Aff push (Aff)) preserve-stack)

       (P-s ε F (pop on #f push (#f)) preserve-stack)

       ;; Intro states
       (I-t ,not? I-f preserve-stack preserve-stack)
       (I-t ,orbegin? Or (pop on #f push (Ot #f)) preserve-stack)
       (I-t ,andbegin? And (pop on #f push (At #f)) preserve-stack)

       (I-f ,not? I-t preserve-stack preserve-stack)
       (I-f ,orbegin? Nor (pop on #f push (Of #f)) preserve-stack)
       (I-f ,andbegin? Nand (pop on #f push (Af #f)) preserve-stack)

       (Or ,not? Or-One-f preserve-stack preserve-stack)
       (Or ,orbegin? Or (pop on Ot push (Ot Ot)) preserve-stack)
       (Or ,andbegin? And (pop on Ot push (At Ot)) preserve-stack)
       (Or ,orend? P-f (pop on Ot push ()) preserve-stack)

       (Or-succ ,not? Or-succ-One preserve-stack preserve-stack)
       (Or-succ ,var? Or-succ preserve-stack preserve-stack)
       (Or-succ ,orbegin? Or (pop on Ots push (Ot Ots)) preserve-stack)
       (Or-succ ,andbegin? And (pop on Ots push (At Ots)) preserve-stack)
       (Or-succ ,orend? P-s (pop on Ots push ()) preserve-stack)
       
       (Or-One-t ,not? Or-One-f preserve-stack preserve-stack)
       (Or-One-t ,var-true? Or-succ (pop on Ot push (Ots)) preserve-stack)
       (Or-One-t ,var-false? Or preserve-stack preserve-stack)
       (Or-One-t ,orbegin? Or (pop on Ot push (Ot Ot)) preserve-stack)
       (Or-One-t ,andbegin? And (pop on Ot push (At Ot)) preserve-stack)

       (Or-One-f ,not? Or-One-t preserve-stack preserve-stack)
       (Or-One-f ,var-false? Or-succ (pop on Ot push (Ots)) preserve-stack)
       (Or-One-f ,var-true? Or preserve-stack preserve-stack)
       (Or-One-f ,orbegin? Nor (pop on Ot push (Of Ot)) preserve-stack)
       (Or-One-f ,andbegin? Nand (pop on Ot push (Af Ot)) preserve-stack)
       
       (Or-succ-One ,not? Or-succ-One preserve-stack preserve-stack)
       (Or-succ-One ,not? Or-succ-One preserve-stack preserve-stack)
       (Or-succ-One ,var? Or-succ preserve-stack preserve-stack)
       (Or-succ-One ,orbegin? Or-succ (pop on Ots push (Ots Ots)) preserve-stack)
       (Or-succ-One ,andbegin? And (pop on Ots push (At Ots)) preserve-stack)
       
       (Nor ,var-true? Nor-succ (pop on Of push (Ofs)) preserve-stack)
       (Nor ,var-false? Nor preserve-stack preserve-stack)
       (Nor ,not? Nor-One-f preserve-stack preserve-stack)
       (Nor ,orbegin? Or (pop on Of push (Ot Of)) preserve-stack)
       (Nor ,andbegin? And (pop on Of push (At Of)) preserve-stack)
       (Nor ,orend? P-s (pop on Of push ()) preserve-stack)
       
       (Nor-succ ,var? Nor-succ preserve-stack preserve-stack)
       (Nor-succ ,not? Nor-succ-One preserve-stack preserve-stack)
       (Nor-succ ,orbegin? Or (pop on Ofs push (Ot Ofs)) preserve-stack)
       (Nor-succ ,andbegin? And (pop on Ofs push (At Ofs)) preserve-stack)
       (Nor-succ ,orend? P-f (pop on Ofs push ()) preserve-stack)
       
       (Nor-succ-One ,not? Nor-succ-One preserve-stack preserve-stack)
       (Nor-succ-One ,not? Nor-succ-One preserve-stack preserve-stack)
       (Nor-succ-One ,var? Nor-succ preserve-stack preserve-stack)
       (Nor-succ-One ,orbegin? Or (pop on Ofs push (Ot Ofs)) preserve-stack)
       (Nor-succ-One ,andbegin? And (pop on Ofs push (At Ofs)) preserve-stack)
       
       (Nor-One-f ,var-false? Nor-succ (pop on Of push (Ofs)) preserve-stack)
       (Nor-One-f ,var-true? Nor preserve-stack preserve-stack)
       (Nor-One-f ,not? Nor-One-t preserve-stack preserve-stack)
       (Nor-One-f ,orbegin? Nor (pop on Of push (Of Of)) preserve-stack)       
       (Nor-One-f ,andbegin? Nand (pop on Of push (Af Of)) preserve-stack)
       
       (Nor-One-t ,var-true? Nor-succ (pop on Of push (Ofs)) preserve-stack)
       (Nor-One-t ,var-false? Nor preserve-stack preserve-stack)
       (Nor-One-t ,not? Nor-One-f preserve-stack preserve-stack)
       (Nor-One-t ,orbegin? Nor (pop on Of push (Of Ot)) preserve-stack)
       (Nor-One-t ,andbegin? Nand (pop on Of push (Af Ot)) preserve-stack)
       
       (And ,var-true? And preserve-stack preserve-stack)
       (And ,var-false? And-fail (pop on At push (Atf)) preserve-stack)
       (And ,not? And-One-f preserve-stack preserve-stack)
       (And ,orbegin? Or (pop on At push (Ot At)) preserve-stack)
       (And ,andbegin? And (pop on At push (At At)) preserve-stack)
       (And ,andend? P-s (pop on At push ()) preserve-stack)
       
       (And-fail ,not? And-fail-One preserve-stack preserve-stack)
       (And-fail ,var? And-fail preserve-stack preserve-stack)
       (And-fail ,orbegin? Or (pop on Atf push (Ot Atf)) preserve-stack)
       (And-fail ,andbegin? And (pop on Atf push (At Atf)) preserve-stack)
       (And-fail ,andend? P-f (pop on Atf push ()) preserve-stack)
       
       (And-One-t ,not? And-One-f preserve-stack preserve-stack)
       (And-One-t ,var-true? And preserve-stack preserve-stack)
       (And-One-t ,var-false? And-fail (pop on At push (Atf)) preserve-stack)
       (And-One-t ,orbegin? Or (pop on At push (Ot At)) preserve-stack)
       (And-One-t ,andbegin? And (pop on At push (At At)) preserve-stack)

       (And-One-f ,not? And-One-t preserve-stack preserve-stack)
       (And-One-f ,var-false? And preserve-stack preserve-stack)
       (And-One-f ,var-true? And-fail (pop on At push (Atf)) preserve-stack)
       (And-One-f ,orbegin? Nor (pop on At push (Of At)) preserve-stack)
       (And-One-f ,andbegin? Nand (pop on At push (Af At)) preserve-stack)
       
       (And-fail-One ,not? And-fail-One preserve-stack preserve-stack)
       (And-fail-One ,not? And-fail-One preserve-stack preserve-stack)
       (And-fail-One ,var? And-fail preserve-stack preserve-stack)
       (And-fail-One ,orbegin? Or (pop on Atf push (Ot Atf)) preserve-stack)
       (And-fail-One ,andbegin? And (pop on Atf push (At Atf)) preserve-stack)
       
       (Nand ,var-true? Nand preserve-stack preserve-stack)
       (Nand ,var-false? Nand-fail (pop on Af push (Aff)) preserve-stack)
       (Nand ,not? Nand-One-f preserve-stack preserve-stack)
       (Nand ,orbegin? Or (pop on Af push (Ot Af)) preserve-stack)
       (Nand ,andbegin? And (pop on Af push (At Af)) preserve-stack)
       (Nand ,andend? P-f (pop on Af push ()) preserve-stack)
       
       (Nand-fail ,not? Nand-fail-One preserve-stack preserve-stack)
       (Nand-fail ,var? Nand-fail preserve-stack preserve-stack)
       (Nand-fail ,orbegin? Or (pop on Aff push (Ot Aff)) preserve-stack)
       (Nand-fail ,andbegin? And (pop on Aff push (At Aff)) preserve-stack)
       (Nand-fail ,andend? P-s (pop on Aff push ()) preserve-stack)
       
       (Nand-One-t ,not? Nand-One-f preserve-stack preserve-stack)
       (Nand-One-t ,var-true? Nand preserve-stack preserve-stack)
       (Nand-One-t ,var-false? Nand-fail (pop on Af push (Aff)) preserve-stack)
       (Nand-One-t ,orbegin? Or (pop on Af push (Ot Af)) preserve-stack)
       (Nand-One-t ,andbegin? And (pop on Af push (At Af)) preserve-stack)

       (Nand-One-f ,not? Nand-One-t preserve-stack preserve-stack)
       (Nand-One-f ,var-false? Nand preserve-stack preserve-stack)
       (Nand-One-f ,var-true? Nand-fail (pop on Af push (Aff)) preserve-stack)
       (Nand-One-f ,orbegin? Nor (pop on Af push (Of Af)) preserve-stack)
       (Nand-One-f ,andbegin? Nand (pop on Af push (Af Af)) preserve-stack)
       
       (Nand-fail-One ,not? Nand-fail-One preserve-stack preserve-stack)
       (Nand-fail-One ,not? Nand-fail-One preserve-stack preserve-stack)
       (Nand-fail-One ,var? Nand-fail preserve-stack preserve-stack)
       (Nand-fail-One ,orbegin? Or (pop on Aff push (Ot Aff)) preserve-stack)
       (Nand-fail-One ,andbegin? And (pop on Aff push (At Aff))) preserve-stack)
     Logic-Terms
     '((Ot Of At Af Ots Ofs Atf Aff)
       (ϵ pT pF qT qF pTpT pTqF pFqT pFqF)))))
