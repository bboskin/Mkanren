#lang racket

(require "grammars.rkt"
         "automata.rkt")
;; implementations of a few grammars, using
;; features from grammars.rkt



;; some REs and DFAs
(define A* (RE->DFA '(a *)))
(define A+ (RE->DFA '(a +)))
(define AUB (RE->DFA '(a U b)))
(define AUB* (RE->DFA '((a U b) *)))
(define AUB+ (RE->DFA '((a U b) +)))
(define AUb•c+* (RE->DFA '((a U ((b • c) +)) *)))

(define (DFA-tests)
  (let* ((A*-Σ50 (find-words A* 50))
         (A+-Σ50 (find-words A+ 50)))
    (and
     (member '() A*-Σ50)
     (not (member '() A+-Σ50))
     (equal? (cdr A*-Σ50) A+-Σ50))
    (equal? '((a) (b)) (find-words AUB 100))
    (equal? (length (find-words AUB* 2)) 7)

    (accept? AUb•c+* '())
    (accept? AUb•c+* '(a))
    (accept? AUb•c+* '(a b c))
    (not (accept? AUb•c+* '(a b a c)))
    (accept? AUb•c+* '(a a a a b c b c a b c b c b c b c a b c))
    (not (accept? AUb•c+* '(a a a a b c b c a b a c b c b c b c a b c)))))


;; Testing RE->CFG->CNF conversion
(define A*/CFG (RE->CFG '(a *)))
(define A+/CFG (RE->CFG '(a +)))
(define AUB/CFG (RE->CFG '(a U b)))
(define AUB*/CFG (RE->CFG '((a U b) *)))
(define AUB+/CFG (RE->CFG '((a U b) +)))
(define AUB•c+*/CFG (RE->CFG '((a U ((b • c) +)) *)))

(define AnBn '((S -> ε (A S B))
               (A -> 'a)
               (B -> 'b)))

(define Bool/SuperSimp
  '((S -> 'p ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define Bool/Simp
  '((S -> 'p ('not S) ('andbegin S* 'andend) ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define Bool
  '((S -> 'T 'F 'p 'q
       ('not S)
       ('andbegin S* 'andend)
       ('orbegin S* 'orend))
    (S* -> ε (S S*))))


(define CFGs
  (list A*/CFG A+/CFG AUB/CFG AUB*/CFG AUB+/CFG AUB•c+*/CFG
        AnBn Bool/SuperSimp Bool/Simp Bool))

(define CNFs (map (λ (x)
                    (begin (displayln (list "testing" x))
                           (CFG->CNF x)))
                  CFGs))

(define (grammar-conversion-tests)
  (and (andmap CFG? CFGs)
       (andmap CNF? CNFs)))






#|



(displayln "starting to construct PDAs")
(define A*-PDA (CFG->PDA 'S (RE->CFG 'S '(a *))))
(define A+-PDA (CFG->PDA 'S (RE->CFG 'S '(a +))))
(define AUB-PDA (CFG->PDA 'S (RE->CFG 'S '(a U b))))
(define AUB*-PDA (CFG->PDA 'S (RE->CFG 'S '((a U b) *))))
(define AUB+-PDA (CFG->PDA 'S (RE->CFG 'S '((a U b) +))))
(define A•B+-PDA (CFG->PDA 'S (RE->CFG 'S '((a • b) +))))
(define cUa•a-PDA (CFG->PDA 'S (RE->CFG 'S '((c U (a • a)) *))))
#;(define AUb•c+*-PDA (CFG->PDA 'S (RE->CFG 'S '((a U ((b • c) +)) *))))

(displayln "constructed PDAs")
(define (set-equal? s1 s2) (andmap (λ (x) (member x s2)) s2))

#;
(Automaton
 'S
 '(F40292)
 '(S40293 S F40292)
 '((S40293 ε S preserve-stack)
   (S a S40293 preserve-stack)
   (S ε S preserve-stack)
   (S ε F40292 preserve-stack))
 '(a)
 '(()))

(define (RE-PDA-tests)
  (let* ((A*-Σ50 (find-words A* 50))
         (A*-PDA-Σ50 (find-words A*-PDA 50))
         (A+-Σ50 (find-words A+ 50))
         (A+-PDA-Σ50 (find-words A+-PDA 50))
         (AUB*-Σ10 (find-words AUB* 3))
         (AUB*-PDA-Σ10 (find-words AUB*-PDA 3))
         (AUB+-Σ10 (find-words AUB+ 3))
         (AUB+-PDA-Σ10 (find-words AUB+-PDA 3)))
    (and (set-equal? A*-Σ50 A*-PDA-Σ50)
         (set-equal? A+-Σ50 A+-PDA-Σ50)
         (set-equal? AUB*-Σ10 AUB*-PDA-Σ10)
         (set-equal? AUB+-Σ10 AUB+-PDA-Σ10))))




;; some CFGs
(define AnBn
  (CFG->PDA
   'S
   '((S -> ε)
     (S -> 'a S 'b))))

(define Bool
  (CFG->PDA
   'S
   '(#;(S -> 'T)
     #;(S -> 'F)
     #;(S -> 'p)
     (S -> 'q)
     (S -> 'not S)
     (S -> 'andbegin S* 'andend)
     (S -> 'orbegin S* 'orend)
     (S* -> ε)
     (S* -> S S*))))


(define (CFG-tests)
  (let ((v1 (find-words AnBn 5))
        (b1 (find-words Bool 4)))
    (and (equal? v1 '(() (a b) (a a b b)))
         (member '(andbegin q andend) b1)
         (not (member '(andbegin q orend) b1)))))


(define run-tests? #f)
(if run-tests?
    (begin
      (if (time (DFA-tests))
          (displayln "DFA-tests passed")
          (error 'testing "DFA-tests failed!!!"))
      (if (time (RE-PDA-tests))
          (displayln "RE-PDA-tests passed")
          (error 'testing "RE-PDA-tests failed!!!"))
      (if (time (CFG-tests))
          (displayln "CFG-tests passed")
          (error 'testing "CFG-tests failed!!!"))
      (displayln "All tests passed"))
    (displayln "tests skipped."))

|#
