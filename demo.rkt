#lang racket

(require rackunit
         "grammars.rkt"
         "G-to-M.rkt"
         "queries.rkt"
         "basics.rkt")

;;;;;;;;;;;;;;;
;; demo + TODOs

#|

TODOs:

-- make renaming better (no gensym)

-- add this step to CFG->CNF consolidation:
             turn
     S1 - epsilon -> S2 -> a -> S3
              to
     S1 -> a -> S3

   where s1 only points to S2, S2

-- add contracts to all the functions IN PRGRESS
   -- basics.rkt done!
   -- automata.rkt done!

-- formalize gramamars in Pie

-- formalize automata in Pie

-- learn about turing machines & implement

;; related to jack's stuff

-- write a query that returns k words starting with a given prefix

-- implement feature generation in MK and compare speed, results
-- experiment with other function groups (call em computation groups?)

   -- Features (filter* • [G: select | group G reduce)] • reduce)
   -- other ideas?

|#






;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hi! I hope you're well.

;; I'm going to talk out loud here and
;; play with an interface to REs, CFGs, CNFs, DFAs, and PDAs.
;; I hope you enjoy! Let me know what doesn't make sense
;; and what you think of the thoughts/quetsions at the end!



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Part 1: Deriving automata
;;;;;;; from regular expressions and grammars
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here I define some Regular Expressions,
;; how show how to:
;; build DFAs that have the language of a provided RE,
;; convert an RE into a CFG then that CFG into CNF
;; build ε-PDAs that are equivalent to a CNF

;; I'll require files as they are needed, so that
;; you know how to poke around if you so desire.
(require "grammars.rkt" "G-to-M.rkt")

(define A* '(a *))
(define AUB '(a U b))
(define C*•D+ '(((c *) • d) +))
(define AUB*•C*•D++ `(((,AUB *) • ,C*•D+) +))

(define A*/DFA (RE->DFA A*))

(define AUB/DFA (RE->DFA AUB))
(define C*•D+/DFA (RE->DFA C*•D+))
(define AUB*•C*•D++/DFA (RE->DFA AUB*•C*•D++))

(define A*/PDA (CNF->PDA (CFG->CNF (RE->CFG A*))))
(define AUB/PDA (CNF->PDA (CFG->CNF (RE->CFG AUB))))
(define C*•D+/PDA (CNF->PDA (CFG->CNF (RE->CFG C*•D+))))
(define AUB*•C*•D++/PDA (CNF->PDA (CFG->CNF (RE->CFG AUB*•C*•D++))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Part 2: Using automata
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; if you check out "queries.rkt", you'll see that each query
;; makes a call with higher-order arguments to a macro called
;; run, which is defined in "basics.rkt". I'll talk
;; about run later in the doc.


(require "queries.rkt")

;; we can ask machines if they accept a certain word.
;; words are lists of symbols (or numbers), and
;; the empty word is '() , (not ε)

(check-equal? #t (accept? A*/DFA '()))
(check-equal? #t (accept? A*/PDA '()))
(check-equal? #f (accept? AUB/DFA '()))
(check-equal? #t (accept? AUB*•C*•D++/DFA '(a a c d c c d c c d)))
(check-equal? #t (accept? AUB*•C*•D++/DFA '(a a c d c c d c c d)))
(check-equal? #t (accept? AUB*•C*•D++/DFA '(a a c d c c d c c d b a d)))
(check-equal? #t (accept? AUB*•C*•D++/PDA '(a a c d c c d c c d b a d)))
(check-equal? #f (accept? AUB*•C*•D++/DFA '(a a c d c c d c c b a a)))
(check-equal? #f (accept? AUB*•C*•D++/PDA '(a a c d c c d c c b a a)))

;; we can ask machines to tell us k words in their language
;; using take-words : M x Nat -> L(M)
;; (but we only like to treat these outputs as sets)

;; (I made my own poor-man's set-equal? (called set-equal??)
;; because the Racket function with the same name gave me issue.)

(define (check-set-equal? s1 s2)
  (if (set-equal?? s1 s2)
      (displayln "test passed")
      (error 'check-set-equal?
             (format "The two sets ~s and ~s are not the same."
                     s1 s2))))

(check-set-equal? (remove '() (take-words A*/DFA 10))
                  (take-words (RE->DFA '(a +)) 9))
(check-set-equal? '((a) (b))
                  (set-intersection
                   (take-words AUB/DFA 10)
                   (take-words (RE->DFA `(,AUB *)) 10)))


;; we can also ask machines to give us all of the words
;; in their language up to a certain length
;; using find-words : M x Nat -> L(M)

(check-set-equal?
 (find-words AUB/PDA 4)
 (find-words AUB/DFA 4))

(check-set-equal?
 (find-words AUB*•C*•D++/PDA 4)
 (find-words AUB*•C*•D++/DFA 4))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Part 3: Examples with CFGS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Here are some honest-to-goodness PDAs made from CFGs

;; In these CFGs, the production rule in the car of the grammar
;; is assumed to represent the 'complete sentence' of the grammar,
;; as we would intend on paper


;; needs no explanation
(define AnBn '((S -> ε ('a S 'b))))
(define AnBn/CNF (CFG->CNF AnBn))
(define AnBn/PDA (CNF->PDA AnBn/CNF))


;; boolean grammar with 2 variables p and q,
;; with begin/end tokens since words need to be flat lists.

(define Bool
  '((S -> 'T 'F 'p 'q
       ('not S)
       ('andbegin S* 'andend)
       ('orbegin S* 'orend))
    (S* -> ε (S S*))))

(define Bool/CNF (CFG->CNF Bool))
(define Bool/PDA (CNF->PDA Bool/CNF))


;; describes tautologies (with no variables)

(define Val-of
  '((True ->
          'T
          ('not False)
          ('andbegin True* 'andend)
          ('orbegin Value* True Value* 'orend))
    (False ->
           'F
           ('not True)
           ('andbegin Value* False Value* 'andend)
           ('orbegin False* 'orend))
    (Value ->  True False)
    
    (False* -> ε (False False*))
    (True* -> ε (True True*))
    (Value* -> ε (Value Value*))))

(define Val-of/CNF (CFG->CNF Val-of))
(define Val-of/PDA (CNF->PDA Val-of/CNF))


(check-equal?
 #t
 (subset? (take-words Val-of/PDA 7)
          (find-words Bool/PDA 3)))

;; take-words, if you know the right k, generally finds the same
;; set as find-words and quits MUCH faster, so I will use
;; different calls to keep things moving


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Part 4: Now, talking about run.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
The macro run provides a foldl-like algorithm
through which to traverse an automaton
parameterized by things like
-- "what are our termination conditions?"
-- "do we have a specific word in mind or spamming Σ?"
-- "what kind of thing are we trying to get out of this search,
    a boolean? a list of words?"

You have an accumulator (à la State monad) that you get to use in
any way that you want,
so I think that pretty much whatever you'd want to do along
the way you have the means to using run, but I have no proof of that.
:)

Run is a frontier-based search algorithm, where an automaton's transition
function allows us to add new states to our frontier.

A 'state' is a 3-tuple with an automaton state,
a stack, and an accumulator.

|#

#|
After defining and refining run a good deal, I
started working with a friend on a project inspired by a paper
that he had read where they use automata to generate
programs within a filter-map-reduce paradigm
 (which they call features)
that can be used to reduce large database.
They generate lots of features and hand them to a neural
network that learns what kind of features are more useful
for making predictions in the future.

It doesn't really matter what they did right now.
(and their formalization was...not quite right... in a lot of ways)

but we've been trying to replicate their work (but with a better
formalization) and so I really wanted to make my back-end fast!
|#



#|
Here is the series of improvements that I made to run, and
the last few surprised me in being hugely effective, and have made
my search algorithm more similar to minikanren's interleaving DFS
in a cool way. (I think)


-- represented δ as a hashtable instead of a list
   (easy enough, and unsurprisingly effective)


-- Next, it starts getting more fun.

   I split the frontier into TWO frontiers:
     one that holds states where the last transition was
         on reading a symbol,
        (I'll call this the state-frontier or Fs),  and
     one that holds states where the last transition was
         on an ε (I'll call this the ε-frontier or Fε)

   And then the first algorithm change now that
   the two kinds of transitions are exposed is that
   states in Fε are only expanded when Fs is empty.
   Both frontiers, though, are still treated as queues
   and so we can loosely think of this as BFS.

   This change has a big improvement of take-word queries
   (but for obvious reasons doesn't change as much for find-word
   queries)


-- And finally, the simplest and surprisingly significant change
   was in changing Fε from a queue to a stack.

  (a query to take 1000 words that took 15 minutes
   now only takes 3 minutes) was in changing Fε from a queue to a stack.
   
Am I correct in thinking that this search strategy, where

 --- states arrived at by epsilon transitions are
     only expanded when there are no available states
     from symbol transitions
 --- state transitions are explored in BFS order
 --- epsilon transitions are explored in DFS order


is similar or even isomorphic to miniKanren's interleaving DFS?
It feels right and seems like an interesting result. 

|#

;; 







