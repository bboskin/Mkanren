#lang racket

(require "basics.rkt"
         "queries.rkt"
         "grammars.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; There's a very special and important mathemagical object, called the finite-state automaton.


;; We have a definition to define NPDAs with as many stacks as we want (so including NFA's), but as of now there are no ϵ-transitions
;; since we don't need em! And if you don't know what that or any of this means yet, don't worry!

;; Automatons have states and transitions.
;; If you know what a graph is, states are like nodes and transitions are like edges.
;; We can draw them both graphs and automata on paper in similar ways.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; We're going to define an automaton that represents the bay area.
;; (defined below with the name East-Bay)
;; (This is a fairly simple automaton, if you have any expectations, but we'll have more going on soon enough.)

;; Here are some technical properties about this machine,
;; to serve as an example of the terminology
;; (in this doc I'll sometimes call automata machines)

;; The language (Σ = {'to-el-cerrito 'to-albany 'to-berkeley 'to-oakland})
;; of this machine has four elements.

;; The automaton and its transitions can be drawn graphically as:

#|
                                        | 
                                        v
                       El-Cerrito <-> Albany <-> Berkeley <-> [Oakland]



|#

;; Each state 'represents' an East Bay City, the states together are represented by East-Bay-Cities below.
;; The start state (the entry point to the automaton) is Albany.

;; There is one final state, Oakland. We'll use brackets [] in diagrams to notate final states.
;; Final states describe the words that an automaton accepts. (Those words are a subset of all possible orderings of letters in the alphabet Σ)
;; If you can transition to a final state when a word w ends, then w is part of the language of the automaton.
;; Automata can have any number of final states. Automata with 0 final states don't accept any words (Σ = {}).

;; We can use the automaton below (as it's defined right now) to verify and
;; discover paths from Albany to Oakland. But we can, and will, change it up!

(define East-Bay-Language-Symbols '(to-berkeley to-oakland to-albany to-el-cerrito))
(define East-Bay-Cities '(El-Cerrito Albany Berkeley Oakland))
(define East-Bay-Start-State 'Albany)
(define East-Bay-Final-States '(Oakland))

;; we also define a few functions here for shorthand in the machine's definition
;; (and we'll keep writing functions to recognize other symbols similar to these throughout the doc)
(define path-to-berk? (λ (x) (eqv? x 'to-berkeley)))
(define path-to-oak? (λ (x) (eqv? x 'to-oakland)))
(define path-to-alb? (λ (x) (eqv? x 'to-albany)))
(define path-to-e-c? (λ (x) (eqv? x 'to-el-cerrito)))

;; Here's the automaton!
(define East-Bay
  (Automaton
   East-Bay-Start-State
   East-Bay-Final-States
   East-Bay-Cities
   `((Albany ,path-to-e-c? El-Cerrito)
     (El-Cerrito ,path-to-alb? Albany)
     (Albany ,path-to-berk? Berkeley)
     (Berkeley ,path-to-alb? Albany)
     (Berkeley ,path-to-oak? Oakland)
     (Oakland ,path-to-berk? Berkeley))
   East-Bay-Language-Symbols
   '()))

;; the transitions are set up such that
;; each transition that can be taken on reading the symbol 'to-_state_ point at _state.
;; For example, there is a transition from Albany to El-Cerrito on reading the symbol 'to-el-cerrito.
;; There are six total transitions, each of which is one-direction.

;; You can read the direction `(S1 ,when? S2) meaning that you can go from state S1 to state S2 when the
;; current input letter satisfies the question when? (and you're at S1)

;; Words in the language are possible paths.
;; Some of those paths can be traversed on the automaton.
;; Some of the traversible paths lead to Oakland.
;; Some of the traversible paths can start from Albany.

;; The words that can take us from Albany to Oakland are the words accepted by the machine.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Asking an automata if it accepts or rejects a word
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we represent words as lists of symbols like '(), '(apple dog), or '(to-el-cerrito to-albany to-albany)

;; something we might want to ask is: is this a word recognized by the automaton?

;; some examples of possible words. Do you think that any of these words are accepted by the East Bay automaton?
;; Run the program and then look at the variable East-Bay-Words once you've thought about it!
;; (by typing East-Bay-Words below and press enter)

(define path1 '(to-el-cerrito))
(define path2 '(to-albany to-albany to-albany to-berkeley to-oakland))
(define path3 '())
(define path5 '(to-oakland))
(define path4 '(to-berkeley to-berkeley to-berkeley))
(define path6 '(to-berkeley to-albany to-el-cerrito))
(define path7 '(to-el-cerrito to-albany to-berkeley to-oakland))
(define path8 '(to-berkeley to-oakland))
(define path9 '(to-berkeley to-albany to-berkeley to-albany to-el-cerrito to-albany to-berkeley to-oakland))

(define paths `(,path1 ,path2 ,path3 ,path4 ,path5 ,path6 ,path7 ,path8 ,path9))

(define East-Bay-Words (filter (λ (w) (accept? East-Bay w)) paths))

;; the function test-input, used above, takes a machine M and a single word w,
;; and returns true (#t) or false (#f) depending on whether or not M accepts w.


;; If we want to find out ALL of the words in a language (up to a certain length)
;; we can use the function find-words, and give it an automaton and a number (the max length of word)

;; check out these variables! Check out more on your own!
;; if you're curious on just how many words there are up to a certain size, use the length function (shown below)

(define East-Bay-5 (find-words East-Bay 6))
(define East-Bay-5-number (length East-Bay-5))


;; Now, let's revisit the East Bay Automaton.
;; Look at the following few values:
(define East-Bay-1 (find-words East-Bay 1))
(define East-Bay-2 (find-words East-Bay 2))
(define East-Bay-3 (find-words East-Bay 3))
(define East-Bay-4 (find-words East-Bay 4))

;; we notice that East-Bay-1 has no members,
;; and that East-Bay-2 and East-Bay-3 are the same
;; (there are not paths between Albany and Oakland that take exactly three steps.

;; Finish the new automaton below by deciding its start state and its final state(s)
;; so that the values below it are all non-empty and unique. There are lots of ways to do this

(define East-Bay2
  (Automaton
   'TODO ;; replace TODO with a city! (ex: 'Albany)
   '(TODO) ;; Put One (or more) cities here! (ex: '(El-Cerrito Oakland))
   East-Bay-Cities
   `((Albany ,path-to-e-c? El-Cerrito)
     (El-Cerrito ,path-to-alb? Albany)
     (Albany ,path-to-berk? Berkeley)
     (Berkeley ,path-to-alb? Albany)
     (Berkeley ,path-to-oak? Oakland)
     (Oakland ,path-to-berk? Berkeley))
   East-Bay-Language-Symbols
   '()))

(define East-Bay2-1 (find-words East-Bay2 1))
(define East-Bay2-2 (find-words East-Bay2 2))
(define East-Bay2-3 (find-words East-Bay2 3))
(define East-Bay2-4 (find-words East-Bay2 4))


