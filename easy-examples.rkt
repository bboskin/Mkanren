#lang racket

(require "automata.rkt")
(provide (all-defined-out))


;; In this document, we play with an intellectual exercise,
;; tackling satisfiability and model discovery
;; with finite-state automata.
;; (TODO) in the document automata.pie we explore a similar® exercise and related proofs with dependent types in Pie.

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

;; Now, let's check out some more typical automata!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DFA's and Regular Expressions


;; There is a class of languages called Regular Expressions (REs) that can be represented
;; by letters and just a few operators. All REs can be accepted by a certain kind of automaton!
;; These automata are called Deterministic Finite Automata (DFA).
;; DFAs do not have any stacks. Since the East didnt use a stack, it was a DFA as well.

;; (technically many of these (not East Bay) are actually NFAs, (non-determinant)
;; for reasons that don't matter for all. It just makes the automata simpler
;; Later we'll use non-determinism in a more significant way and we can talk about what happened
;; and why it matters!


;; Before getting into DFAs, here are a few examples of RE's and examples of what they mean.
;; U means either one of the things on either side. (union)
;; * means repeat the RE within 0 or more times
;; + means repeat the RE within 1 or more times
;; order with no symbol in between just means order (concatenation)

;; after the first two RE's, all the languages are actually infinitely long

#|
a U b U c = "a", "b", "c"
acdc U bc = "acdc", "bc"
a* = "", "a", "aa", "aaa", ..., "aaaaaaaa", ...
a+ = "a", "aa", "aaa", ..., "aaaaaaaa", ...
[a U b]* = "", "a", "b", "aba", "baabababaa", ...
[a+ U b]* = "", "b", "aaaa", "abaabaaabaaa", ...
b [a U b]* d* = "b", "baaaa", "bad", "babababababaabababbabaababbadddddddd", ...

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; here are some DFA's corresponding to RE's! They are defined in the same way
;; as the Easy Bay automaton (which is also a DFA. These are all DFAs because they don't have any stacks!),
;; and the name of the DFA should be a clue of the
;; RE that they represent.

;; some helper functions/constants do make automata transitions more readable

(define Alphabet '(a b c d e f g h i j k l m n o p q r s t u v w x y z))

(define is-a? (λ (x) (eqv? x 'a)))
(define is-b? (λ (x) (eqv? x 'b)))
(define is-c? (λ (x) (eqv? x 'c)))
(define is-d? (λ (x) (eqv? x 'd)))

;; now, we have a simple language.
;; This automaton recognizes and accepts strings of 0 or more a's,
;; and rejects all other strings using alphabet letters.
(define A*
  (Automaton
   'S
   '(S)
   '(S)
   `((S ,(λ (x) (eqv? x 'a)) S))
   Alphabet
   '()))

#|              
               ___
              |   |a
              v   |
            ->[S]-

|#

;; this automaton also recognizes strings of 0 or more a's
;; the definition is silly because it describes the same language
;; as A* above, and has a bunch of unecessary states.

(define A*-silly
  (Automaton
   'S
   '(S A)
   '(S A B C D E F)
   `((S ,(λ (x) (eqv? x 'a)) A)
     (A ,(λ (x) (eqv? x 'a)) A))
   Alphabet
   '()))
#|

                    ___
                   |   |a
                a  v   |
          ->[S]--->[A]-

|#
;; recognizes strings of 1 or more a's followed by 0 or more b's
(define A+B*
  (Automaton
   'S
   '(A B)
   '(S A B)
   `((S ,is-a? A)
     (A ,is-a? A)
     (A ,is-b? B)
     (B ,is-b? B))
   Alphabet
   '()))

;; recognizes either 0 or more A's or zero or more B's (no mixes)
(define A*UB*
  (Automaton
   'S
   '(S A B)
   '(S A B)
   `((S ,is-a? A)
     (A ,is-a? A)
     (S ,is-b? B)
     (B ,is-b? B))
   Alphabet
   '()))

;; a bigger, weirder example
;; (but can we simplify this RE without changing its meaning,
;; without needing to change the automaton?)
(define |A+UB|*|CUB|+
  (Automaton
   'S
   '(F)
   '(S F)
   `((S ,is-b? S)
     (S ,is-a? S)
     (S ,is-b? F)
     (S ,is-c? F)
     (F ,is-b? F)
     (F ,is-c? F))
   Alphabet
   '()))


;; To confirm that these automata are correct, use the function
;; valid-input? with an automaton and a word to see if they accept
;; words or not correctly. Check out the following tests (one at a time) after thinking about them.

(define RE-tests
  (begin
    (accept? A* '())
    (accept? A* '(a))
    (accept? A* '(a a a a))
    (accept? A* '(a a a a b))
    (accept? A+B* '())
    (accept? A* '(a))
    (accept? A+B* '(a a a a))
    (accept? A+B* '(a a a a b))
    (accept? A+B* '(b b b b))
    (accept? A+B* '(b a a a a a))
    (accept? A*UB* '())
    (accept? A*UB* '(a a a a a))
    (accept? A*UB* '(a b a b a b a))
    (accept? A*UB* '(b))
    (accept? A*UB* '(b b b b b))
    (accept? |A+UB|*|CUB|+ '(a a a b a b a b b c b c b c b))))


;; TODO: make one really nuts RE with examples

;; If we want to find out ALL of the words in a language (up to a certain length)
;; we can use the function find-words, and give it an automaton and a number (the max length of word)

;; check out these variables! Check out more on your own!
;; if you're curious on just how many words there are up to a certain size, use the length function (shown below)

(define A*-5 (find-words A* 5))
(define A*UB*-5 (find-words A*UB* 5))
(define A+B*-5 (find-words A+B* 5))
(define A+B*-100-number (length (find-words A+B* 100)))
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

;;;;;;;;;;;;;;;;
;; CFGs and PDAs

;; Now we'll look at some more interesting languages: Context-Free Grammars (CFGs)
;; All RE's are CFGs, and more languages are as well.

;; I'm not going to give a formal definition of them, but 
;; They generally involve needing to repeat something in a way that RE's can't capture.
;; The 'repeating something' needs memory, and so the automata
;; that describe CFGs have are a DFA with a stack, and are called Push-Down Automata (PDAs).

;; a stack is a data structure where you can add values, and can only access the most recently
;; added value. (they are LIFO -- last in, first out. or FILO, if you like -- first in, last out)

;; I'm not going to talk much more PDAs because this isn't a lecture. Look them up!


;; recognizes strings of a's followed by strings of b's, with the same number of a's and b's
;; (this is what we first need a stack for,
;; to keep track of how many a's we had to know how
;; many b's we'll need)
(define AnBn
  (Automaton
   'S
   '(S B)
   '(S A B)
   `((S ,is-a? A (pop on #f push (a #f)))
     (A ,is-a? A (pop on a push (a a)))
     (A ,is-b? B (pop on a push ()))
     (B ,is-b? B (pop on a push ())))
   Alphabet
   '((a))))

;; a bigger example -- k a's, 0 or more c's, then k b's, then 1 or more a's
(define AnC*BnA+
  (Automaton
   'S
   '(F)
   '(A C B F)
   `((S ,is-a? A (pop on #f push (a #f)))
     (S ,is-a? F (pop on #f push (#f)))
     (S ,is-c? C (pop on #f push (#f)))
     (A ,is-a? A (pop on a  push (a a)))
     (A ,is-b? B (pop on a  push ()))
     (A ,is-c? C (pop on a  push (a)))
     (C ,is-c? C (pop on a  push (a)))
     (C ,is-c? C (pop on #f push (#f)))
     (C ,is-b? B (pop on a  push ()))
     (C ,is-a? F (pop on #f push (#f)))
     (B ,is-b? B (pop on a  push ()))
     (B ,is-a? F (pop on #f push (#f)))
     (F ,is-a? F (pop on #f push (#f))))
   Alphabet
   '((a))))

;; experiment with these two automata, using
;; the functions (accept? M w) and (find-words M k)


;; Once you feel like you understand what each automaton means,
;; expand the window below and run (find-words AnC*BnA+ 30) for a cool pattern.


;; Excercise: make an automaton to recognize all palindromes with Σ={a,b,c}.
;; think about if you can do it without using any stacks!

(define Palindromes
  (Automaton
   'TODO
  '(TODO)
  '(TODO)
  '() ;; TODO
  '(a b c)
  '() ;; TODO
  ))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boolean Algebra is a CFG

;; Boolean Expressions, for our purposes,
;; are expressions that use:
;; variable names (p, q, r, s)
;; not
;; and, or

;; A boolean expression is either valid, satisfiable, or unsatisfiable
;; The judgment of satisfiablity comes from whether or not the variables
;; can be assigned in a way that makes the expression true.

;; Here are some examples of boolean expressions and their satisfiability

;; p                                    satisfiable but not valid: True if p=T, False if p=F
;; p and not p                          unsatisfiable: False if p=T, False if p=F
;; p or not p                           valid: True if p=T, True if p=F
;; (not (p or q)) and (p and q)         unsatisfiable: False in all cases p,q=T; p=T,q=F; p=F,q=T; q=F,q=F
;; (not (not (p or q)) and (p and q))   valid: True in all cases p,q=T; p=T,q=F; p=F,q=T; q=F,q=F
;;                                      (this is just the negation of the previous expression)

;; I'm not going to talk about truth tables here, but look them up if you want to see more
;; about how to reason about boolean expressions


;; We can write the grammar of boolean expressions using a PDA!
;; because we don't have parentheses, we have to write expressions a little more tediously,
;; explicitly beginning and closing every and/or. BUT, here's a PDA:

(define Logic-Terms '(p q r not andbegin andend orbegin orend))

(define var? (λ (x) (memv x '(p q r))))
(define not? (λ (x) (eqv? x 'not)))

(define andbegin? (λ (x) (eqv? x 'andbegin)))
(define andend? (λ (x) (eqv? x 'andend)))

(define orbegin? (λ (x) (eqv? x 'orbegin)))
(define orend? (λ (x) (eqv? x 'orend)))

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

