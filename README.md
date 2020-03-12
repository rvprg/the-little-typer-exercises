# the-little-typer-exercises

```
;; p.xii
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

;; p.16
;; list of atoms
(define lat?
  (lambda (l)
    (cond
      ((null? l) #t)
      ((atom? (car l)) (lat? (cdr l)))
      (else #f))))

;; write a length function
;; (mylength '('a 'b 'c)) => 3

(define (mylength l)
  (define (len l c)
    (cond
      ((pair? l) (len (cdr l) (+ 1 c)))
      (c)))
  (len l 0))

;; write an iota function
;; (iota 2 6) => '(2, 3, 4, 5, 6)
(define (iota s e)
  (define (it e l)
    (if (< e s) l (it (- e 1) (cons e l))))
  (it e '()))

;; write a function to check membership
;; (member? 'a '(a b c)) => #t
;;
;; What's the value of (member? 'a '('a 'b 'c)) ?
(define (member? e l)
  (if (pair? l)
      (if (equal? e (car l))
          #t
          (member e (cdr l)))
      #f))

;; write a function to remove the first occurance of a member from a list
;; (rember 'a '(a b c a)) => '(b c a)

(define (rember e l)
  (if (pair? l)
      (if (equal? e (car l))
          (cdr l)
          (cons (car l) (rember e (cdr l))))
      l))  

;; write a function insertR that inserts an atom
;; to the right of another in a list
;;  (insertR '(c b b) 'b 'a) => '(c b a b)

(define (insertR l p e)
  (if (pair? l)
      (if (equal? p (car l))
          (cons (car l) (cons e (cdr l)))
          (cons (car l) (insertR (cdr l) p e)))
      l))  

;; write a function insertL that inserts an atom to the left
;; of another in a list
;;  (insertL '(c b b) 'b 'a) => '(c a b b)
(define (insertL l p e)
  (if (pair? l)
      (if (equal? p (car l))
          (cons e l)
          (cons (car l) (insertL (cdr l) p e)))
      l))

;; write a function that replaces the first occurance of
;; an atom in a list with another
;;  (subst 'z 'a '(a b c)) => '(z b c)
(define (subst e p l)
  (if (pair? l)
      (if (equal? p (car l))
          (cons e (cdr l))
          (cons (car l) (subst e p (cdr l))))
      l))

;; write a function that removes all occurances of an
;; atom from a list
;;  (multirember 'a '(a b a c)) => '(b c)
(define (multirember e l)
  (if (pair? l)
      (if (equal? e (car l))
          (rember e (cdr l))
          (cons (car l) (rember e (cdr l))))
      l))

;; write a function insertR that inserts an atom
;; to the right of all occurances of another in a list
;;  (multiinsertR 'z 'a '(a b a c a)) => '(a z b a z c a z)
(define (multiinsertR e p l)
  (if (pair? l)
      (if (equal? p (car l))
          (cons (car l) (cons e (multiinsertR e p (cdr l))))
          (cons (car l) (multiinsertR e p (cdr l))))
      l))

;; write a function multisubst that replaces all occurances
;; of an atom with another in a list
;;  (multisubst 'z 'a '(b c a z d a)) => '(b c z z d z)
(define (multisubst e p l)
  (if (pair? l)
      (if (equal? p (car l))
          (cons e (multisubst e p (cdr l)))
          (cons (car l) (multisubst e p (cdr l))))
      l))

(define add1
  (lambda (n)
    (+ n 1)))

(define sub1
  (lambda (n)
    (- n 1)))

;; write a function o+ that adds two numbers (using add1, sub1)
;;  (o+ 2 3) => 5
(define (o+ a b)
  (if (= b 0)
      a
      (o+ (add1 a) (sub1 b))))

;; write a function o- that subtract two numbers (using add1, sub1)
;;  (o- 3 2) => 1
(define (o- a b)
  (if (= b 0)
      a
      (o- (sub1 a) (sub1 b))))

;; write a function that adds all the numbers in a tuple
;;  (addtup '(1 2 3)) => 6
(define (addtup l)
  (define (it sum l)
    (if (pair? l)
        (o+ (car l) (it sum (cdr l)))
        sum))
  (it 0 l))

;; write a function to multiply two numbers
;;  (ox 2 3) => 6
(define (ox a b)
  (define (it b acc)
    (if (= b 0)
        acc
        (it (sub1 b) (o+ acc a))))
  (it b 0))
      
;; write a function which defines 'greater than' for two numbers
;;  (> 2 3) => #f
(define (greater_than a b)
  (if (and (not (= a 0)) (not (= b 0)))
      (greater_than (sub1 a) (sub1 b))
      (and (not (= a 0)) (= b 0))))
```

```
#lang pie

;; Exercises on using Nat elimiators from Chapter 3 of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University

;; Exercise 3.1
;;
;; Define a function called at-least-two? that takes one Nat argument and evaluates to an Atom.
;;
;; at-least-two? evaluates to 't if the Nat is greater than or equal to 2 otherwise it evaluates to 'nil.
;;
;; Note: The only Nat eliminator you should need in the body of at-least-two? is which-Nat.

(claim at-least-two?
  (-> Nat Atom))
       
(define at-least-two?
  (λ (x)
    (which-Nat x
      'nil
      (λ (x) (which-Nat x
               'nil
               (λ (x) (which-Nat x
                        't
                        (λ (x) 't))))))))

;; Exercise 3.2
;;
;; Rewrite the definition of + (in frame 3.27) using the rec-Nat eliminator instead of the iter-Nat eliminator.
(claim +
  (-> Nat Nat Nat))

(claim step-+
  (-> Nat Nat Nat))

(define step-+
  (λ (n-1 step_n-1)
    (add1 step_n-1)))

(define +
  (λ (n j)
    (rec-Nat n
      j
      step-+)))


;; Exercise 3.3
;;
;; Define a function called exp that takes two Nat arguments and evaluates to a Nat.
;;
;; exp evaluates to the exponentiation, a^b, of the two passed arguments.

(claim *
  (-> Nat Nat Nat))

(claim step-*
  (-> Nat Nat Nat Nat))

(define step-*
  (λ (b n-1 step_n-1)
    (+ b step_n-1)))

(define *
  (λ (a b)
    (rec-Nat a
      0
      (step-* b))))

(claim exp
  (-> Nat Nat Nat))

(claim step-exp
  (-> Nat Nat Nat Nat))

(define step-exp
  (λ (a n-1 step_n-1)
    (* a step_n-1)))

(define exp
  (λ (a b)
    (rec-Nat b
      1
      (step-exp a))))

;; Exercise 3.4
;;
;; Define a function called max that takes two Nat arguments and evaluates to a Nat.
;;
;; max evaluates to the larger of the two passed arguments.

(claim dec
  (-> Nat Nat))

(define dec
  (λ (x)
    (which-Nat x
      0
      (λ (x) x))))

(claim max
  (-> Nat Nat Nat))

(claim mon
  (-> Nat Nat Nat))

(define mon
  (λ (a b)
    (iter-Nat b
      a
      (λ (x) (dec x)))))

(define max
  (λ (a b)
    (which-Nat (mon a b)
      b
      (λ (x) a))))
```

```
;; Exercises on Pi types and using the List eliminator from Chapters 4 and 5
;; of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University


;; Exercise 4.1
;;
;; Extend the definitions of kar and kdr (frame 4.42) so they work with arbirary
;; Pairs (instead of just for Pair Nat Nat).

(claim elim-Pair
  (Pi ((A U)
       (D U)
       (X U))
    (-> (Pair A D)
        (-> A D
            X)
        X)))

(define elim-Pair
  (λ (A D X)
    (λ (p f)
      (f (car p) (cdr p)))))

(claim kar
  (Pi ((E U))
    (-> (Pair E E) E)))

(claim kdr
  (Pi ((E U))
    (-> (Pair E E) E)))

(define kar
  (λ (E)
    (λ (p)
      (elim-Pair
        E E E p (λ (a d) a)))))

(define kdr
  (λ (E)
    (λ (p)
      (elim-Pair
        E E E p (λ (a d) d)))))
```