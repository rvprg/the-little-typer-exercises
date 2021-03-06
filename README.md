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
        
;; Exercise 4.2
;;
;; Define a function called compose that takes (in addition to the type
;; arguments A, B, C) an argument of type (-> A B) and an argument of
;; type (-> B C) that and evaluates to a value of type (-> A C), the function
;; composition of the arguments.

(claim compose
  (Pi ((A U)
       (B U)
       (C U))
    (-> (-> A B) (-> B C) (-> A C))))

(define compose
  (λ (A B C)
    (λ (f g)
      (λ (x) (g (f x))))))

;; Exercise 5.1
;;
;; Define a function called sum-List that takes one List Nat argument and
;; evaluates to a Nat, the sum of the Nats in the list.

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

(claim sum-List
  (-> (List Nat) Nat))

(define sum-List
  (λ (l)
    (rec-List l
      0
      (λ (e _ s) (+ e s)))))

;; Exercise 5.2
;;
;; Define a function called maybe-last which takes (in addition to the type
;; argument for the list element) one (List E) argument and one E argument and
;; evaluates to an E with value of either the last element in the list, or the
;; value of the second argument if the list is empty.

(claim step-append
  (Π ((E U))
    (-> E (List E) (List E) (List E))))

(define step-append
  (λ (E)
    (lambda (e es appendes)
      (:: e appendes))))

(claim snoc
  (Pi ((E U))
    (-> (List E) E
      (List E))))

(define snoc
  (lambda (E)
    (lambda (start e)
      (rec-List start
        (:: e nil)
        (step-append E)))))

(claim reverse
  (Pi ((E U))
    (-> (List E) (List E))))

(claim step-reverse
  (Pi ((E U))
    (-> E (List E) (List E) (List E))))

(define step-reverse
  (λ (E)
    (λ (e es reversees)
      (snoc E reversees e))))

(define reverse
  (λ (E)
    (λ (l)
      (rec-List l
        (the (List E) nil)
        (step-reverse E)))))

(claim maybe-last
  (Pi ((E U))
    (-> (List E) E E)))

(define maybe-last
  (λ (E)
    (λ (l e)
      (rec-List (reverse E l)
        e
        (λ (x _ _)
          x)))))

;; Exercise 5.3
;;
;; Define a function called filter-list which takes (in addition to the type
;; argument for the list element) one (-> E Nat) argument representing a
;; predicate and one (List E) argument.
;;
;; The function evaluates to a (List E) consisting of elements from the list
;; argument where the predicate is true.
;;
;; Consider the predicate to be false for an element if it evaluates to zero,
;; and true otherwise.

(claim filter-list
  (Pi ((E U))
    (-> (List E) (-> E Nat) (List E))))

(define filter-list
  (λ (E)
    (λ (l p)
      (rec-List l
        (the (List E) nil)
        (λ (e es s)
          (which-Nat (p e)
            s
            (λ (_) (:: e s))))))))

;; Exercise 5.4
;;
;; Define a function called sort-List-Nat which takes one (List Nat) argument
;; and evaluates to a (List Nat) consisting of the elements from the list
;; argument sorted in ascending order.
        
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

(claim head-Nat
  (-> (List Nat) Nat))

(define head-Nat
  (λ (l)
    (rec-List l
      0
      (λ (s _ _) s))))

(claim tail-Nat
  (-> (List Nat) (List Nat)))

(define tail-Nat
  (λ (l)
    (rec-List l
      (the (List Nat) nil)
      (λ (_ es _) es))))
      
(claim insert-Nat
  (-> (List Nat) Nat (List Nat)))

(define insert-Nat
  (λ (l n)
    (rec-List l
      (:: n nil)
      (λ (s _ rec)
        (which-Nat (mon (head-Nat rec) s)
          (:: (head-Nat rec) (:: s (tail-Nat rec)))
          (λ (_) (:: s rec)))))))

(claim sort-List-Nat
  (-> (List Nat) (List Nat)))

(define sort-List-Nat
  (λ (l)
    (rec-List l
      (the (List Nat) nil)
      (λ (s _ rec)
        (insert-Nat rec s)))))

```

```
#lang pie

;; Exercises on Vec and ind-Nat from Chapters 6 and 7 of The Little
;; Typer

(claim +
  (-> Nat Nat
    Nat))

(define +
  (λ (a b)
    (rec-Nat a
      b
      (λ (a-k b+a-k)
        (add1 b+a-k)))))

;; Exercise 7.0
;;
;; Define a function called zip that takes an argument of type (Vec A n) and a
;; second argument of type (Vec B n) and evaluates to a vlue of type (Vec (Pair A B) n),
;; the result of zipping the first and second arguments.

(claim zip
  (Pi ((A U)
       (B U)
       (n Nat))
    (-> (Vec A n) (Vec B n) (Vec (Pair A B) n))))

(claim zip-motive
  (Pi ((A U)
       (B U)
       (n Nat))
    U))

(define zip-motive
  (λ (A B n)
    (-> (Vec A n) (Vec B n) (Vec (Pair A B) n))))

(claim zip-step
  (Pi ((A U)
       (B U)
       (n Nat))
    (-> (zip-motive A B n)
      (zip-motive A B (add1 n)))))

(define zip-step
  (λ (A B n)
    (λ (zip_n-1)
      (λ (v1 v2)
        (vec:: (cons (head v1) (head v2)) (zip_n-1 (tail v1) (tail v2)))))))

(define zip
  (λ (A B n)
    (ind-Nat n
      (zip-motive A B)
      (λ (_ _) (the (Vec (Pair A B) zero) vecnil))
      (zip-step A B))))

(check-same (Vec (Pair Nat Atom) 0) 
  (zip Nat Atom 0 vecnil vecnil)
  vecnil)

(check-same (Vec (Pair Nat Atom) 2) 
  (zip Nat Atom 2 (vec:: 1 (vec:: 2 vecnil)) (vec:: 'a (vec:: 'b vecnil)))
  (vec:: (cons 1 'a) (vec:: (cons 2 'b) vecnil)))
  
;; Exercise 7.1
;;
;; Define a function called append that takes an argument of type (Vec E n) and an
;; argument of type (Vect E m) and evaluates to a value of type (Vec (+ n m)), the
;; result of appending the elements of the second argument to the end of the first.

(claim append
  (Π ([E U]
      [m Nat]
      [n Nat])
    (-> (Vec E m) (Vec E n)
      (Vec E (+ n m)))))

(claim append-motive
  (Pi ((E U)
       (m Nat)
       (n Nat))
    U))

(define append-motive
  (λ (E m n)
    (-> (Vec E m) (Vec E n)
      (Vec E (+ n m)))))

(claim append-step
  (Pi ((E U)
       (m Nat)
       (n Nat))
    (-> (append-motive E m n)
      (append-motive E m (add1 n)))))

(define append-step
  (λ (E m n)
    (λ (append_n-1)
      (λ (v1 v2)
        (vec:: (head v2) (append_n-1 v1 (tail v2)))))))

(claim append-base
  (Pi ((E U)
       (m Nat))
    (append-motive E m 0)))

(define append-base
  (λ (E m)
    (λ (v1 v2) v1)))

(define append
  (λ (E m n)
    (ind-Nat n
      (append-motive E m)
      (append-base E m)
      (append-step E m))))

(check-same (Vec Atom 5)
  (append Atom 2 3
    (vec:: 'a (vec:: 'b vecnil))
    (vec:: 'c (vec:: 'd (vec:: 'e vecnil))))
  (vec:: 'c (vec:: 'd (vec:: 'e (vec:: 'a (vec:: 'b vecnil))))))

;; Exercise 7.2
;;
;; Define a function called drop-last-k that takes an argument of type (Vec E ?) and
;; evaluates to a value of type (Vec E ?), the result of dropping the last k elements
;; from the first argument.
;;
;; NB: The type of the function should guarantee that we can't drop more elements
;; than there are in the first argument.

(claim drop-last-k
  (Pi ((E U)
       (k Nat)
       (m Nat))
    (-> (Vec E (+ m k)) (Vec E m))))

(claim drop-last-k-motive
  (-> U Nat Nat U))
       
(define drop-last-k-motive
  (λ (E k m)
    (-> (Vec E (+ m k))
        (Vec E m))))

(claim drop-last-k-base
  (Pi ((E U)
        (k Nat))
    (drop-last-k-motive E k 0)))

(define drop-last-k-base
  (λ (E k)
    (λ (_)
    vecnil)))

(claim drop-last-k-step
  (Pi ((E U)
       (k Nat)
       (i Nat))
    (-> (drop-last-k-motive E k i)
        (drop-last-k-motive E k (add1 i)))))

(define drop-last-k-step
  (λ (E k i)
    (λ (drop-last-almost)
      (λ (es)
        (vec:: (head es) (drop-last-almost (tail es)))))))

(define drop-last-k
  (λ (E k m)
      (ind-Nat m
        (drop-last-k-motive E k)
        (drop-last-k-base E k)
        (drop-last-k-step E k))))
```

```
#lang pie

;; Exercises on Nat equality from Chapter 8 and 9 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

;; Exercise 8.1
;; Define a function called zero+n=n that states and proves that
;; 0+n = n for all Nat n.

(claim zero+n=n
  (Pi ((n Nat))
    (= Nat n (+ zero n))))

(define zero+n=n
  (λ (n)
    (same n)))
    
;; Exercise 8.2
;;
;; Define a function called a=b->a+n=b+n that states and proves that
;; a = b implies a+n = b+n for all Nats a, b, n.

(claim a=b->a+n=b+n
  (Pi ((a Nat)
       (b Nat)
       (n Nat))
    (-> (= Nat a b)
      (= Nat (+ a n) (+ b n)))))

(define a=b->a+n=b+n
  (λ (a b n)
    (λ (p)
      (replace p
        (λ (k)
          (= Nat (+ a n) (+ k n)))
        (same (+ a n))))))
        
;; Exercise 8.3
;;
;; Define a function called plusAssociative that states and proves that
;; + is associative.

(claim plusAssociative
  (Π ([n Nat]
      [m Nat]
      [k Nat])
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(define plusAssociative
  (λ (n m)
    (λ (k)
      (ind-Nat k
         (λ (k)
           (= Nat (+ k (+ n m)) (+ (+ k n) m)))
        (same (+ n m))
        (λ (_ e)
          (cong e (+ 1)))))))    
          
;; Exercise 9.1
;;
;; Define a function called same-cons that states and proves that
;; if you cons the same value to the front of two equal Lists then
;; the resulting Lists are also equal.

(claim same-cons
  (Π ([E U]
      [l1 (List E)]
      [l2 (List E)]
      [e E])
    (-> (= (List E) l1 l2)
      (= (List E) (:: e l1) (:: e l2)))))

(define same-cons
  (λ (E l1 l2 e)
    (λ (s)
      (replace s
        (λ (x)
          (= (List E) (:: e l1) (:: e x)))
        (same (:: e l1))))))

;; Exercise 9.2
;;
;; Define a function called same-lists that states and proves that
;; if two values, e1 and e2, are equal and two lists, l1 and l2 are
;; equal then the two lists, (:: e1 l1) and (:: e2 l2) are also equal.

(claim same-lists
  (Pi ((E U)
       (l1 (List E))
       (l2 (List E))
       (e1 E)
       (e2 E))
    (-> (= E e1 e2) (= (List E) l1 l2)
        (= (List E) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (λ (E l1 l2 e1 e2)
    (λ (e1=e2 l1=l2)
      (replace e1=e2
        (λ (x)
          (= (List E) (:: e1 l1) (:: x l2)))
        (same-cons E l1 l2 e1 l1=l2)))))

```

```
#lang pie

;; Exercises on ind-Nat from Chapter 10 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

(claim length
       (Π ([E U])
          (-> (List E)
              Nat)))

(define length
  (λ (_)
    (λ (es)
      (rec-List es
                0
                (λ (_ _ almost-length)
                  (add1 almost-length))))))

(claim step-append
       (Π ([E U])
          (-> E (List E) (List E)
              (List E))))

(define step-append
  (λ (E)
    (λ (e es append-es)
      (:: e append-es))))

(claim append
       (Π ([E U])
          (-> (List E) (List E)
              (List E))))

(define append
  (λ (E)
    (λ (start end)
      (rec-List start
                end
                (step-append E)))))

(claim filter-list
       (Π ([E U])
          (-> (-> E Nat) (List E)
              (List E))))

(claim filter-list-step
       (Π ([E U])
          (-> (-> E Nat)
              (-> E (List E) (List E)
                  (List E)))))

(claim if
       (Π ([A U])
          (-> Nat A A
              A)))

(define if
  (λ (A)
    (λ (e if-then if-else)
      (which-Nat e
                 if-else
                 (λ (_) if-then)))))

(define filter-list-step
  (λ (E)
    (λ (p)
      (λ (e es filtered-es)
        (if (List E) (p e)
            (:: e filtered-es)
            filtered-es)))))

(define filter-list
  (λ (E)
    (λ (p es)
      (rec-List es
                (the (List E) nil)
                (filter-list-step E p)))))

;; Exercise 10.1
;;
;; Define a function called list-length-append-dist that states and proves that
;; if you append two lists, l1 and l2, and then the length of the result is
;; equal to the sum of the lengths of l1 and l2.

(claim list-length-append-dist
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)])
          (= Nat
             (length E (append E l1 l2))
             (+ (length E l1) (length E l2)))))

(define list-length-append-dist
  (λ (E l1 l2)
    (ind-List l1
      (λ (x)
        (= Nat
             (length E (append E x l2))
             (+ (length E x) (length E l2))))
      (same (length E l2))
      (λ (e es l1=l2)
        (cong l1=l2 (+ 1))))))
        
;; Exercise 10.2
;;
;; In the following exercises we'll use the function called <= that takes two
;; Nat arguments a, b and evaluates to a type representing the proposition
;; that a is less than or equal to b.

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))

;; Exercise 10.2.1
;;
;; Using <=, state and prove that 1 is less than or equal to 2.

(claim one<=two
  (<= 1 2))

(define one<=two
  (cons 1 (same 2)))
  
  
;; Exercise 10.2.2
;;
;; Define a funciton called <=-simplify to state and prove that for all
;; Nats a, b, n we have that n+a <= b implies a <= b
;;
;; NB: You may need to use plusAssociative that was proved in Exercise 8.3.

(claim <=-simplify
       (Π ([a Nat]
           [b Nat]
           [n Nat])
          (-> (<= (+ n a) b)
              (<= a b))))

;; This solution is from: https://github.com/paulcadman/the-little-typer
(define <=-simplify
  (λ (a b n)
    (λ (n+a<=b)
      (cons (+ (car n+a<=b) n)
            ;;
            ;; The goal is to produce a value of type:
            ;;
            ;; [1] (= Nat (+ (+ (car n+a<=b) n) a)
            ;;               b)
            ;;
            ;; (cdr n+a<=b) is a value of type:
            ;;
            ;; [2] (= Nat (+ (car n+a<=b) (+ n a))
            ;;            b)
            ;;
            ;; Using symm and plusAssociative we produce a value of type:
            ;;
            ;; [3] (= Nat (+ (+ (car n+a<=b) n) a)
            ;;            (+ (car n+a<=b) (+ n a)))
            ;;
            ;; Using trans with [2] and [3] we produce a value of [1] which
            ;; is our goal.
            ;;
            (trans (symm (plusAssociative n a (car n+a<=b)))
                   (cdr n+a<=b))))))  
                   
;; Exercise 10.2.3
;;
;; Define a function called <=-trans that states and proves that <= is
;; transitive.

(claim <=-trans
       (Π ([a Nat]
           [b Nat]
           [c Nat])
          (-> (<= a b)
              (<= b c)
              (<= a c))))

;; This solution is from: https://github.com/paulcadman/the-little-typer
(define <=-trans
  ;;
  ;; The goal is to produce a value of type:
  ;;
  ;; [1] (<= a c)
  ;;
  ;; The target of the replace has type:
  ;;
  ;; [2] (= Nat b (+ (car a<=b) a))
  ;;
  ;; (mot from) is therefore (mot b) and its type is:
  ;;
  ;; [3] (Σ ([k Nat])
  ;;        (= Nat (+ k b) c))
  ;;
  ;; b<=c is a value of [3] so it can be used as the base of reduce.
  ;;
  ;; The replace expression therefore produces a value of type (mot to) which is
  ;; (mot (+ (car a<=b) a)). This has type:
  ;;
  ;; [4] (Σ ([k] Nat)
  ;;        (= Nat (+ k (+ (car a<=b) a )) c))
  ;;
  ;; By definition of <= this is the same type as:
  ;;
  ;; [5] (<= (+ (car a<=b) a) c)
  ;;
  ;; Using <=-simplify we can remove (car a<=b) from [5] to produce a value of
  ;; [1], our goal type.
  ;;
  (λ (a b c)
    (λ (a<=b b<=c)
      (<=-simplify a c (car a<=b)
                   (replace (symm (cdr a<=b))
                            (λ (l)
                              (Σ ([k Nat])
                                 (= Nat (+ k l) c)))
                            b<=c)))))                   
```
