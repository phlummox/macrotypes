#lang s-exp "../infer+tup.rkt"
(require "rackunit-typechecking.rkt")

(check-type (λ (x) 5) : (∀ (X) (→ X Int)))
(check-type (λ (x) x) : (∀ (X) (→ X X)))
(check-type ((λ (x) x) 5) : Int)
(check-type ((λ (x) x) (λ (y) y)) : (∀ (Y) (→ Y Y)))

(check-type (λ (x) (λ (y) 6)) : (∀ (X) (→ X (∀ (Y) (→ Y Int)))))
(check-type (λ (x) (λ (y) x)) : (∀ (X) (→ X (∀ (Y) (→ Y X)))))
(check-type (λ (x) (λ (y) y)) : (∀ (X) (→ X (∀ (Y) (→ Y Y)))))

(check-type (λ (x) (λ (y) (λ (z) 7))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Int)))))))
(check-type (λ (x) (λ (y) (λ (z) x))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z X)))))))
(check-type (λ (x) (λ (y) (λ (z) y))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Y)))))))
(check-type (λ (x) (λ (y) (λ (z) z))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Z)))))))

(check-type (+ 1 2) : Int)
(check-type (λ (x) (+ x 2)) : (→ Int Int))
(check-type (λ (x y) (+ 1 2)) : (∀ (X Y) (→ X Y Int)))
(check-type (λ (x y) (+ x 2)) : (∀ (Y) (→ Int Y Int)))
(check-type (λ (x y) (+ 1 y)) : (∀ (X) (→ X Int Int)))
(check-type (λ (x y) (+ x y)) : (→ Int Int Int))

(check-type (λ (x) (λ (y) (+ 1 2))) : (∀ (X) (→ X (∀ (Y) (→ Y Int)))))
(check-type (λ (x) (λ (y) (+ x 2))) : (→ Int (∀ (Y) (→ Y Int))))
(check-type (λ (x) (λ (y) (+ 1 y))) : (∀ (X) (→ X (→ Int Int))))
(check-type (λ (x) (λ (y) (+ x y))) : (→ Int (→ Int Int)))

(check-type (λ (x) (λ (y) (λ (z) (+ 1 2)))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Int)))))))
(check-type (λ (x) (λ (y) (λ (z) (+ x 2)))) : (→ Int (∀ (Y) (→ Y (∀ (Z) (→ Z Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ y 2)))) : (∀ (X) (→ X (→ Int (∀ (Z) (→ Z Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ z 2)))) : (∀ (X) (→ X (∀ (Y) (→ Y (→ Int Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ x y)))) : (→ Int (→ Int (∀ (Z) (→ Z Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ x z)))) : (→ Int (∀ (Y) (→ Y (→ Int Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ y z)))) : (∀ (X) (→ X (→ Int (→ Int Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ (+ x y) z)))) : (→ Int (→ Int (→ Int Int))))

(check-type (λ (f a) (f a)) : (∀ (A B) (→ (→ A B) A B)))

(check-type (λ (a f g) (g (f a)))
            : (∀ (A B C) (→ A (→ A B) (→ B C) C)))
(check-type (λ (a f g) (g (f a) (+ (f 1) (f 2))))
            : (∀ (C) (→ Int (→ Int Int) (→ Int Int C) C)))
(check-type (λ (a f g) (g (λ () (f a)) (+ (f 1) (f 2))))
            : (∀ (C) (→ Int (→ Int Int) (→ (→ Int) Int C) C)))

(typecheck-fail
 (λ (f) (f f))
 #:with-msg "couldn't unify A[0-9]+ and \\(→ A[0-9]+ R[0-9]+\\) because one contains the other")

(typecheck-fail
 (λ (f)
   ((λ (g) (f (λ (x) ((g g) x))))
    (λ (g) (f (λ (x) ((g g) x))))))
 #:with-msg "couldn't unify A[0-9]+ and \\(→ A[0-9]+ R[0-9]+\\) because one contains the other")

(define fact-builder
  (λ (fact)
    (λ (n)
      (if (= 0 n)
          1
          (* n (fact (sub1 n)))))))

(check-type fact-builder : (→ (→ Int Int) (→ Int Int)))

(define fact~ (fact-builder (fact-builder (fact-builder (fact-builder (fact-builder (λ (n) 1)))))))
(check-type fact~ : (→ Int Int))
(check-type (fact~ 0) : Int -> 1)
(check-type (fact~ 1) : Int -> 1)
(check-type (fact~ 2) : Int -> 2)
(check-type (fact~ 3) : Int -> 6)
(check-type (fact~ 4) : Int -> 24)
(check-type (fact~ 5) : Int -> 120)
(check-type (fact~ 6) : Int -> 720)
;(check-type (fact~ 7) : Int -> 5040)  ; fails, produces 2520
;(check-type (fact~ 8) : Int -> 40320) ; fails, produces 6720

(define/rec Y : (∀ (A B) (→ (→ (→ A B) (→ A B)) (→ A B)))
  (λ (f)
    (f (λ (x) ((Y f) x)))))
(check-type Y : (∀ (A B) (→ (→ (→ A B) (→ A B)) (→ A B))))

(define fact (Y fact-builder))
(check-type fact : (→ Int Int))
(check-type (fact 0) : Int -> 1)
(check-type (fact 1) : Int -> 1)
(check-type (fact 2) : Int -> 2)
(check-type (fact 3) : Int -> 6)
(check-type (fact 4) : Int -> 24)
(check-type (fact 5) : Int -> 120)
(check-type (fact 6) : Int -> 720)
(check-type (fact 7) : Int -> 5040)
(check-type (fact 8) : Int -> 40320)

;; TODO: fix this error message
#;(typecheck-fail
 ((λ (x) (+ x 1))
  ((λ (y) (if y #true #false))
   #false))
 #:with-msg "expected: Int\n *given: Bool")

;; match tests

(check-type (match 1 with [(v: x) -> x]) : Int -> 1)

(check-type (λ (x) (match x with [(v: y) -> (+ y 1)])) : (→ Int Int))

(check-type (match (tup 1 "a") with [(v: x) -> x])
            : (× Int String) -> (tup 1 "a"))
(check-type (match (tup 1 "a") with [(tup: (v: x) (v: y)) -> x])
            : Int -> 1)
(check-type (match (tup 1 "a") with [(tup: (v: x) (v: y)) -> y])
            : String -> "a")

(check-type (λ (x) (match x with [(tup: (v: y) (v: z)) -> y]))
            : (∀ (Y Z) (→ (× Y Z) Y)))
(check-type (λ (x) (match x with [(tup: (v: y) (v: z)) -> z]))
            : (∀ (Y Z) (→ (× Y Z) Z)))

;; let tests

(check-type (let ([f (λ (x) x)])
              (if (f #true)
                  (f 5)
                  (f 6)))
            : Int -> 5)

(check-type (let ([double (λ (f) (λ (a) (f (f a))))])
              (tup (double (λ (x) (+ x 1)))
                   (double (λ (b) (if b b #false)))
                   (double double)))
            : (∀ (X) (× (→ Int Int) (→ Bool Bool) (→ (→ X X) (→ X X)))))

;; letrec tests

(check-type (letrec () 1) : Int -> 1)
(check-type (letrec ([x 1]) x) : Int -> 1)

(check-type (letrec ([x (begin (λ () x) 5)]) x) : Int -> 5)
(check-type (letrec ([x (begin (λ () (ann x : Int)) 5)]) x) : Int -> 5)
(typecheck-fail
 (letrec ([x (begin (λ () (ann x : Bool)) 5)]) x)
 #:with-msg "expected: Bool\n *given: Int")

(check-type (letrec ([f (λ () x)] [x 5])
              (f))
            : Int -> 5)

(check-type
 (letrec ([factorial (λ (n)
                       (if (zero? n)
                           1
                           (* n (factorial (sub1 n)))))]
          [mapper (λ (f)
                    (λ (lst)
                      (if (empty? lst)
                          empty
                          (cons (f (first lst)) ((mapper f) (rest lst))))))])
   ((mapper factorial) (list 0 1 2 3 4 5 6 7 8)))
 : (List Int) -> (list 1 1 2 6 24 120 720 5040 40320))

(define mapper
  (letrec
      ([mapper (λ (f)
                 (λ (lst)
                   (if (empty? lst)
                       empty
                       (cons (f (first lst)) ((mapper f) (rest lst))))))])
    mapper))
(check-type mapper : (∀ (A B) (→ (→ A B) (→ (List A) (List B)))))
(check-type ((mapper (mapper fact)) (list (list 0 1 2) (list 3 4 5) (list 6 7 8)))
            : (List (List Int))
            -> (list (list 1 1 2) (list 6 24 120) (list 720 5040 40320)))

;; This local mapper function is polymorphic!
(check-type
 (letrec ([factorial (λ (n)
                       (if (zero? n)
                           1
                           (* n (factorial (sub1 n)))))]
          [mapper (λ (f)
                    (λ (lst)
                      (if (empty? lst)
                          empty
                          (cons (f (first lst)) ((mapper f) (rest lst))))))])
   ((mapper (mapper factorial)) (list (list 0 1 2) (list 3 4 5) (list 6 7 8))))
 : (List (List Int)) -> (list (list 1 1 2) (list 6 24 120) (list 720 5040 40320)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lctrue (λ (t f) (t)))
(define lcfalse (λ (t f) (f)))

(define lcif (λ (c t e) (c t e)))

(check-type (lcif lctrue (λ () 1) (λ () 2)) : Int -> 1)
(check-type (lcif lcfalse (λ () 1) (λ () 2)) : Int -> 2)

;; TODO: get this something like this type working
;; (define-type (LCNat X)
;;   (→
;;    (→ X) ; zero case
;;    (→ (LCNat X) X) ; add1 case
;;    X))
(define lc0 (λ (z s) (z)))
(check-type lc0 : (∀ (R S) (→ (→ R) S R)))

(define lcadd1 (λ (n) (λ (z s) (s n))))
(define lcsub1 (λ (n) (n (λ () (error "can't subtract one from zero")) (λ (n-1) n-1))))
(check-type lcadd1 : (∀ (N) (→ N (∀ (Z R) (→ Z (→ N R) R)))))
(check-type lcsub1 : (∀ (Y R) (→ (→ (→ (∀ (X) X)) (→ Y Y) R) R)))

(define lc1 (lcadd1 lc0))
(define lc2 (lcadd1 lc1))
(define lc3 (lcadd1 lc2))

(check-type (lc0 (λ () 0) (λ (n-1) 1)) : Int -> 0)
(check-type (lc1 (λ () 0) (λ (n-1) 1)) : Int -> 1)
(check-type (lc2 (λ () 0) (λ (n-1) 1)) : Int -> 1)
(check-type (lc3 (λ () 0) (λ (n-1) 1)) : Int -> 1)

(check-type (lc1 (λ () 0) (λ (n-1) (n-1 (λ () 1) (λ (n-2) 2))))
            : Int -> 1)
(check-type (lc2 (λ () 0) (λ (n-1) (n-1 (λ () 1) (λ (n-2) 2))))
            : Int -> 2)
(check-type (lc3 (λ () 0) (λ (n-1) (n-1 (λ () 1) (λ (n-2) 2))))
            : Int -> 2)

(check-type (lc2 (λ () 0) (λ (n-1) (n-1 (λ () 1) (λ (n-2) (n-2 (λ () 2) (λ (n-3) 3))))))
            : Int -> 2)
(check-type (lc3 (λ () 0) (λ (n-1) (n-1 (λ () 1) (λ (n-2) (n-2 (λ () 2) (λ (n-3) 3))))))
            : Int -> 3)

(define lcnat->int
  (λ (n)
    (n (λ () 0)
       (λ (n-1)
         (n-1
          (λ () 1)
          (λ (n-2)
            (n-2
             (λ () 2)
             (λ (n-3)
               (n-3
                (λ () 3)
                (λ (n-4)
                  4))))))))))

(define int->lcnat
  (λ (n)
    (if (= 0 n)
        lc0
        (if (= 1 n)
            lc1
            (if (= 2 n)
                lc2
                lc3)))))

(check-type (lcnat->int lc0) : Int -> 0)
(check-type (lcnat->int lc1) : Int -> 1)
(check-type (lcnat->int lc2) : Int -> 2)
(check-type (lcnat->int lc3) : Int -> 3)
(check-type (lcnat->int (int->lcnat 0)) : Int -> 0)
(check-type (lcnat->int (int->lcnat 1)) : Int -> 1)
(check-type (lcnat->int (int->lcnat 2)) : Int -> 2)
(check-type (lcnat->int (int->lcnat 3)) : Int -> 3)

;(define tuplc+lc-lc*
;  (letrec ([lc+ (λ (a b)
;                  (a (λ () b)
;                     (λ (a-1) (lc+ a-1 (lcadd1 b)))))]
;           [lc- (λ (a b)
;                  (b (λ () a)
;                     (λ (b-1) (lc- (lcsub1 a) b-1))))]
;           [lc* (λ (a b)
;                  (a (λ () a)
;                     (λ (a-1) (lc+ b (lc* a-1 b)))))])
;    (tup lc+ lc- lc*)))
;(define lc+ (match tuplc+lc-lc* [(tup: (v: lc+) (v: lc-) (v: lc*)) lc+]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; from the old infer tests

(check-type (λ (x) (+ x 1)) : (→ Int Int))
(check-type ((λ (f) (f 10)) (λ (x) x)) : Int -> 10)

; stlc+lit tests with app, but infer types (no annotations)
(check-type ((λ (x) x) 1) : Int -> 1)
(check-type ((λ (f x y) (f x y)) + 1 2) : Int -> 3)
(check-type ((λ (x) (+ x x)) 10) : Int -> 20)

(check-type ((λ (x) ((λ (y) y) x)) 10) : Int -> 10)

; top level functions
(define/rec (f [x : Int]) -> Int x)
(check-type f : (→ Int Int))
(check-type (f 1) : Int -> 1)
(typecheck-fail (f (λ ([x : Int]) x)))

(define/rec #:∀ (X) (g [x : X]) -> X x)
(check-type g : (∀ (X) (→ X X)))

; (inferred) polymorpic instantiation
(check-type (g 1) : Int -> 1)
(check-type (g #f) : Bool -> #f) ; different instantiation
(check-type (g add1) : (→ Int Int) -> add1)
(check-type (g +) : (→ Int Int Int) -> +)

; function polymorphic in list element
(define/rec #:∀ (X) (g2 [lst : (List X)]) -> (List X) lst)
(check-type g2 : (∀ (X) (→ (List X) (List X))))
(typecheck-fail (g2 1) #:with-msg "expected: \\(List X\\)\n *given: Int")
(check-type (g2 empty) : (∀ (X) (List X)) -> empty)
(check-type (g2 (cons 1 empty)) : (List Int) -> (cons 1 empty))
(check-type (g2 (cons "1" empty)) : (List String) -> (cons "1" empty))

(define/rec #:∀ (X) (g3 [lst : (List X)]) -> X (first lst))
(check-type g3 : (∀ (X) (→ (List X) X)) -> g3)
(check-type g3 : (∀ (A) (→ (List A) A)) -> g3)
(check-not-type g3 : (∀ (A B) (→ (List A) B)))
(typecheck-fail (g3)
 ; TODO: more precise err msg
 #:with-msg "expected: \\(→ R[0-9]+\\)\n *given: \\(→ \\(List X\\) X\\)")
(check-type (g3 empty) : (∀ (X) X)) ; runtime fail
(check-type (g3 (cons 1 empty)) : Int -> 1)
(check-type (g3 (cons "1" empty)) : String -> "1")

; recursive fn
(define/rec (recf [x : Int]) -> Int (recf x))
(check-type recf : (→ Int Int))

(define/rec (countdown [x : Int]) -> Int
  (if (zero? x)
      0
      (countdown (sub1 x))))
(check-type (countdown 0) : Int -> 0)
(check-type (countdown 10) : Int -> 0)
(typecheck-fail (countdown "10") #:with-msg "couldn't unify Int and String")

; list abbrv
(check-type (list 1 2 3) : (List Int))
(typecheck-fail (list 1 "3")
 #:with-msg "expected: A[0-9]+, \\(List A[0-9]+\\)\n *given: Int, \\(List String\\)")


(define/rec #:∀ (X Y) (map [f : (→ X Y)] [lst : (List X)]) -> (List Y)
  (if (empty? lst)
      empty
      (cons (f (first lst)) (map f (rest lst)))))

(check-type map : (∀ (X Y) (→ (→ X Y) (List X) (List Y))))
(check-type map : (∀ (Y X) (→ (→ Y X) (List Y) (List X))))
(check-type map : (∀ (A B) (→ (→ A B) (List A) (List B))))
(check-not-type map : (∀ (X Y) (→ (→ X X) (List X) (List X))))
(check-not-type map : (∀ (X) (→ (→ X X) (List X) (List X))))

(check-type (map add1 empty) : (List Int) -> empty)
(check-type (map add1 (list)) : (List Int) -> empty)
(check-type (map add1 (list 1 2 3)) : (List Int) -> (list 2 3 4))
(typecheck-fail
 (map add1 (list "1"))
 #:with-msg "expected: \\(→ X Y\\), \\(List X\\)\n *given: \\(→ Int Int\\), \\(List String\\)")
(check-type (map (λ (x) (+ x 2)) (list 1 2 3)) : (List Int) -> (list 3 4 5))
(check-type (map first (list (list 1 2 3) (list 4 5) (list 6))) : (List Int) -> (list 1 4 6))

(define/rec #:∀ (X) (filter [p? : (→ X Bool)] [lst : (List X)]) -> (List X)
  (if (empty? lst)
      empty
      (if (p? (first lst))
          (cons (first lst) (filter p? (rest lst)))
          (filter p? (rest lst)))))
(define/rec #:∀ (X) (filter/let [p? : (→ X Bool)] [lst : (List X)]) -> (List X)
  (if (empty? lst)
      empty
      (let ([x (first lst)] [filtered-rst (filter p? (rest lst))])
        (if (p? x) (cons x filtered-rst) filtered-rst))))

(check-type (filter zero? empty) : (List Int) -> empty)
(check-type (filter zero? (list 1 2 3)) : (List Int) -> empty)
(check-type (filter zero? (list 0 1 2)) : (List Int) -> (list 0))
(check-type (filter (λ (x) (not (zero? x))) (list 0 1 2)) : (List Int) -> (list 1 2))

(define/rec #:∀ (X Y) (foldr [f : (→ X Y Y)] [base : Y] [lst : (List X)]) -> Y
  (if (empty? lst)
      base
      (f (first lst) (foldr f base (rest lst)))))
(define/rec #:∀ (X Y) (foldl [f : (→ X Y Y)] [acc : Y] [lst : (List X)]) -> Y
  (if (empty? lst)
      acc
      (foldl f (f (first lst) acc) (rest lst))))

(define/rec #:∀ (X) (all? [p? : (→ X Bool)] [lst : (List X)]) -> Bool
  (if (empty? lst)
      #true
      (and (p? (first lst)) (all? p? (rest lst)))))

(define/rec #:∀ (X) (tails [lst : (List X)]) -> (List (List X))
  (if (empty? lst)
      (list empty)
      (cons lst (tails (rest lst)))))

; creates backwards list
(define/rec #:∀ (X) (build-list [n : Int] [f : (→ Int X)]) -> (List X)
  (if (zero? (sub1 n))
      (list (f 0))
      (cons (f (sub1 n)) (build-list (sub1 n) f))))
(check-type (build-list 1 add1) : (List Int) -> (list 1))
(check-type (build-list 3 add1) : (List Int) -> (list 3 2 1))
(check-type (build-list 5 sub1) : (List Int) -> (list 3 2 1 0 -1))

(define/rec #:∀ (X) (append [lst1 : (List X)] [lst2 : (List X)]) -> (List X)
  (if (empty? lst1)
      lst2
      (cons (first lst1) (append (rest lst1) lst2))))

; nqueens
(define-type-alias Queen (× Int Int))
(define/rec (q-x [q : Queen]) -> Int (match q with [(tup: (v: x) (v: y)) -> x]))
(define/rec (q-y [q : Queen]) -> Int (match q with [(tup: (v: x) (v: y)) -> y]))
(define/rec (Q [x : Int] [y : Int]) -> Queen (tup x y))

(define/rec (safe? [q1 : Queen] [q2 : Queen]) -> Bool
  (let ([x1 (q-x q1)][y1 (q-y q1)]
        [x2 (q-x q2)][y2 (q-y q2)])
    (not (or (= x1 x2) (= y1 y2) (= (abs (- x1 x2)) (abs (- y1 y2)))))))
(define/rec (safe/list? [qs : (List Queen)]) -> Bool
  (if (empty? qs)
      #t
      (let ([q1 (first qs)])
        (all? (λ (q2) (safe? q1 q2)) (rest qs)))))
(define/rec (valid? [lst : (List Queen)]) -> Bool
  (all? safe/list? (tails lst)))

(define/rec (nqueens [n : Int]) -> (List Queen)
  (let* ([process-row
          (λ ;([r : Int] [all-possible-so-far : (List (List Queen))])
              (r all-possible-so-far)
            (foldr
             ;; 2015-12-18: dont need annotations on lambdas with concrete type
             (λ ;([qs : (List Queen)] [new-qss : (List (List Queen))])
                 (qs new-qss)
               (append
                (map
                 ;; 2015-12-18: dont need annotations on lambdas with concrete type
                 (λ (c) (cons (Q r c) qs))
                 (build-list n add1))
                new-qss))
             empty
             all-possible-so-far))]
         [all-possible (foldl process-row (list empty) (build-list n add1))])
    (let ([solns (filter valid? all-possible)])
      (if (empty? solns)
          empty
          (first solns)))))

(check-type nqueens : (→ Int (List Queen)))
(check-type (nqueens 1) : (List Queen) -> (list (Q 1 1)))
(check-type (nqueens 2) : (List Queen) -> (list))
(check-type (nqueens 3) : (List Queen) -> (list))
(check-type (nqueens 4) : (List Queen) -> (list (Q 1 2) (Q 2 4) (Q 3 1) (Q 4 3)))
(check-type (nqueens 5) : (List Queen) -> (list (Q 1 2) (Q 2 4) (Q 3 1) (Q 4 3) (Q 5 5)))

; --------------------------------------------------
; all ext-stlc tests should still pass (copied below):
;; tests for stlc extensions
;; new literals and base types
(check-type "one" : String) ; literal now supported
(check-type #f : Bool) ; literal now supported

(check-type (λ (x) (ann x : Bool)) : (→ Bool Bool)) ; Bool is now valid type

;; Unit
(check-type (void) : Unit)
(check-type void : (→ Unit))

(typecheck-fail
 ((ann (λ (x) x) : (→ Unit Unit)) 2)
 #:with-msg
 "couldn't unify Unit and Int")
(typecheck-fail
 ((ann (λ (x) x) : (→ Unit Unit)) void)
  #:with-msg
  "couldn't unify Unit and \\(→ Unit\\)")

(check-type ((ann (λ (x) x) : (→ Unit Unit)) (void)) : Unit)

;; begin
(check-type (begin 1) : Int)

(typecheck-fail (begin) #:with-msg "expected more terms")
;; 2016-03-06: begin terms dont need to be Unit
(check-type (begin 1 2 3) : Int)
#;(typecheck-fail
 (begin 1 2 3)
 #:with-msg "Expected expression 1 to have Unit type, got: Int")

(check-type (begin (void) 1) : Int -> 1)
(check-type ((λ (x) (begin (void) x)) 1) : Int -> 1)
(check-type ((λ (x) (begin x)) 1) : Int -> 1)
(check-type ((λ (x) (begin (begin x))) 1) : Int -> 1)
(check-type ((λ (x) (begin (void) (begin (void) x))) 1) : Int -> 1)
(check-type ((λ (x) (begin (begin (void) x))) 1) : Int -> 1)

;;ascription
(check-type (ann 1 : Int) : Int -> 1)
(check-type ((λ (x) (ann x : Int)) 10) : Int -> 10)
(typecheck-fail (ann 1 : Bool) #:with-msg "expected: Bool\n *given: Int")
;ann errs
(typecheck-fail (ann 1 : Complex) #:with-msg "unbound identifier")
(typecheck-fail (ann 1 : 1) #:with-msg "not a valid type")
(typecheck-fail (ann 1 : (λ (x) x)) #:with-msg "not a valid type")
(typecheck-fail (ann Int : Int) #:with-msg "expected: Int\n *given: #%type")

; let
(check-type (let () (+ 1 1)) : Int -> 2)
(check-type (let ([x 10]) (+ 1 2)) : Int -> 3)
(check-type (let ([x 10] [y 20]) ((λ (z a) (+ a z)) x y)) : Int -> 30)
(typecheck-fail
 (let ([x #f]) (+ x 1))
 #:with-msg "expected: Int, Int\n *given: Bool, Int")
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))
                #:with-msg "x: unbound identifier")

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int -> 21)
(typecheck-fail
 (let* ([x #t] [y (+ x 1)]) 1)
 #:with-msg "expected: Int, Int\n *given: Bool, Int")

; letrec
(check-type (letrec ([x #f] [y 1]) y) : Int -> 1)
(check-type (letrec ([y 1] [x #f]) x) : Bool -> #f)

(check-type (letrec ([x 1] [y (+ x 1)]) (+ x y)) : Int -> 3)

;; recursive
(check-type
 (letrec ([countdown
           (λ (i)
             (if (= i 0)
                 "liftoff"
                 (countdown (- i 1))))])
   (countdown 10)) : String -> "liftoff")

;; mutually recursive
(check-type
 (letrec ([is-even?
           (λ (n)
             (or (zero? n)
                 (is-odd? (sub1 n))))]
          [is-odd?
           (λ (n)
             (and (not (zero? n))
                  (is-even? (sub1 n))))])
   (is-odd? 11)) : Bool -> #t)

;; check some more err msgs
(typecheck-fail
 (and "1" #f)
 #:with-msg
 "expected: Bool, Bool\n *given: String, Bool")
(typecheck-fail
 (and #t "2")
 #:with-msg
 "expected: Bool, Bool\n *given: Bool, String")
(typecheck-fail
 (or "1" #f)
 #:with-msg
 "expected: +Bool, Bool\n *given: +String, Bool")
(typecheck-fail
 (or #t "2")
 #:with-msg
 "expected: +Bool, Bool\n *given: +Bool, String")
;; 2016-03-10: change if to work with non-false vals
(check-type (if "true" 1 2) : Int -> 1)
(typecheck-fail
 (if #t 1 "2")
 #:with-msg 
 "couldn't unify Int and String")

;; tests from stlc+lit-tests.rkt --------------------------
; most should pass, some failing may now pass due to added types/forms
(check-type 1 : Int)
;(check-not-type 1 : (Int → Int))
;(typecheck-fail "one") ; literal now supported
;(typecheck-fail #f) ; literal now supported
(check-type (λ (x y) x) : (∀ (X Y) (→ X Y X)))
(check-not-type (λ (x) x) : Int)
(check-type (λ (x) x) : (∀ (X) (→ X X)))
(check-type (λ (f) 1) : (∀ (X) (→ X Int)))
(check-type ((λ (x) x) 1) : Int -> 1)

(typecheck-fail
 ((ann (λ (x) x) : (→ Bool Bool)) 1)
 #:with-msg
 "expected: Bool\n *given: Int")
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail
 (λ (f) ((ann f : Int) 1 2))
 #:with-msg
 "expected: \\(→ A[0-9]+ B[0-9]+ R[0-9]+\\)\n *given: Int")

(check-type (λ (f x y) (f x y))
            : (∀ (X Y R) (→ (→ X Y R) X Y R)))
(check-type ((λ (f x y) (f x y)) + 1 2)
            : Int -> 3)

(typecheck-fail
 (+ 1 (λ (x) x))
 #:with-msg
 "expected: Int, Int\n *given: Int, \\(→ X[0-9]+ X[0-9]+\\)")
(check-type (λ (x) (+ x x)) : (→ Int Int))
(typecheck-fail
 ((λ (x y) y) 1)
 #:with-msg "expected: \\(→ A[0-9]+ R[0-9]+\\)\n *given: \\(→ X[0-9]+ Y[0-9]+ Y[0-9]+\\)")

(check-type ((λ (x) (+ x x)) 10) : Int -> 20)

