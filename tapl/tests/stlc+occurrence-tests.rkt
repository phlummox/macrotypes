#lang s-exp "../stlc+occurrence.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; basic types & syntax

(check-type 1 : Int)
(check-type #f : Bool)
(check-type "hello" : String)
(check-type 1 : Top)
(check-type (λ ([x : (∪ Bool Int)]) x)
            : (→ (∪ Bool Int) (∪ Bool Int)))

(typecheck-fail
 (λ ([x : ∪]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (1 ∪)]) x)
 #:with-msg "")
(typecheck-fail
 (λ ([x : (Int ∪)]) x)
 #:with-msg "expected identifier")
(typecheck-fail
 (λ ([x : (→ ∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (→ Int ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪ Int →)]) x)
 #:with-msg "Improper usage of type constructor →: →, expected >= 1 arguments")

;; -----------------------------------------------------------------------------
;; --- type evaluation

(check-type (λ ([x : (∪ Int Int Int Int)]) x)
            : (→ Int Int))
(check-type (λ ([x : (∪ Int Bool)]) 42)
            : (→ (∪ Bool Int) Int))
(check-type (λ ([x : (∪ Int Bool Bool Int)]) x)
            : (→ (∪ Bool Int) (∪ Bool Int)))
(check-type (λ ([x : (∪ (∪ Int Bool))]) 42)
            : (→ (∪ Int Bool) Int))
(check-type (λ ([x : (∪ Int Bool)]) 42)
            : (→ (∪ (∪ Int Bool)) Int))
(check-type (λ ([x : (∪ Int Bool)]) 42)
            : (→ (∪ (∪ Int Bool) (∪ Int Bool)) Int))


;; -----------------------------------------------------------------------------
;; --- subtyping

;; ---- basics
(check-type 1 : (∪ Int))
(check-type 1 : (∪ (∪ Int)))
(check-type (λ ([x : Int]) x)
            : (→ Bot Top))

(check-not-type 1 : (∪ Bool))

;; - AMB : t <: t' => t <: (U ... t' ...)
(check-type 1 : (∪ Bool Int))
(check-type -1 : (∪ Int Bool))
(check-type 1 : (∪ Bool Int (→ Bool Bool)))
(check-type 1 : (∪ (∪ Int Bool) (∪ Int Bool)))

(check-not-type 1 : (∪ Bool (→ Int Int)))

;; --- EXT : (U t' ...) <: (U t t' ...)
(check-type (λ ([x : (∪ Int Bool)]) x)
            : (→ (∪ Int Bool) (∪ Int Bool String)))
(check-type (λ ([x : (∪ Int Bool)]) x)
            : (→ (∪ Bool) (∪ Int Bool String)))

(check-not-type (λ ([x : (∪ Int Bool)]) x)
            : (→ (∪ Int Bool) (∪ Int)))
(check-not-type (λ ([x : (∪ Int Bool)]) x)
            : (→ (∪ Bool Int String) (∪ Int Bool)))

;; --- SUB : a<:b => (U a t' ...) <: (U b t' ...)
(check-type (λ ([x : (∪ Int String)]) x)
            : (→ (∪ Int String) (∪ Num String)))
(check-type (λ ([x : (∪ Int String)]) x)
            : (→ (∪ Nat String) (∪ Num String)))

(check-type (λ ([x : (∪ Int String)]) x)
            : (→ (∪ Int String) Top))

(check-not-type (λ ([x : (∪ Int String)]) x)
            : (→ Top (∪ Num String)))

;; --- ALL
(check-type (λ ([x : (∪ Bool Int String)]) x)
            : (→ (∪ Bool Int String) Top))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ (∪ Nat Int Num) Num))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ Nat Num))

;; --- misc
;; Because Int<:(U Int ...)
(check-type (λ ([x : (∪ Int Nat)]) #t)
                  : (→ Int Bool))

;; -----------------------------------------------------------------------------
;; --- Basic Filters (applying functions)

;; --- is-boolean?
(check-type
 (λ ([x : (∪ Bool Int)])
    (test [Bool ? x]
          #t
          #f))
 : (→ (∪ Bool Int) Bool))
(check-type-and-result
 ((λ ([x : (∪ Bool Int)])
     (test (Bool ? x)
           #t
           #f)) #t)
  : Bool ⇒ #t)
(check-type-and-result
 ((λ ([x : (∪ Bool Int)])
     (test (Bool ? x)
           #t
           #f)) 902)
  : Bool ⇒ #f)

;; --- successor
(check-type
 (λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          (+ 1 x)
          0))
 : (→ (∪ Int Bool) (∪ Num Nat)))
(check-type-and-result
 ((λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          (+ 1 x)
          0)) #f)
 : Num ⇒ 0)
(check-type-and-result
 ((λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          (+ 1 x)
          1)) #t)
 : Num ⇒ 1)
(check-type-and-result
 ((λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          (+ 1 x)
          0)) 9000)
 : Num ⇒ 9001)

;; ;; --- Do-nothing filter
(check-type
 (λ ([x : Int])
    (test (Int ? x) #t #f))
 : (→ Int Bool))
(check-type
 (λ ([x : Int])
    (test (Bool ? x) 0 x))
 : (→ Int (∪ Nat Int)))

;; --- Filter a subtype
(check-type
 (λ ([x : (∪ Nat Bool)])
    (test (Int ? x)
          x
          x))
 : (→ (∪ Nat Bool) (∪ Int (∪ Nat Bool))))

(check-type
 (λ ([x : (∪ Int Bool)])
    (test (Nat ? x)
          x
          x))
 : (→ (∪ Bool Int) (∪ Int Nat Bool)))

;; --- Filter a supertype
(check-type
 (λ ([x : (∪ Int Bool)])
    (test (Num ? x)
          1
          x))
 : (→ (∪ Bool Int) (∪ Nat Bool)))

(check-type-and-result
 ((λ ([x : (∪ Int Bool)])
     (test (Num ? x)
           #f
           x)) #t)
 : Bool
 ⇒ #t)

;; Should filter all the impossible types 
(check-type-and-result
 ((λ ([x : (∪ Nat Int Num Bool)])
     (test (Num ? x)
           #f
           x)) #t)
 : Bool
 ⇒ #t)

;; Can refine non-union types
(check-type-and-result
 ((λ ([x : Top])
    (test (String ? x)
          x
          "nope"))
  "yes")
 : String ⇒ "yes")

;; ----------------------------------------------------------------------------- 
;; --- misc subtyping + filters (regression tests)
(check-type
 (λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Bool) Nat))
(check-type
 (λ ([x : (∪ Int Bool)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Bool) Int))

;; -----------------------------------------------------------------------------
;; --- Invalid filters

(typecheck-fail
 (λ ([x : (∪ Int Bool)])
    (test (1 ? x) #t #f))
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (#f ? #t) #t #f)
 #:with-msg "not a valid type")

;; -----------------------------------------------------------------------------
;; --- Subtypes should not be collapsed

(check-not-type (λ ([x : (∪ Int Nat)]) #t)
                : (→ Num Bool))
(check-type ((λ ([x : (∪ Int Nat Bool)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             #t)
            : Nat ⇒ 0)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Nat ? x)
                      1
                      (test (Int ? x)
                            2
                            0)))
             1)
            : Nat ⇒ 1)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             -10)
            : Nat ⇒ 2)
               
;; -----------------------------------------------------------------------------
;; --- Functions in union

(check-type (λ ([x : (∪ Int (∪ Nat) (∪ (→ Int String Int)) (→ (→ (→ Int Int)) Int))]) #t)
            : (→ (∪ Int Nat (→ Int String Int) (→ (→ (→ Int Int)) Int)) Bool))

(check-type (λ ([x : (∪ Int (→ Int Int))]) #t)
            : (→ Int Bool))

;; --- filter functions
(check-type
 (λ ([x : (∪ Int (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
          x))
 : (→ (∪ Int (→ Int Int)) Int))

(check-type
 (λ ([x : (∪ (→ Int Int Int) (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0))))
 : (→ (∪ (→ Int Int Int) (→ Int Int)) Int))

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) 1)
 : Int ⇒ 1)

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int]) 5))
 : Int ⇒ 5)

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int] [z : Int]) z))
 : Int ⇒ 0)

;; --- disallow same-arity functions
(typecheck-fail
 (λ ([x : (∪ (→ Int Int) (→ String String))]) 1)
 #:with-msg "Cannot discriminate")

;; -----------------------------------------------------------------------------
;; --- Filter with unions

(check-type
 (λ ([x : (∪ Int String)])
  (test ((∪ Int String) ? x)
        x
        "nope"))
 : (→ (∪ Int String) (∪ Int String)))

(check-type
 (λ ([x : (∪ Int String Bool)])
    (test ((∪ Int String) ? x)
          x
          "Nope"))
 : (→ (∪ Int String Bool) (∪ Int String)))

(check-type
 (λ ([x : (∪ Int String Bool)])
    (test ((∪ Int String) ? x)
          (test (String ? x)
                "yes"
                "int")
          "bool"))
 : (→ (∪ Int String Bool) String))

(check-type-and-result
 ((λ ([x : (∪ String Bool)])
     (test ((∪ Int Nat Num) ? x)
           x
           (+ 1 2))) "hi")
 : Num ⇒ 3)

(check-type-and-result
  ((λ ([x : (∪ String Int Bool)])
      (test ((∪ Int String) ? x)
            x
            "error")) 1)
  : (∪ String Int) ⇒ 1)

(check-type-and-result
  ((λ ([x : (∪ String Int Bool)])
      (test ((∪ Int String) ? x)
            x
            "error")) "hi")
  : (∪ Int String) ⇒ "hi")

;; -----------------------------------------------------------------------------
;; --- Subtyping products

(check-type (tup 1) : (× Nat))
(check-type (tup 1) : (× Int))
(check-type (tup 1) : (× Num))
(check-type (tup 1) : (× Top))
(check-type (tup 1) : Top)

(check-not-type (tup 1) : Bool)
(check-not-type (tup 1) : String)
(check-not-type (tup 1) : (× String))
(check-not-type (tup 1) : (× Int String))
(check-not-type (tup 1) : Bot)

(check-type (tup 1 2 3) : (× Int Nat Num))
(check-type (tup 1 2 3) : (× Num Nat Num))
(check-type (tup 1 2 3) : (× Top Top Num))
(check-type (tup 1 "2" 3) : (× Int Top Int))

(check-not-type (tup 1 2 3) : (× Nat Nat String))

;; -----------------------------------------------------------------------------
;; --- Latent filters (on products)

(check-type
 (λ ([v : (× (∪ Int String) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
 : (→ (× (∪ Int String) Int) Num))

(check-type-and-result
 ((λ ([v : (× (∪ Int String) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
  (tup ((λ ([x : (∪ Int String)]) x) -2) -3))
 : Num ⇒ -5)

(check-type-and-result
 ((λ ([v : (× (∪ Int String) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
  (tup "hi" -3))
 : Num ⇒ 0)

;; --- Use a product as filter

(check-type
 (λ ([x : (∪ Int (× Int Int Int))])
    (test (Int ? x)
          (+ 1 x)
          (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
 : (→ (∪ (× Int Int Int) Int) Num))

(check-type-and-result
 ((λ ([x : (∪ Int (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
  0)
 : Num ⇒ 1)

(check-type-and-result
 ((λ ([x : (∪ Int (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
  (tup 2 2 2))
 : Num ⇒ 6)

(check-type-and-result
 ((λ ([x : (∪ Int (× String Nat) (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
     (test ((× Int Int Int) ? x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))
           (proj x 1))))
  (tup 2 2 2))
 : Num ⇒ 6)

(check-type-and-result
 ((λ ([x : (∪ Int (× String Nat) (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
     (test ((× Int Int Int) ? x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))
           (proj x 1))))
  (tup "yolo" 33))
 : Num ⇒ 33)

;; -- All together now

(check-type-and-result
 ((λ ([x : (∪ Int (× Bool Bool) (× Int (∪ String Int)))])
     (test (Int ? x)
           "just an int"
     (test ((× Bool Bool) ? x)
           "pair of bools"
           (test (String ? (proj x 1))
                 (proj x 1)
                 "pair of ints"))))
  (tup 33 "success"))
 : String ⇒ "success")

(check-type-and-result
 ((λ ([x : (∪ Int (× Int Int) (× Int (∪ String Int)))])
     (test (Int ? x)
           "just an int"
     (test ((× Int Int) ? x)
           "pair of ints"
           (test (String ? (proj x 1))
                 (proj x 1)
                 "another pair of ints"))))
  (tup 33 "success"))
 : String ⇒ "success")

;; -----------------------------------------------------------------------------
;; --- Filter lists

(check-type
 (λ ([x : (List (∪ Int String))])
    (test ((List String) ? x)
          x
          #f))
 : (→ (List (∪ Int String)) (∪ Bool (List String))))

;; -- -subtyping lists
(check-type
 (cons 1 (nil {Nat}))
 : (List Int))

(check-type
 ((λ ([filter/3 : (→ (List (∪ Int String)) (List Int))]
      [add*/3 : (→ Num (List Num) (List Num))]
      [xs : (×  (∪ Int String) (∪ Int String) (∪ Int String))])
     (add*/3 5 (filter/3 (cons (proj xs 0)
                               (cons (proj xs 1)
                                     (cons (proj xs 2)
                                           (nil {(∪ String Int)})))))))
  ;; filter (okay this is a little tricky for recursion)
  (λ ([xs : (List (∪ Int String))])
     ((λ ([v1 : (∪ Int String)]
          [v2 : (∪ Int String)]
          [v3 : (∪ Int String)])
         (test (Int ? v1)
               (cons v1 (test (Int ? v2)
                              (cons v2 (test (Int ? v3)
                                             (cons v3 (nil {Int}))
                                             (nil {Int})))
                              (test (Int ? v3)
                                    (cons v3 (nil {Int}))
                                    (nil {Int}))))
               (test (Int ? v2)
                     (cons v2 (test (Int ? v3)
                                    (cons v3 (nil {Int}))
                                    (nil {Int})))
                     (test (Int ? v3)
                           (cons v3 (nil {Int}))
                           (nil {Int})))))
      (head xs) (head (tail xs)) (head (tail (tail xs)))))
  ;; add3
  (λ ([n : Num] [xs : (List Num)])
     (cons (+ n (head xs))
      (cons (+ n (head (tail xs)))
       (cons (+ n (head (tail (tail xs))))
        (nil {Num})))))
  ;; xs (3-tuple)
  (tup 1 "foo" 3))
 : (List Num))

;; -----------------------------------------------------------------------------
;; --- ICFP'10 examples

;; -- Exaple 1 (x can have any type)
(check-type
 (λ ([x : Top])
    (test (Num ? x)
       (+ 1 x)
       0))
 : (→ Top Num))

;; -- Example 2
(check-type
 (λ ([x : (∪ String Num)]
     [str-length : (→ String Num)])
    (test (Num ? x)
          (+ 1 x)
          (str-length x)))
 : (→ (∪ String Num) (→ String Num) Num))

;; -- TODO Example 3 (requires IF)
;; (check-type
;;  (λ ([member : (→ Num (List Num) Bool)])
;;     (λ ([x : Num] [l : (List Num)])
;;        (if (member x l)
;;            <compute with x>
;;            <fail>)))
;;  : <compute-result>

;; -- Example 4
(check-type
 (λ ([x : (∪ Num String Top)] [f : (→ (∪ Num String) Num)])
    (test ((∪ Num String) ? x)
          (f x)
          0))
 : (→ (∪ Num String Top) (→ (∪ Num String) Num) Num))

;; Exmample 10 (we don't allow non-homogenous lists, so need to select head before filtering)
(check-type
 (λ ([p : (List (∪ Nat String))])
    ((λ ([x : (∪ Nat String)])
       (test (Num ? x)
             (+ 1 x)
             7))
    (head p)))
 : (→ (List (∪ Nat String)) Num))

;; -----------------------------------------------------------------------------
;; --- TODO CPS filters

;; -----------------------------------------------------------------------------
;; --- TODO Filter on values (should do nothing)

;; (check-type
;;  (test (Int ? 1) #t #f)
;;  : Bool)

;; -----------------------------------------------------------------------------
;; --- TODO Values as filters (check equality)

