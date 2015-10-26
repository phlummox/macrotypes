#lang s-exp "../stlc+occurrence+tup.rkt"
(require "rackunit-typechecking.rkt")

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

