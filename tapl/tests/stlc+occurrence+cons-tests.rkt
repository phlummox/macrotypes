#lang s-exp "../stlc+occurrence+cons.rkt"
(require "rackunit-typechecking.rkt")

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


;; ICFP Example 10
;; (we don't allow non-homogenous lists, so need to select head before filtering)
(check-type
 (λ ([p : (List (∪ Nat String))])
    ((λ ([x : (∪ Nat String)])
       (test (Num ? x)
             (+ 1 x)
             7))
    (head p)))
 : (→ (List (∪ Nat String)) Num))
