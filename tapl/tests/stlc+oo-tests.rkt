#lang s-exp "../stlc+oo.rkt"
(require "rackunit-typechecking.rkt")

(signature (to-string α) (→ α String))

;; -- overload at union type

(instance (to-string (∪ Int String))
          (λ ([x : (∪ Int String)])
             (test (Int ? x)
                   "int"
                   "str")))

(check-type-and-result
 (to-string 42)
 : String ⇒ "int")

(check-type-and-result
 (to-string "hello")
 : String ⇒ "str")

(check-type-and-result
 ((λ ([x : (∪ String Int)])
     (to-string x))
  1)
 : String ⇒ "int")

(check-type-and-result
 ((λ ([x : (∪ String Int)])
     (to-string x))
  "two")
 : String ⇒ "str")

;; -- just checking subtyping

(typecheck-fail
 (to-string (+ 1 1))
 #:with-msg "Could not resolve instance")

(typecheck-fail
 (to-string 3.14)
 #:with-msg "Could not resolve instance")

;; -- 

(check-type-and-result
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  "two")
 : String ⇒ "str")

(check-type-and-result
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  6)
 : String ⇒ "int")

(check-type
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  #t)
 : String)

(runtime-fail
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  #t)
 #:with-msg "Dynamic resolution failed")

;; Sneaks by, because 2 passes the predicate for integers
(check-type-and-result
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  (+ 1 1))
 : String ⇒ "int")

(check-type
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  3.14)
 : String)

(runtime-fail
 ((λ ([x : (∪ String Int Bool Num)])
     (to-string x))
  3.14)
 #:with-msg "Dynamic resolution failed")

;; Dynamic resolution can't possibly succeed
(typecheck-fail
 (λ ([x : (∪ Bool Num)])
    (to-string x))
 #:with-msg "Could not resolve instance")
