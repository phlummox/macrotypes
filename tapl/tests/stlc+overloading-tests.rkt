#lang s-exp "../stlc+overloading.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; --- Invalid signatures

(typecheck-fail
 (signature (to-string0 α) (→ α String String))
 #:with-msg "Expected")

(typecheck-fail
 (signature (to-string0 α) (→ String String))
 #:with-msg "Expected")

(typecheck-fail
 (signature (to-string0 α) (→ α String))
 #:with-msg "not allowed in an expression context")

;; -----------------------------------------------------------------------------
;; --- basic overloading

(signature (to-string α) (→ α String))

(typecheck-fail
 (to-string 1)
 #:with-msg "Could not resolve instance")

(typecheck-fail
 (to-string "yolo")
 #:with-msg "Could not resolve instance")

;; -- can later add cases to an overloaded name
(instance (to-string Nat)
  (λ ([x : Nat]) "nat"))

(instance (to-string String)
  (λ ([x : String]) "string"))

(check-type-and-result
 (to-string 3)
 : String ⇒ "nat")

(typecheck-fail
 (to-string (+ 0 0))
 #:with-msg "Could not resolve instance")

(instance (to-string Num)
  (λ ([x : Num]) "num"))

(check-type-and-result
 (to-string (+ 2 2))
 : String ⇒ "num")

(check-type-and-result
 (to-string -1)
 : String ⇒ "num")

(check-type-and-result
 (to-string "hi")
 : String ⇒ "string")

;; -- use 'resolve' to get exact matches

(check-type-and-result
 ((resolve to-string Nat) 1)
 : String ⇒ "nat")

(check-type-and-result
 ((resolve to-string Num) 1)
 : String ⇒ "num")

(typecheck-fail
 (resolve to-string Int)
 #:with-msg "Could not resolve instance")

(typecheck-fail
 ((resolve to-string Num) "hello")
 #:with-msg "have wrong type")

;; -- instances are type-checked. They must match
(typecheck-fail
 (instance (to-string Int)
           (λ ([x : Num]) "num"))
 #:with-msg "must be the instance type")

(typecheck-fail
 (instance (to-string Int)
           (λ ([x : Int]) 0))
 #:with-msg "must match template codomain")

(typecheck-fail
 (instance (to-string Int)
           42)
 #:with-msg "May only overload single-argument functions")

;; -- no overlapping instances
(typecheck-fail
 (instance (to-string Nat)
           (λ ([x : Nat]) "wrong"))
 #:with-msg "Overlaps with existing instance")

;; -- can't instantiate non-overloadeds
(typecheck-fail
 (λ ([x : (→ Int Int)])
   (instance (x Int)
             0))
 #:with-msg "Identifier 'x' is not overloaded")

;; -- explicit resolve

;; -- recursive instances are fine [TODO really want (List α)]
(instance (to-string (List Nat))
          (λ ([x : (List Nat)]) "listnat"))

(check-type-and-result
 (to-string (cons 1 (cons 2 (nil {Nat}))))
 : String ⇒ "listnat")

;; TODO also tuples, (\times \alpha Int)

;; -- higher-order use

