#lang s-exp "../stlc+psi.rkt"
(require "rackunit-typechecking.rkt")

;; TODO more passing examples for sig + instance

;; ----------------------------------------------------------------------------------------
;; -- signature

;; --- pass

(check-type
 (signature (β) (→ β Str))
 : (ψ (β) (§) (→ β Str)))

;; --- fail

(typecheck-fail
 (signature (α) Int)
 #:with-msg "Cannot declare")

(typecheck-fail
 (signature () (→ Int Int))
 #:with-msg "expected more terms")

(typecheck-fail
 (signature (a b c) (→ a b))
 #:with-msg "unexpected term")

(typecheck-fail
 (signature (a) (→ Int a))
 #:with-msg "Cannot declare")

;; -----------------------------------------------------------------------------
;; -- instance

;; --- pass

(check-type
 (instance (signature (α) (→ α Str))
           (λ ([x : Int]) "int"))
 : (ψ (β) (§ Int) (→ β Str)))

;; --- fail

(typecheck-fail
 (instance 4 6)
 #:with-msg "")

(typecheck-fail
 (instance "yolo" (λ ([x : Int]) "hi"))
 #:with-msg "cannot declare instance")

(typecheck-fail
 (instance (signature (a) (→ a Int))
           3)
 #:with-msg "only → types can be instances")

;; -----------------------------------------------------------------------------
;; -- resolve

;; --- pass
(check-type
 (resolve
  (instance
   (signature (α) (→ α Str))
   (λ ([x : Int]) "int"))
  Int)
 : (→ Int Str))

(check-type-and-result
 ((resolve
   (instance (signature (α) (→ α Str))
             (λ ([x : Nat]) "nat"))
   Nat) 3)
 : Str ⇒ "nat")

(check-type-and-result
 ((resolve
   (instance
    (instance (signature (α) (→ α Str))
              (λ ([x : Nat]) "nat"))
    (λ ([x : Boolean]) "bool"))
   Nat)
  3)
 : Str ⇒ "nat")

(check-type-and-result
 ((resolve
   (instance
    (instance (signature (α) (→ α Str))
              (λ ([x : Nat]) "nat"))
    (λ ([x : Boolean]) "bool"))
   Boolean)
  #f)
 : Str ⇒ "bool")

;; --- fail

(typecheck-fail
 (resolve
  (signature (a) (→ a Boolean))
  Boolean)
 #:with-msg "No matching instance")

(typecheck-fail
 (resolve
  (instance
   (signature (a) (→ a Boolean))
   (λ ([x : Boolean]) #t))
  Nat)
 #:with-msg "No matching instance")

;; --- TODO implicit resolve
;; --- TODO 

