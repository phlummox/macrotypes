#lang s-exp "../stlc+psi.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; ∀-sub? tests

;; --- succeed

(check-type
 (Λ (a) 3)
 : (∀ (t) Int))

(check-type
 (Λ (a) 3)
 : (∀ (t) Num))

(check-type
 (Λ (a) (λ ([x : a]) x))
 : (∀ (t) (→ Bot t)))

(check-type
  (Λ (a) (λ ([x : Int]) x))
  : (∀ (t) (→ Int Int)))

(check-type
  (Λ (a) (λ ([x : Int]) x))
  : (∀ (t) (→ Int Num)))

(check-type
  (Λ (a) (λ ([x : Int]) x))
  : (∀ (t) (→ Nat Num)))

(check-type
  (Λ (a) (λ ([x : a]) 3))
  : (∀ (A) (→ A Int)))

(check-type
  (Λ (a) (λ ([x : a]) 3))
  : (∀ (A) (→ A Num)))

(check-type
  (Λ (a) (λ ([x : Int] [y : a]) y))
  : (∀ (A) (→ Nat A A)))

(check-type
  (Λ (a) (λ ([x : Int]) (Λ (b) (λ ([y : b] [x : a]) x))))
  : (∀ (A) (→ Int (∀ (B) (→ B A A)))))

(check-type
  (Λ (a) (λ ([x : Int]) (Λ (b) (λ ([y : b] [x : a]) x))))
  : (∀ (A) (→ Nat (∀ (B) (→ B A A)))))

;; --- fail

(check-not-type
 (Λ (a) (λ ([x : a]) x))
 : (∀ (t) (→ Int t)))

(check-not-type
  (Λ (a) (λ ([x : Int]) x))
  : (∀ (t) (→ Int Nat)))

(check-not-type
 (Λ (a) (λ ([x : a]) x))
 : (∀ (t) (→ t Int)))

(check-not-type
  (Λ (a) (λ ([x : Int]) x))
  : (∀ (t) (→ Num Nat)))

(check-not-type
  (Λ (a) (λ ([x : a]) 3))
  : (∀ (A) (→ A A)))

(check-not-type
  (Λ (a) (λ ([x : a]) -3))
  : (∀ (A) (→ A Nat)))

(check-not-type
  (Λ (a) (λ ([x : Int] [y : a]) y))
  : (∀ (A) (→ Num A A)))

(check-not-type
  (Λ (a) (λ ([x : Int]) (Λ (b) (λ ([y : b] [x : a]) x))))
  : (∀ (A) (→ Num (∀ (B) (→ B A A)))))

;; ----------------------------------------------------------------------------------------
;; -- signature

;; --- pass

(check-type
 (signature (β) (→ β Str))
 : (ψ (β) (§) (→ β Str)))

;; α-equivalence works
(check-type
 (signature (a) (→ a Boolean))
 : (ψ (b) (§) (→ b Boolean)))

;; TODO more shapes

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

(check-type
 (instance
  (instance
   (instance (signature (a) (→ a Int))
             (λ ([x : Int]) -42))
   (λ ([x : Nat]) -42))
  (λ ([x : Boolean]) -42))
 : (ψ (x) (§ Int Nat Boolean) (→ x Int)))

;; § are ordered and de-duplicated
(check-type
 (instance
  (instance
   (instance (signature (a) (→ a Int))
             (λ ([x : Int]) -42))
   (λ ([x : Nat]) -42))
  (λ ([x : Boolean]) -42))
 : (ψ (x) (§ Int Int Int Nat Int Boolean) (→ x Int)))

;; --- fail

;; Not overloadable
(typecheck-fail
 (instance 4 6)
 #:with-msg "")

;; Not overloadable
(typecheck-fail
 (instance "yolo" (λ ([x : Int]) "hi"))
 #:with-msg "cannot declare instance")

;; Not overloading at a function type
(typecheck-fail
 (instance (signature (a) (→ a Int))
           3)
 #:with-msg "only → types can be instances")

;; Instance type doesn't match sig
(typecheck-fail
 (instance (signature (a) (→ a Str))
           (λ ([x : Int]) x))
 #:with-msg "Cannot unify")

(typecheck-fail
 (instance (signature (a) (→ a Str))
           (λ ([x : Str]) 1))
 #:with-msg "Cannot unify")

(typecheck-fail
 (instance (signature (a) (→ a Str))
           (λ ([x : Int] [y : Int]) "hi"))
 #:with-msg "non-overloadable type") ;; bad error message

;; Okay, because subtyping
(check-type
 (instance (signature (A) (→ A Boolean))
           (λ ([x : Int]) #t))
 : (ψ (B) (§) (→ B Boolean)))

;; Wrong carrier
(check-not-type
 (instance (signature (A) (→ A Boolean))
           (λ ([x : Int]) #t))
 : (ψ (B) (§ B) (→ B Boolean)))

;; Too-large carrier
(check-not-type
 (instance (signature (A) (→ A Boolean))
           (λ ([x : Int]) #t))
 : (ψ (B) (§ Int Boolean) (→ B Boolean)))

;; TODO why "improper usage of ψ" ?
;; Missing type variables
;; (check-not-type
;;  (instance (signature (A) (→ A Boolean))
;;            (λ ([x : Int]) #t))
;;  : (ψ () (§ Int) (→ B Boolean)))

;; Too many type variables
;; (check-not-type
;;  (instance (signature (A) (→ A Boolean))
;;            (λ ([x : Int]) #t))
;;  : (ψ (A B C) (§ Int) (→ B Boolean)))

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

;; -- implicit resolve

(check-type
 ((instance
   (instance (signature (α) (→ α Str))
             (λ ([x : Nat]) "nat"))
   (λ ([x : Boolean]) "bool"))
  #t)
 : Str)

(check-type-and-result
 ((instance
   (instance (signature (α) (→ α Str))
             (λ ([x : Nat]) "nat"))
   (λ ([x : Boolean]) "bool"))
  #t)
 : Str ⇒ "bool")

(check-type-and-result
 ((instance
   (instance (signature (α) (→ α Str))
             (λ ([x : Int]) "num"))
   (λ ([x : Boolean]) "bool"))
  1)
 : Str ⇒ "num")

;; ;; TODO λ

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

;; -----------------------------------------------------------------------------
;; -- lambda

(check-type
 ((λ ([enum : (ψ (A) (§ Int Boolean) (→ A Int))])
     (enum 4))
  (instance 
   (instance
    (signature (A) (→ A Int))
    (λ ([x : Boolean]) 0))
   (λ ([x : Int]) 1)))
 : Int)

(check-type-and-result
 ((λ ([enum : (ψ (A) (§ Int Boolean) (→ A Int))])
     (enum 4))
  (instance 
   (instance
    (signature (A) (→ A Int))
    (λ ([x : Boolean]) 0))
   (λ ([x : Int]) 1)))
 : Int ⇒ 1)

(check-type-and-result
 ((λ ([enum : (ψ (A) (§ Int Boolean) (→ A Int))])
     (enum #t))
  (instance 
   (instance
    (signature (A) (→ A Int))
    (λ ([x : Boolean]) 0))
   (λ ([x : Int]) 1)))
 : Int ⇒ 0)

;; --- less-specific arg type
(check-type-and-result
 ((λ ([enum : (ψ (A) (§ Int) (→ A Int))])
     (enum 4))
  (instance 
   (instance
    (signature (A) (→ A Int))
    (λ ([x : Boolean]) 0))
   (λ ([x : Int]) 1)))
 : Int ⇒ 1)

;; --- less-specific result
(check-type-and-result
 ((λ ([enum : (ψ (A) (§ Int Boolean) (→ A Num))])
     (enum 4))
  (instance 
   (instance
    (signature (A) (→ A Int))
    (λ ([x : Boolean]) 0))
   (λ ([x : Int]) 1)))
 : Num ⇒ 1)

;; lambda, resolve S=t to a plain arrow
;; lambda, infer use (via flow) on a poly, resolve to plain arrow
;; var-arity, one arg instantiates the rest
