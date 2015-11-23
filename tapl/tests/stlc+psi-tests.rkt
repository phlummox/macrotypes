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

;; --- fail

(typecheck-fail
 (signature (α) Int)
 #:with-msg "Cannot declare")

(typecheck-fail
 (signature () (→ Int Int))
 #:with-msg "Improper usage")

(typecheck-fail
 (signature (a b c) (→ a b))
 #:with-msg "Cannot declare signature")

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
 #:with-msg "Different length domains")

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

;; Missing type variables = bad use of constructor
(typecheck-fail
 (λ ([f : (ψ () (§ Int) (→ Int Int))]) 3)
 #:with-msg "Improper usage of type constructor")

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

(typecheck-fail
 ((instance
   (instance (signature (α) (→ α Str))
             (λ ([x : Nat]) "nat"))
   (λ ([x : Boolean]) "bool"))
  -1)
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

(check-type
 (λ ([enum : (ψ (A) (§ Int) (→ A Int))])
    (enum 4))
 : (→ (ψ (A) (§ Int) (→ A Int)) Int))

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

;; --- some failures

(typecheck-fail
 (λ ([enum : (ψ (A) (§ Boolean) (→ A Int))])
    (enum 4))
 #:with-msg "No matching instance")

;; Annotation mismatch, even thought 'Boolean' is never used
(typecheck-fail
 ((λ ([enum : (ψ (A) (§ Boolean Int) (→ A Int))])
     (enum 4))
  (instance 
    (signature (A) (→ A Int))
   (λ ([x : Int]) 1)))
 #:with-msg "Arguments to function")

(typecheck-fail
 (λ ([enum : (ψ (A) (§ Nat) (→ A Int))])
    (enum -4))
 #:with-msg "No matching instance")

;; -----------------------------------------------------------------------------

(check-type
  (signature (A) (→ A A Boolean))
  : (ψ (A) (§) (→ A A Boolean)))

(check-type
  (instance 
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Int]) #t))
  : (ψ (A) (§ Int) (→ A A Boolean)))

(check-type
 (resolve
  (instance 
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Int]) #t))
  Int)
 : (→ Int Int Boolean))

(check-type
 (resolve
  (instance
   (instance 
    (signature (A) (→ A A Boolean))
    (λ ([x : Int] [y : Int]) #t))
   (λ ([x : Boolean] [y : Boolean]) x))
  Int)
 : (→ Int Int Boolean))

(check-type-and-result
 ((resolve
   (instance
    (instance 
     (signature (A) (→ A A Boolean))
     (λ ([x : Int] [y : Int]) #t))
    (λ ([x : Boolean] [y : Boolean]) x))
   Boolean) #t #f)
 : Boolean
 ⇒ #t)

(check-type-and-result
 ((resolve
   (instance
    (instance 
     (signature (A) (→ A A Boolean))
     (λ ([x : Int] [y : Int]) #t))
    (λ ([x : Boolean] [y : Boolean]) x))
   Boolean) #f #t)
 : Boolean
 ⇒ #f)

;; --- eq fails

(typecheck-fail
  (instance 
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Boolean]) #t))
  #:with-msg "Incompatible types")

(typecheck-fail
  (instance 
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Int]) x))
  #:with-msg "Cannot unify")

(typecheck-fail
 (resolve
  (instance 
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Int]) #t))
  Boolean)
 #:with-msg "No matching instance")

;; --- types in signature may be replaced with <:, rather than strict equals

(check-type
  (instance
   (signature (α) (→ α Int Int Boolean))
   (λ ([a : Num] [b : Int] [c : Int]) #f))
  : (ψ (α) (§ Num) (→ α Int Int Boolean)))

(check-type
  (instance
   (signature (α) (→ α Int Int Boolean))
   (λ ([a : Num] [b : Num] [c : Int]) #f))
  : (ψ (α) (§ Num) (→ α Int Int Boolean)))

(check-type
  (instance
   (signature (α) (→ α Int Int Boolean))
   (λ ([a : Num] [b : Int] [c : Num]) #f))
  : (ψ (α) (§ Num) (→ α Int Int Boolean)))

(typecheck-fail
  (instance
   (signature (α) (→ α Int Int Boolean))
   (λ ([a : Num] [b : Nat] [c : Nat]) #f))
  #:with-msg "does not match signature")

;; -- overload at constructors (not simple) types

(check-type
 (instance
  (signature (α) (→ α Int Int))
  (λ ([f : (→ Int Int)] [x : Int]) (f x)))
 : (ψ (α) (§ (→ Int Int)) (→ α Int Int)))

(check-type
 ((resolve
   (instance
    (instance
     (signature (α) (→ α Int Int))
     (λ ([f : (→ Int Int)] [x : Int]) (f x)))
    (λ ([x : Boolean] [y : Int]) -1))
   (→ Int Int)) (λ ([x : Int]) x) 5)
  : Int
  ⇒ 5)

;; #%app resolve
(check-type-and-result
 ((instance
    (instance 
     (signature (A) (→ A A Boolean))
     (λ ([x : Int] [y : Int]) #t))
    (λ ([x : Boolean] [y : Boolean]) x))
   #f #t)
 : Boolean
 ⇒ #f)

;; dynamic resolve
(check-type-and-result
 ((λ ([f : (ψ (B) (§ Boolean) (→ B B Boolean))])
     (f #f #t))
  (instance
   (instance 
    (signature (A) (→ A A Boolean))
    (λ ([x : Int] [y : Int]) #t))
   (λ ([x : Boolean] [y : Boolean]) x)))
 : Boolean
 ⇒ #f)

(check-type-and-result
 ((λ ([x : (ψ (A) (§ (→ Int Int)) (→ A Int Int))])
     ((resolve x (→ Int Int)) (λ ([y : Int]) y) 5))
  (instance
   (instance
    (signature (α) (→ α Int Int))
    (λ ([f : (→ Int Int)] [x : Int]) (f x)))
   (λ ([x : Boolean] [y : Int]) -1)))
 : Int
 ⇒ 5)

;; dynamic resolve with subtyping
(check-type-and-result
 ((λ ([f : (ψ (B) (§ Int) (→ B B Boolean))])
     (f 1 2))
  (instance
   (instance 
    (signature (A) (→ A A Boolean))
    (λ ([x : Int] [y : Int]) #t))
   (λ ([x : Boolean] [y : Boolean]) x)))
 : Boolean
 ⇒ #t)

(check-type-and-result
 ((λ ([f : (ψ (B) (§ Nat) (→ B B Boolean))])
     (f 1 2))
  (instance
   (instance 
    (signature (A) (→ A A Boolean))
    (λ ([x : Nat] [y : Nat]) #t))
   (λ ([x : Boolean] [y : Boolean]) x)))
 : Boolean
 ⇒ #t)

(typecheck-fail
 ((λ ([f : (ψ (B) (§ Nat) (→ B B Boolean))])
     (f -1 -2))
  (instance
   (instance 
    (signature (A) (→ A A Boolean))
    (λ ([x : Nat] [y : Nat]) #t))
   (λ ([x : Boolean] [y : Boolean]) x)))
 #:with-msg "No matching instance")

(check-type-and-result
 ((λ ([f : (ψ (B) (§ Int) (→ B B Boolean))])
     (f -1 2))
  (instance
   (signature (A) (→ A A Boolean))
   (λ ([x : Int] [y : Int]) #t)))
 : Boolean
 ⇒ #t)

;; -----------------------------------------------------------------------------
;; --- multiple type parameters

(check-type
 (signature (A B) (→ A B A Int))
 : (ψ (X Y) (§) (→ X Y X Int)))

(typecheck-fail
 (signature (A B) (→ A Int))
 #:with-msg "must appear")

(typecheck-fail
 (signature (A B C) (→ A B A Int))
 #:with-msg "must appear")


(check-type
 (signature (A B) (→ A B A Int))
 : (ψ (X Y) (§) (→ X Y X Int)))

(check-type
 (instance
  (signature (A B) (→ A B A Int))
  (λ ([x : Int] [y : Boolean] [z : Int])
     x))
: (ψ (X Y) (§ (· Int Boolean)) (→ X Y X Int)))

(typecheck-fail
 (resolve
  (instance
   (signature (A B) (→ A B A Int))
   (λ ([x : Int] [y : Boolean] [z : Int])
      x))
  Int Int)
  #:with-msg "No matching instance")

(check-type
 (resolve
  (instance
   (signature (A B) (→ A B A Int))
   (λ ([x : Int] [y : Boolean] [z : Int])
      x))
  Int Boolean)
: (→ Int Boolean Int Int))

(check-type-and-result
 ((instance
   (signature (A B) (→ A B A Int))
   (λ ([x : Int] [y : Boolean] [z : Int])
      x))
  1 #t 2)
 : Int
 ⇒ 1)

(typecheck-fail
 ((instance
   (signature (A B) (→ A B A Int))
   (λ ([x : Int] [y : Boolean] [z : Int])
      x))
  1 #t #f)
 #:with-msg "Incompatible types")

(check-type
 (λ ([x : (ψ (A B) (§ (· Int Int) (· Int Boolean)) (→ A B A))])
    (x 1 #f))
 ;; Types should de-duplicate and sort
 : (→ (ψ (X Y) (§ (· Int Boolean) (· Int Int) (· Int Int)) (→ X Y X)) Int))

(check-type-and-result
 ((instance
   (signature (A B) (→ A B A Int))
   (λ ([x : Int] [y : Boolean] [z : Int])
      x))
  1 #t 2)
 : Int
 ⇒ 1)
