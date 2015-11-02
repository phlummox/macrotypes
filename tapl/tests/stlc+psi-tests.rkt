#lang s-exp "../stlc+psi.rkt"
(require "rackunit-typechecking.rkt")

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

;; ;; --- TODO more instances, resolvers
