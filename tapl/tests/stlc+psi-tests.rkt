#lang s-exp "../stlc+psi.rkt"
(require "rackunit-typechecking.rkt")

;; ----------------------------------------------------------------------------------------

;; -- signature failures

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

;; --- instance failures

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

(check-type
 (signature (β) (→ β String))
 : (ψ (β) (§) (→ β String)))

(check-type
 (instance (signature (α) (→ α String))
           (λ ([x : Int]) "int"))
 : (ψ (β) (§ Int) (→ β String)))
