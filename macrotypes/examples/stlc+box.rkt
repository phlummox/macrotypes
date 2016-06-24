#lang s-exp macrotypes/typecheck
(extends "stlc+cons.rkt")

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(define-type-constructor Ref)

(define-typed-syntax ref
  [(ref e)
   #:with (e- τ) (infer+erase #'e)
   (⊢ (box- e-) : (Ref τ))])
(define-typed-syntax deref
  [(deref e)
   #:with (e- (τ)) (⇑ e as Ref)
   (⊢ (unbox- e-) : τ)])
(define-typed-syntax := #:literals (:=)
  [(:= e_ref e)
   #:with (e_ref- (τ1)) (⇑ e_ref as Ref)
   #:with (e- τ2) (infer+erase #'e)
   #:when (typecheck? #'τ1 #'τ2)
   (⊢ (set-box!- e_ref- e-) : Unit)])