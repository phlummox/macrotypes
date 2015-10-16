#lang s-exp "typecheck.rkt"
(extends "stlc+lit.rkt" #:except #%datum +)

;; Simply-Typed Lambda Calculus, plus subtyping
;; Types:
;; - types from and stlc+lit.rkt
;; - Top, Num, Nat
;; Type relations:
;; - sub?
;;   - Any <: Top
;;   - Nat <: Int
;;   - Int <: Num
;;   - →
;; Terms:
;; - terms from stlc+lit.rkt, except redefined: datum and +
;; - also *
;; Other: sub? current-sub?

(define-base-type Top)
(define-base-type Num #:sub? (λ (this other) (Top? other)))
(define-base-type Int #:sub? (λ (this other) (typecheck? (expand/df #'Num) other)))
(define-base-type Nat #:sub? (λ (this other) (typecheck? (expand/df #'Int) other)))

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))

(define-typed-syntax #%datum
  [(_ . n:nat) (⊢ (#%datum . n) : Nat)]
  [(_ . n:integer) (⊢ (#%datum . n) : Int)]
  [(_ . n:number) (⊢ (#%datum . n) : Num)]
  [(_ . x) #'(stlc+lit:#%datum . x)])
           
