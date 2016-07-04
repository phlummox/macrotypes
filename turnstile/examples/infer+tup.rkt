#lang turnstile
(extends "infer+match.rkt")
(require (only-in "infer+match.rkt" λ [#%app infer:#%app]))
(require (only-in "stlc+tup.rkt" × ~× [tup stlc:tup]))
(require "infer-utils.rkt")

(define-typed-syntax tup
  [(tup e ...) ≫
   [#:with [x ...] (generate-temporaries #'[e ...])]
   --------
   [_ ≻ (infer:#%app (λ (x ...) (stlc:tup x ...)) e ...)]])

(define-typed-syntax tup:
  [(tup pat ...) ≫
   [⊢ [[pat ≫ _] ⇒ : τ_pat*] ...]
   [#:with [(~?Some [V1 ...] (~?∀* (V2 ...) (~Pat τ_pat pat- (ctx ...))) (~Cs [τ_1 τ_2] ...)) ...]
    (syntax-local-introduce #'[τ_pat* ...])]
   [#:with τ_out (some/inst/generalize #'[V1 ... ... V2 ... ...]
                                       #`(Pat
                                          #,(tycons #'× #'[τ_pat ...])
                                          (list pat- ...)
                                          (ctx ... ...))
                                       #'([τ_1 τ_2] ... ...))]
   --------
   [⊢ [[_ ≫ #f] ⇒ : τ_out]]])

