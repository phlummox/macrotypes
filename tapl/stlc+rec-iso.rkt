#lang s-exp "typecheck.rkt"
(extends "stlc+tup.rkt")
(reuse ∨ var case define-type-alias define #:from "stlc+reco+var.rkt")

;; stlc + (iso) recursive types
;; Types:
;; - types from stlc+tup.rkt
;; - also ∨ from stlc+reco+var
;; - μ
;; Terms:
;; - terms from stlc+tup.rkt
;; - also var and case from stlc+reco+var
;; - fld, unfld
;; Other:
;; - extend type=? to handle lambdas

(define-type-constructor μ #:arity = 1 #:bvs = 1
  #:sub? (λ (τ1 τ2)
           (syntax-parse (list τ1 τ2)
             [(((~literal #%plain-app) tycon1 ((~literal #%plain-lambda) (x:id ...) t1 ...))
               ((~literal #%plain-app) tycon2 ((~literal #%plain-lambda) (y:id ...) t2 ...)))
              #:with (z ...) (generate-temporaries #'(x ...))
              (and (stx-length=? #'(x ...) #'(y ...))
                   (stx-length=? #'(t1 ...) #'(t2 ...))
                   (stx-andmap
                    (λ (t1 t2)
                      (type=? (substs #'(z ...) #'(x ...) t1)
                              (substs #'(z ...) #'(y ...) t2)))
                    #'(t1 ...) #'(t2 ...)))]
             [_ #f])))

(define-typed-syntax unfld
  [(_ τ:type-ann e)
   #:with (~μ* (tv) τ_body) #'τ.norm
   #:with [e- τ_e] (infer+erase #'e)
   #:when (typecheck? #'τ_e #'τ.norm)
   (⊢ e- : #,(subst #'τ.norm #'tv #'τ_body))])
(define-typed-syntax fld
  [(_ τ:type-ann e)
   #:with (~μ* (tv) τ_body) #'τ.norm
   #:with [e- τ_e] (infer+erase #'e)
   #:when (typecheck? #'τ_e (subst #'τ.norm #'tv #'τ_body))
   (⊢ e- : τ.norm)])