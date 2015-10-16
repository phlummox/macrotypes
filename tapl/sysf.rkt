#lang s-exp "typecheck.rkt"
(extends "stlc+lit.rkt")
(reuse #:from "stlc+rec-iso.rkt") ; want this type=?

;; System F
;; Type relation:
;; - extend type=? with ∀
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(define-type-constructor ∀ #:bvs >= 0
  #:sub? (λ (τ1 τ2)
           (syntax-parse (list τ1 τ2)
             [#;(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
                 ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
              (((~literal #%plain-app) tycon1 ((~literal #%plain-lambda) (x:id ...) k1 ... t1))
               ((~literal #%plain-app) tycon2 ((~literal #%plain-lambda) (y:id ...) k2 ... t2)))
              #:when (type=? #'tycon1 #'tycon2)
              #:when (types=? #'(k1 ...) #'(k2 ...))
              #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
              #:with (z ...) (generate-temporaries #'(x ...))
              (type=? (substs #'(z ...) #'(x ...) #'t1)
                      (substs #'(z ...) #'(y ...) #'t2))]
             [_ #f])))

(define-typed-syntax Λ
  [(_ (tv:id ...) e)
   #:with ((tv- ...) e- τ) (infer/tyctx+erase #'([tv : #%type] ...) #'e)
   (⊢ e- : (∀ (tv- ...) τ))])
(define-typed-syntax inst
  [(_ e τ:type ...)
   #:with (e- (tvs (τ_body))) (⇑ e as ∀)
   (⊢ e- : #,(substs #'(τ.norm ...) #'tvs #'τ_body))])