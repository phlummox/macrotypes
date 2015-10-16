#lang s-exp "typecheck.rkt"
(extends "sysf.rkt" #:except #%datum ∀ Λ inst #:rename [~∀ ~sysf:∀])
(reuse String #%datum #:from "stlc+reco+var.rkt")
(provide ★)

; same as fomega.rkt except here λ and #%app works as both type and terms
; - uses definition from stlc, but tweaks type? and kind? predicates
;; → is also both type and kind

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; - String from stlc+reco+var
;; Terms:
;; - extend ∀ Λ inst from sysf
;; - #%datum from stlc+reco+var

(define-syntax-category kind)

(begin-for-syntax
  (current-kind? (λ (k) (or (#%type? k) (kind? k) (#%type? (typeof k)))))
  ;; Try to keep "type?" backward compatible with its uses so far,
  ;; eg in the definition of λ or previous type constuctors.
  ;; (However, this is not completely possible, eg define-type-alias)
  ;; So now "type?" no longer validates types, rather it's a subset.
  ;; But we no longer need type? to validate types, instead we can use (kind? (typeof t))
  (current-type? (λ (t) (or (type? t)
                            (let ([k (typeof t)])
                              (or (★? k) (∀★? k)))
                            ((current-kind?) t)))))

; must override
(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #:with (τ- k_τ) (infer+erase #'τ)
     #'(define-syntax alias (syntax-parser [x:id #'τ-][(_ . rst) #'(τ- . rst)]))]))

(define-syntax ★ (make-rename-transformer #'#%type))
(define-for-syntax ★? #%type?)
(define-kind-constructor ∀★ #:arity >= 0)

(define-typed-syntax ∀ #:export-as ∀
  [(_ bvs:kind-ctx τ_body)
   ;; cant re-use the expansion in sysf:∀ because it will give the bvs kind #%type
   #:with (tvs- τ_body- k_body) (infer/ctx+erase #'bvs #'τ_body)
   ; expand so kind gets overwritten
   (⊢ #,((current-type-eval) #'(sysf:∀ tvs- τ_body-)) : (∀★ bvs.kind ...))])

;; alternative: normalize before type=?
; but then also need to normalize in current-promote
(begin-for-syntax
  (define (normalize τ)
    (syntax-parse τ
      [x:id #'x]
      [((~literal #%plain-app) ((~literal #%plain-lambda) (tv ...) τ_body) τ_arg ...)
       (normalize (substs #'(τ_arg ...) #'(tv ...) #'τ_body))]
      [((~literal #%plain-lambda) (x ...) . bodys)
       #:with bodys_norm (stx-map normalize #'bodys)
       (syntax-track-origin #'(#%plain-lambda (x ...) . bodys_norm) τ #'plain-lambda)]
      [((~literal #%plain-app) x:id . args)
       #:with args_norm (stx-map normalize #'args)
       (syntax-track-origin #'(#%plain-app x . args_norm) τ #'#%plain-app)]
      [((~literal #%plain-app) . args)
       #:with args_norm (stx-map normalize #'args)
       (syntax-track-origin (normalize #'(#%plain-app . args_norm)) τ #'#%plain-app)]
      [_ τ]))
  
  (define old-eval (current-type-eval))
  (define (type-eval τ) (normalize (old-eval τ)))
  (current-type-eval type-eval)
  )

(begin-for-syntax
  (define-syntax ~∀
    (pattern-expander
     (syntax-parser #:datum-literals (:)
       [(_ . args)
        #:with ∀τ (generate-temporary)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv (... ...)) τ) #'∀τ)
                (~parse (~∀★ k (... ...)) (typeof #'∀τ))
                (~parse args #'(([tv k] (... ...)) (τ))))])))
  (define-syntax ~∀*
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ . args)
        #'(~or
           (~∀ . args)
           (~and any (~do
                      (type-error
                       #:src #'any
                       #:msg "Expected ∀ type, got: ~a" #'any))))])))
  )

(define-typed-syntax Λ
  [(_ bvs:kind-ctx e)
   #:with ((tv- ...) e- τ_e)
          (infer/ctx+erase #'bvs #'e)
   (⊢ e- : (∀ ([tv- : bvs.kind] ...) τ_e))])

(define-typed-syntax inst
  [(_ e τ ...)
   #:with (e- (([tv k] ...) (τ_body))) (⇑ e as ∀)
   #:with ([τ- k_τ] ...) (infers+erase #'(τ ...))
   #:when (stx-andmap (λ (t k) (or ((current-kind?) k)
                                   (type-error #:src t #:msg "not a valid type: ~a" t)))
                      #'(τ ...) #'(k_τ ...))
   #:when (typechecks? #'(k_τ ...) #'(k ...))
   (⊢ e- : #,(substs #'(τ- ...) #'(tv ...) #'τ_body))])