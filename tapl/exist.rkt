#lang s-exp "typecheck.rkt"
(extends "stlc+reco+var.rkt")
(reuse #:from "stlc+rec-iso.rkt") ; want type=?, but only need to load current-type=?

;; existential types
;; Types:
;; - types from stlc+reco+var.rkt
;; - ∃
;; Terms:
;; - terms from stlc+reco+var.rkt
;; - pack and open
;; Other: type=? from stlc+rec-iso.rkt


(define-type-constructor ∃ #:bvs = 1
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

(define-typed-syntax pack
  [(_ (τ:type e) as ∃τ:type)
   #:with (~∃* (τ_abstract) τ_body) #'∃τ.norm
   #:with [e- τ_e] (infer+erase #'e)
   #:when (typecheck? #'τ_e  (subst #'τ.norm #'τ_abstract #'τ_body))
   (⊢ e- : ∃τ.norm)])

(define-typed-syntax open #:datum-literals (<=)
  [(_ ([(tv:id x:id) <= e_packed]) e)
   #:with [e_packed- ((τ_abstract) (τ_body))] (⇑ e_packed as ∃)
     ;; The subst below appears to be a hack, but it's not really.
     ;; It's the (TaPL) type rule itself that is fast and loose.
     ;; Leveraging the macro system's management of binding reveals this.
     ;; 
     ;; Specifically, here is the TaPL Unpack type rule, fig24-1, p366:
     ;; Γ ⊢ t_1 : {∃X,T_12}
     ;; Γ,X,x:T_12 ⊢ t_2 : T_2
     ;; ------------------------------
     ;; Γ ⊢ let {X,x}=t_1 in t_2 : T_2
     ;;
     ;; There's *two* separate binders, the ∃ and the let,
     ;; which the rule conflates.
     ;;
     ;; Here's the rule rewritten to distinguish the two binding positions:
     ;; Γ ⊢ t_1 : {∃X_1,T_12}
     ;; Γ,X_???,x:T_12 ⊢ t_2 : T_2
     ;; ------------------------------
     ;; Γ ⊢ let {X_2,x}=t_1 in t_2 : T_2
     ;;
     ;; The X_1 binds references to X in T_12.
     ;; The X_2 binds references to X in t_2.
     ;; What should the X_??? be?
     ;;
     ;; A first guess might be to replace X_??? with both X_1 and X_2,
     ;; so all the potentially referenced type vars are bound.
     ;; Γ ⊢ t_1 : {∃X_1,T_12}
     ;; Γ,X_1,X_2,x:T_12 ⊢ t_2 : T_2
     ;; ------------------------------
     ;; Γ ⊢ let {X_2,x}=t_1 in t_2 : T_2
     ;;
     ;; But this example demonstrates that the rule above doesnt work:
     ;; (open ([x : X_2 (pack (Int 0) as (∃ (X_1) X_1))])
     ;;   ((λ ([y : X_2]) y) x)
     ;; Here, x has type X_1, y has type X_2, but they should be the same thing,
     ;; so we need to replace all X_1's with X_2
     ;;
     ;; Here's the fixed rule, which is implemented here
     ;;
     ;; Γ ⊢ t_1 : {∃X_1,T_12}
     ;; Γ,X_2,x:[X_2/X_1]T_12 ⊢ t_2 : T_2
     ;; ------------------------------
     ;; Γ ⊢ let {X_2,x}=t_1 in t_2 : T_2
     ;;
   #:with [_ (x-) (e-) (τ_e)]
          (infer #'(e)
                 #:tvctx #'([tv : #%type])
                 #:ctx   #`([x : #,(subst #'tv #'τ_abstract #'τ_body)]))
   (⊢ (let ([x- e_packed-]) e-) : τ_e)])