#lang turnstile
(extends "ext-stlc.rkt" 
 #:except #%app #%datum + add1 sub1 * Int Int? ~Int Float Float? ~Float)
(reuse define-type-alias #:from "stlc+reco+var.rkt")
(provide Int Num Nat U)
(provide case→)

;; Simply-Typed Lambda Calculus, plus union types
;; Types:
;; - types from and ext+stlc.rkt
;; - Top, Num, Nat
;; - U
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

(define-base-types Zero NegInt PosInt Float)
(define-type-constructor U* #:arity > 0)
(define-type-constructor case-> #:arity > 0)
(define-syntax case→ (make-rename-transformer #'case->))

(define-for-syntax (prune+sort tys)
  (define ts (stx->list tys))
  (stx-sort (remove-duplicates (stx->list tys) typecheck?)))
  
  (define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) ty2-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ...))
     (if (= 1 (stx-length #'tys-))
         (stx-car #'tys)
         #'(U* . tys-))]))
(define-syntax Nat
  (make-variable-like-transformer 
   (add-orig #'(U Zero PosInt) #'Nat)))
(define-syntax Int
  (make-variable-like-transformer 
   (add-orig #'(U NegInt Nat) #'Int)))
(define-syntax Num 
  (make-variable-like-transformer (add-orig #'(U Float Int) #'Num)))

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))
(define-primop add1 : (case→ (→ Nat Nat)
                             (→ Int Int)))
(define-primop sub1 : (case→ (→ Zero NegInt)
                             (→ PosInt Nat)
                             (→ NegInt NegInt)
                             (→ Nat Nat)
                             (→ Int Int)))

(define-typed-syntax datum #:export-as #%datum
  [(_ . n:integer) ≫
   [#:with ty_out (let ([m (syntax-e #'n)])
                    (cond [(zero? m) #'Zero]
                          [(> m 0) #'PosInt]
                          [else #'NegInt]))]
   --------
   [⊢ [_ ≫ (#%datum- . n) ⇒ : ty_out]]]
  [(#%datum . n:number) ≫
   [#:when (real? (syntax-e #'n))]
   --------
   [⊢ [_ ≫ (#%datum- . n) ⇒ : Float]]]
  [(_ . x) ≫
   --------
   [_ ≻ (ext-stlc:#%datum . x)]])

(define-typed-syntax app #:export-as #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~→ ~! τ_in ... τ_out)]]
   [#:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
    (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])]
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~case-> . (~and ty_fns ((~→ . _) ...)))]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   [#:with τ_out
    (for/first ([ty_f (stx->list #'ty_fns)]
                #:when (syntax-parse ty_f
                         [(~→ τ_in ... τ_out)
                          (and (stx-length=? #'(τ_in ...) #'(e_arg ...))
                               (typechecks? #'(τ_arg ...) #'(τ_in ...)))]))
      (syntax-parse ty_f [(~→ _ ... t_out) #'t_out]))]
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]])

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ; 2 U types, subtype = subset
       [((~U* . tys1) (~U* . tys2))
        (for/and ([t (stx->list #'tys1)])
          ((current-sub?) t t2))]
       ; 1 U type, 1 non-U type. subtype = member
       [(ty (~U* . tys))
        (for/or ([t (stx->list #'tys)])
          ((current-sub?) #'ty t))]
       ; 2 case-> types, subtype = subset
       [((~case-> . tys1) (~case-> . tys2))
        (for/and ([t (stx->list #'tys2)])
          ((current-sub?) t1 t))]
       ; 1 case-> , 1 non-case->
       [((~case-> . tys) ty)
        (for/or ([t (stx->list #'tys)])
          ((current-sub?) t #'ty))]
       [((~→ s1 ... s2) (~→ t1 ... t2))
        (and (subs? #'(t1 ...) #'(s1 ...))
             ((current-sub?) #'s2 #'t2))]
       [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  (define (join t1 t2) #`(U #,t1 #,t2))
  (current-join join))
                   
