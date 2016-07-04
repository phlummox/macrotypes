#lang turnstile
(extends "infer+sugar.rkt")
(require "infer-utils.rkt")
(provide Pat (for-syntax ~Pat))

(define-type-constructor Pattern #:arity = 3)
(define-type-constructor Context #:arity >= 0)
(define-type-constructor Context1 #:arity >= 1)
(define-type-constructor Context-Prop #:arity = 2)

(define-syntax Pat
  (syntax-parser #:datum-literals (:)
    [(Pat τ_match pat ctx)
     #`(Pattern τ_match
                #,(mk-type #'(quote-syntax pat))
                #,(translate-ctx #'ctx))]))
(begin-for-syntax
  (define (translate-ctx ctx)
    (syntax-parse ctx
      [(ctx1 ...)
       #`(Context #,@(stx-map translate-ctx1 #'[ctx1 ...]))]))
  (define (translate-ctx1 ctx1)
    (syntax-parse ctx1
      [[x:id (~seq tag τ) ...]
       #`(Context1 #,(mk-type #'(quote-syntax x))
                   #,@(stx-map translate-ctx-prop #'[[tag τ] ...]))]))
  (define (translate-ctx-prop ctx-prop)
    (syntax-parse ctx-prop
      [[tag:id τ]
       #`(Context-Prop #,(mk-type #'(quote-syntax tag)) τ)])))

(begin-for-syntax
  (define-syntax ~Pat
    (pattern-expander
     (syntax-parser
       [(Pat τ-pat pat-pat ctx-pat)
        #:with ctx-stx (generate-temporary)
        #'(~Pattern τ-pat
                    ((~literal quote-syntax) pat-pat)
                    (~and ctx-stx
                          (~parse ctx-pat (translate-ctx/type #'ctx-stx))))])))
  (define (translate-ctx/type ctx-stx)
    (syntax-parse ctx-stx
      [(~Context ctx1 ...)
       (stx-map translate-ctx1/type #'[ctx1 ...])]))
  (define (translate-ctx1/type ctx1-stx)
    (syntax-parse ctx1-stx
      [(~Context1 ((~literal quote-syntax) x) ctx-prop ...)
       #:with [[props ...] ...] (stx-map translate-ctx-prop/type #'[ctx-prop ...])
       #'[x props ... ...]]))
  (define (translate-ctx-prop/type ctx-prop-stx)
    (syntax-parse ctx-prop-stx
      [(~Context-Prop ((~literal quote-syntax) tag) τ)
       #'[tag τ]])))

(define-typed-syntax v:
  [(v x:id) ≫
   [#:with X (generate-temporary #'x)]
   --------
   [⊢ [[_ ≫ #f] ⇒ : (∀ (X) (Pat X x ([x : X])))]]])

(define-typed-syntax match #:datum-literals (with -> :)
  [(match e_match:expr with
     [pat:expr -> e_body:expr]
     ...+) ≫
   [#:with A (generate-temporary 'match-result)]
   [⊢ [[e_match ≫ e_match-] ⇒ : τ_match*]]
   [#:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_match) (~Cs [τ_1 τ_2] ...))
    (syntax-local-introduce #'τ_match*)]
   [⊢ [[pat ≫ _] ⇒ : τ_pat*] ...]
   [#:with [(~?Some [V3 ...]
                    (~?∀* (V4 ...) (~Pat τ_pat pat- ([x : τ_x] ...)))
                    (~Cs [τ_3 τ_4] ...))
            ...]
    (syntax-local-introduce #'[τ_pat* ...])]
   [([V3 : #%type ≫ V3-] ... [V4 : #%type ≫ V4-] ...) ([x : τ_x ≫ x-] ...)
    ⊢ [[e_body ≫ e_body-] ⇒ : τ_body*]]
   ...
   [#:with [(~?Some [V5 ...] (~?∀* (V6 ...) τ_body) (~Cs [τ_5 τ_6] ...)) ...]
    (syntax-local-introduce #'[τ_body* ...])]
   [#:with [[τ_pat- [τ_3- τ_4-] ...] ...]
    (substs #'[V3- ... ... V4- ... ...]
            #'[V3 ... ... V4 ... ...]
            #'[[τ_pat [τ_3 τ_4] ...] ...])]
   [#:with Xs #'[A V1 ... V2 ... V3- ... ... V4- ... ... V5 ... ... V6 ... ...]]
   [#:with τ_out (some/inst/generalize #'Xs
                                       #'A
                                       #'([τ_pat- τ_match] ...
                                          [τ_body A] ...
                                          [τ_1 τ_2] ...
                                          [τ_3- τ_4-] ... ...
                                          [τ_5 τ_6] ... ...))]
   --------
   [⊢ [[_ ≫ (match- e_match-
              [pat- (let- ([x- x] ...) e_body-)]
              ...)]
       ⇒ : τ_out]]])

