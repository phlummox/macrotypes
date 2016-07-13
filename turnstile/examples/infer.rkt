#lang turnstile
(extends "ext-stlc.rkt" #:except #%app λ ann if let let* letrec begin)
(reuse Λ ∀ inst #:from "sysf.rkt")
(require (only-in "sysf.rkt" ∀ ~∀ ∀? Λ))
(reuse List #:from "stlc+cons.rkt")
(require (only-in "stlc+cons.rkt" List ~List) (only-in racket/list empty empty? first rest))
(reuse tup × proj #:from "stlc+tup.rkt")
(reuse define-type-alias #:from "stlc+reco+var.rkt")
(require "infer-utils.rkt"
         (for-syntax macrotypes/type-constraints))

(define-typed-syntax λ
  [(λ (x:id ...) body:expr) ≫
   [#:with [X ...]
    (for/list ([X (in-list (generate-temporaries #'[x ...]))])
      (add-orig X X))]
   [([X : #%type ≫ X-] ...) ([x : X ≫ x-] ...)
    ⊢ [[body ≫ body-] ⇒ : τ_body*]]
   [#:with (~?Some [V ...] τ_body (~Cs [id_2 τ_2] ...)) (syntax-local-introduce #'τ_body*)]
   [#:with τ_fn (some/inst/generalize #'[X- ... V ...]
                                      #'(→ X- ... τ_body)
                                      (list #'([id_2 τ_2] ...)))]
   --------
   [⊢ [[_ ≫ (λ- (x- ...) body-)] ⇒ : τ_fn]]])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫
   [#:with [A ...] (generate-temporaries #'[e_arg ...])]
   [#:with B (generate-temporary 'result)]
   [⊢ [[e_fn ≫ e_fn-] ⇒ : τ_fn*]]
   [#:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_fn) (~Cs [τ_3 τ_4] ...))
    (syntax-local-introduce #'τ_fn*)]
   [#:with τ_fn-expected (tycons #'→ #'[A ... B])]
   [⊢ [[e_arg ≫ e_arg-] ⇒ : τ_arg*] ...]
   [#:with [(~?Some [V3 ...] (~?∀* (V4 ...) τ_arg) (~Cs [τ_5 τ_6] ...)) ...]
    (syntax-local-introduce #'[τ_arg* ...])]
   [#:with Xs #'[A ... B V1 ... V2 ... V3 ... ... V4 ... ...]]
   [#:with τ_out (some/inst/generalize #'Xs
                                       #'B
                                       (list
                                        #'([τ_3 τ_4] ...
                                           [τ_5 τ_6] ... ...)
                                        #'([τ_fn τ_fn-expected])
                                        #'([τ_arg A] ...)))]
   --------
   [⊢ [[_ ≫ (#%app- e_fn- e_arg- ...)] ⇒ : τ_out]]])

(define-typed-syntax if
  [(if e_c:expr e_t:expr e_e:expr) ≫
   [#:with R (generate-temporary 'if-res)]
   [⊢ [[e_c ≫ e_c-] ⇒ : τ_c*]]
   [#:with (~?Some [V1 ...] (~?∀* (V2 ...) _) (~Cs [τ_1 τ_2] ...))
    (syntax-local-introduce #'τ_c*)]
   [⊢ [[e_t ≫ e_t-] ⇒ : τ_t*]]
   [#:with (~?Some [V3 ...] (~?∀* (V4 ...) τ_t) (~Cs [τ_3 τ_4] ...))
    (syntax-local-introduce #'τ_t*)]
   [⊢ [[e_e ≫ e_e-] ⇒ : τ_e*]]
   [#:with (~?Some [V5 ...] (~?∀* (V6 ...) τ_e) (~Cs [τ_5 τ_6] ...))
    (syntax-local-introduce #'τ_e*)]
   [#:with Xs #'[R V1 ... V2 ... V3 ... V4 ... V5 ... V6 ...]]
   [#:with τ_out (some/inst/generalize #'Xs
                                       #'R
                                       (list
                                        #'([τ_1 τ_2] ...
                                           [τ_3 τ_4] ...
                                           [τ_5 τ_6] ...)
                                        #'([τ_t R]
                                           [τ_e R])))]
   --------
   [⊢ [[_ ≫ (if- e_c- e_t- e_e-)] ⇒ : τ_out]]])

(define-typed-syntax or
  [(or e ...) ≫
   [⊢ [[e ≫ e-] ⇒ : τ_e*] ...]
   [#:with [(~?Some [V1 ...] (~?∀* (V2 ...) τ_e) (~Cs [τ_1 τ_2] ...)) ...]
    (syntax-local-introduce #'[τ_e* ...])]
   [#:with Bool* ((current-type-eval) #'Bool)]
   [#:with τ_out (some/inst/generalize #'[V1 ... ... V2 ... ...]
                                       #'Bool
                                       (list
                                        #'([τ_1 τ_2] ... ...)
                                        #'([τ_e Bool*] ...)))]
   --------
   [⊢ [[_ ≫ (or- e- ...)] ⇒ : τ_out]]])

(define-typed-syntax and
  [(and e ...) ≫
   [⊢ [[e ≫ e-] ⇒ : τ_e*] ...]
   [#:with [(~?Some [V1 ...] (~?∀* (V2 ...) τ_e) (~Cs [τ_1 τ_2] ...)) ...]
    (syntax-local-introduce #'[τ_e* ...])]
   [#:with Bool* ((current-type-eval) #'Bool)]
   [#:with τ_out (some/inst/generalize #'[V1 ... ... V2 ... ...]
                                       #'Bool
                                       (list
                                        #'([τ_1 τ_2] ... ...)
                                        #'([τ_e Bool*] ...)))]
   --------
   [⊢ [[_ ≫ (and- e- ...)] ⇒ : τ_out]]])

(define-typed-syntax let
  [(let ([x e_x] ...) e_body) ≫
   [⊢ [[e_x ≫ e_x-] ⇒ : τ_x*] ...]
   [#:with [(~?Some [V1 ...] (~?∀* (V2 ...) τ_x) (~Cs [τ_1 τ_2] ...)) ...]
    (syntax-local-introduce #'[τ_x* ...])]
   [() ([x : τ_x ≫ x-] ...) ⊢ [[e_body ≫ e_body-] ⇒ : τ_body*]]
   [#:with (~?Some [V3 ...] (~?∀* (V4 ...) τ_body) (~Cs [τ_3 τ_4] ...))
    (syntax-local-introduce #'τ_body*)]
   [#:with τ_out (some/inst/generalize #'[V1 ... ... V2 ... ...]
                                       #'τ_body
                                       (list
                                        #'([τ_1 τ_2] ... ... [τ_3 τ_4] ...)))]
   --------
   [⊢ [[_ ≫ (let- ([x- e_x-] ...) e_body-)] ⇒ : τ_out]]])

(define-typed-syntax letrec
  [(letrec ([x e_x] ...) e_body) ≫
   [#:with [X ...] (generate-temporaries (stx-map id-upcase #'[x ...]))]
   [#:with R (generate-temporary 'R)]
   [([X : #%type ≫ X-] ...) ([x : X ≫ x-] ...)
    ⊢ [[e_x ≫ e_x-] ⇒ : τ_x*] ... [[e_body ≫ e_body-] ⇒ : τ_body*]]
   [#:with [(~?Some [V1 ...] (~?∀* (V2 ...) τ_x) (~Cs [τ_1 τ_2] ...)) ...
            (~?Some [V3 ...] (~?∀* (V4 ...) τ_body) (~Cs [τ_3 τ_4] ...))]
    (syntax-local-introduce #'[τ_x* ... τ_body*])]
   [#:with τ_out (some/inst/generalize #'[X- ... R V1 ... ... V2 ... ... V3 ... V4 ...]
                                       #'R
                                       (list
                                        #'([τ_1 τ_2] ... ... [τ_3 τ_4] ...)
                                        #'([τ_x X-] ...)
                                        #'([τ_body R])))]
   --------
   [⊢ [[_ ≫ (letrec- ([x- e_x-] ...) e_body-)] ⇒ : τ_out]]])


(define-typed-syntax ann #:datum-literals (:)
  [(ann e:expr : τ:type) ≫
   [#:with (~?∀ (X ...) τ_ann) #'τ.norm]
   [⊢ [[e ≫ e-] ⇒ : τ_e**]]
   [#:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_e*) (~Cs [τ_1 τ_2] ...))
    (syntax-local-introduce #'τ_e**)]
   [#:with τ_e (some/inst/generalize #'[X ... V1 ... V2 ...]
                                     #'τ_ann
                                     (list
                                      #'([τ_1 τ_2] ...)
                                      #'([τ_e* τ_ann])))]
   --------
   [⊢ [[_ ≫ e-] ⇒ : τ_e]]])

(define-typed-syntax ann/exact #:datum-literals (:)
  [(ann e:expr : τ:type) ≫
   [#:with (~?∀ (X ...) τ_ann) #'τ.norm]
   [⊢ [[e ≫ e-] ⇒ : τ_e**]]
   [#:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_e*) (~Cs [τ_1 τ_2] ...))
    (syntax-local-introduce #'τ_e**)]
   [#:with τ_e ((current-type-eval)
                (some/inst/generalize #'[X ... V1 ... V2 ...]
                                      #'τ_ann
                                      (list
                                       #'([τ_1 τ_2] ...)
                                       #'([τ_e* τ_ann]))))]
   [τ_e τ⊑ τ.norm #:for e]
   --------
   [⊢ [[_ ≫ e-] ⇒ : τ.norm]]])

(define-typed-syntax define
  [(define x:id e:expr) ≫
   [⊢ [[e ≫ e-] ⇒ : τ_e]]
   [#:with tmp (generate-temporary #'x)]
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ tmp : τ_e)))
          (define- tmp e-))]]
  [(define (f x:id ...) body:expr) ≫
   --------
   [_ ≻ (define f (λ (x ...) body))]])

(define-typed-syntax define/rec #:datum-literals (: ->)
  [(define/rec x:id : τ_x:type e:expr) ≫
   [#:with tmp (generate-temporary #'x)]
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ tmp : τ_x.norm)))
          (define- tmp (ann/exact e : τ_x.norm)))]]
  [(define/rec (f x:id ...) : τ_f body:expr) ≫
   --------
   [_ ≻ (define/rec f : τ_f (λ (x ...) body))]]
  [(define/rec (f [x:id : τ_x] ...) -> τ_res body:expr) ≫
   --------
   [_ ≻ (define/rec f : (→ τ_x ... τ_res)
          (ext-stlc:λ ([x : τ_x] ...) (ann/exact body : τ_res)))]]
  [(define/rec #:∀ (X:id ...+) (f [x:id : τ_x] ...) -> τ_res body:expr) ≫
   --------
   [_ ≻ (define/rec f : (∀ (X ...) (→ τ_x ... τ_res))
          (sysf:Λ (X ...) (ext-stlc:λ ([x : τ_x] ...) (ann/exact body : τ_res))))]])

(define-primop empty? : (∀ (X) (→ (List X) Bool)))
(define-primop empty : (∀ (X) (List X)))
(define-primop cons : (∀ (X) (→ X (List X) (List X))))
(define-primop first : (∀ (X) (→ (List X) X)))
(define-primop rest : (∀ (X) (→ (List X) (List X))))

(define-primop abs : (→ Int Int))



