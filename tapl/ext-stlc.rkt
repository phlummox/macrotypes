#lang s-exp "typecheck.rkt"
(extends "stlc+lit.rkt" #:except #%datum)
(provide (for-syntax current-join))
 
;; Simply-Typed Lambda Calculus, plus extensions (TAPL ch11)
;; Types:
;; - types from stlc+lit.rkt
;; - Bool, String
;; - Unit
;; Terms:
;; - terms from stlc+lit.rkt
;; - literals: bool, string
;; - boolean prims, numeric prims
;; - if
;; - prim void : (→ Unit)
;; - begin
;; - ascription (ann)
;; - let, let*, letrec

(define-base-type Bool)
(define-base-type String)

(define-typed-syntax #%datum
  [(_ . b:boolean)
   --------------------
   ⊢ (#%datum . b) : Bool]
  [(_ . s:str) (⊢ (#%datum . s) : String)]
  [(_ . x) #'(stlc+lit:#%datum . x)])

(define-primop zero? : (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop - : (→ Int Int Int))
(define-primop add1 : (→ Int Int))
(define-primop sub1 : (→ Int Int))
(define-primop not : (→ Bool Bool))

(define-typed-syntax and
  [(_ e1 e2)
   ⊢ e1 ≫ e1- : Bool
   ⊢ e2 ≫ e2- : Bool
   --------------------
   ⊢ (and e1- e2-) : Bool])
  
(define-typed-syntax or
  [(_ e1 e2)
   ⊢ e1 ≫ e1- : Bool
   ⊢ e2 ≫ e2- : Bool
   --------------------
   ⊢ (or e1- e2-) : Bool])

(begin-for-syntax 
  (define current-join (make-parameter (λ (x y) x))))
(define-typed-syntax if
  [(_ e_tst e1 e2)
   ⊢ e_tst ≫ e_tst- : Bool
   ⊢ e1 ≫ e1- : τ1
   ⊢ e2 ≫ e2- : τ2
   #:with τ-out ((current-join) #'τ1 #'τ2)
   τ1 ⊑ τ-out
   #:with-msg "first if branch has bad type"
   τ2 ⊑ τ-out
   #:with-msg "second if branch has bad type"
   --------------------
   ⊢ (if e_tst- e1- e2-) : τ-out])

(define-base-type Unit)
(define-primop void : (→ Unit))

(define-typed-syntax begin
  [(_ e_unit ... e)
   ⊢ e_unit ≫ e_unit- : Unit ...
   ⊢ e ≫ e- : τ
   --------------------
   ⊢ (begin e_unit- ... e-) : τ])

(define-typed-syntax ann 
  [(_ e (~datum :) ascribed-τ:type)
   ⊢ e ≫ e- : τ
   τ ⊑ ascribed-τ.norm
   #:with-msg
   (format "~a does not have type ~a\n"
           (syntax->datum #'e) (syntax->datum #'ascribed-τ))
   --------------------
   ⊢ e- : ascribed-τ])

(define-typed-syntax let/tc #:export-as let
  [(_ (~and bvs ([x e] ...)) e_body)
   ⊢ e ≫ e- : τ ...
   ([x τ] ...) ⊢ e_body ≫ e_body- : τ_body
   #:with (x- ...) #'xs-
   --------------------
   ⊢ (let ([x- e-] ...) e_body-) : τ_body])

(define-typed-syntax let*/tc #:export-as let*
  [(_ () e_body) #'e_body]
  [(_ ([x e] [x_rst e_rst] ...) e_body)
   #'(let/tc ([x e]) (let*/tc ([x_rst e_rst] ...) e_body))])

(define-typed-syntax letrec
  [(_ ([b:type-bind e] ...) e_body)
   #:with (all-e ...) #'(e ... e_body) ; consolidate so they get the same ctx
   (b ...) ⊢ all-e ≫ all-e- : all-τ ...
   #:with (e- ... e_body-) #'(all-e- ...)
   #:with (τ ... τ_body) #'(all-τ ...)
   #:with (x- ...) #'xs-
   b.type ⊑ τ ...
   #:with-msg
   (string-append
    "type check fail, args have wrong type:\n"
    (string-join
     (stx-map
      (λ (e τ τ-expect)
        (format
         "~a has type ~a, expected ~a"
         (syntax->datum e) (type->str τ) (type->str τ-expect)))
      #'(e ...) #'(τ ...) #'(b.type ...))
     "\n"))
   --------------------
   ⊢ (letrec ([x- e-] ...) e_body-) : τ_body])
     