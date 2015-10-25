#lang s-exp "typecheck.rkt"
(extends "stlc+lit.rkt" #:except #%datum +)
(extends "ext-stlc.rkt" #:except #%datum + and)
(provide (for-syntax subs? current-sub?))

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
(define-base-type Num)
(define-base-type Nat)

(define-base-type Bot)

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))

(define-typed-syntax #%datum
  [(_ . n:nat) (⊢ (#%datum . n) : Nat)]
  [(_ . n:integer) (⊢ (#%datum . n) : Int)]
  [(_ . n:number) (⊢ (#%datum . n) : Num)]
  [(_ . x) #'(ext-stlc:#%datum . x)])

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
;    (printf "t1 = ~a\n" (syntax->datum τ1))
;    (printf "t2 = ~a\n" (syntax->datum τ2))
    (or ((current-type=?) τ1 τ2)
        (Top? τ2)))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  (define-syntax (define-sub-relation stx)
    (syntax-parse stx #:datum-literals (<: =>)
      [(_ τ1:id <: τ2:id)
       #:with τ1-expander (format-id #'τ1 "~~~a" #'τ1)
       #:with τ2-expander (format-id #'τ2 "~~~a" #'τ2)
       #:with fn (generate-temporary)
       #:with old-sub? (generate-temporary)
       #'(begin
           (define old-sub? (current-sub?))
           (define (fn t1 t2)
             (define τ1 ((current-type-eval) t1))
             (define τ2 ((current-type-eval) t2))
             (syntax-parse (list τ1 τ2)
               [(τ1-expander τ) ((current-sub?) #'τ2 #'τ)]
               [(τ τ2-expander) ((current-sub?) #'τ #'τ1)]
               [_ #f]))
           (current-sub? (λ (t1 t2) (or (old-sub? t1 t2) (fn t1 t2))))
           (current-typecheck-relation (current-sub?)))]
      [(_ (~seq τ1:id <: τ2:id (~and (~literal ...) ddd))
          (~seq τ3:id <: τ4:id)
           =>
          (tycon1 . rst1) <: (tycon2 . rst2))
       #:with tycon1-expander (format-id #'tycon1 "~~~a" #'tycon1)
       #:with tycon2-expander (format-id #'tycon2 "~~~a" #'tycon2)
       #:with fn (generate-temporary)
       #:with old-sub? (generate-temporary)
       #'(begin
           (define old-sub? (current-sub?))
           (define (fn t1 t2)
             (define τ1 ((current-type-eval) t1))
             (define τ2 ((current-type-eval) t2))
             (syntax-parse (list τ1 τ2)
               [((tycon1-expander . rst1) (tycon2-expander . rst2))
                (and (subs? #'(τ1 ddd) #'(τ2 ddd))
                     ((current-sub?) #'τ3 #'τ4))]
               [_ #f]))
           (current-sub? (λ (t1 t2) (or (old-sub? t1 t2) (fn t1 t2))))
           (current-typecheck-relation (current-sub?)))]))

  (define-sub-relation Nat <: Int)
  (define-sub-relation Int <: Num)
  (define-sub-relation t1 <: s1 ... s2 <: t2 => (→ s1 ... s2) <: (→ t1 ... t2)))
           
