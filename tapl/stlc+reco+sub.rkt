#lang s-exp "typecheck.rkt"
(extends "stlc+sub.rkt" #:except #%app #%datum)
(extends "stlc+reco+var.rkt" #:except #%datum + Int ~Int Int? ∨ × tup)
;;use type=? and eval-type from stlc+reco+var.rkt, not stlc+sub.rkt
;; but extend sub? from stlc+sub.rkt

;; Simply-Typed Lambda Calculus, plus subtyping, plus records
;; Types:
;; - types from stlc+sub.rkt
;; Type relations:
;; - sub? extended to records
;; Terms:
;; - terms from stlc+sub.rkt
;; - records and variants from stlc+reco+var

(define-typed-syntax #%datum
  [(_ . n:number) #'(stlc+sub:#%datum . n)]
  [(_ . x) #'(stlc+reco+var:#%datum . x)])

(define-typed-syntax ∨
  [(_ . rst)
     (add-sub ((current-type-eval) #'(stlc+reco+var:∨ . rst)) ∨-sub?)])

(define-typed-syntax × #:export-as ×
  [(_ . rst)
     (add-sub ((current-type-eval) #'(stlc+reco+var:× . rst)) ×-sub?)])

;; have to redefine it to use the new wrapped version of × with the new subtyping rules
(define-typed-syntax tup #:datum-literals (=)
  [(_ [l:id = e] ...)
   #:with ([e- τ] ...) (infers+erase #'(e ...))
   (⊢ (list (list 'l e-) ...) : (× [l : τ] ...))])

(begin-for-syntax
  (define (×-sub? τ1 τ2)
    (or
     (Top? τ2)
     (syntax-parse (list τ1 τ2)
       [((~× [k : τk] ...) (~× [l : τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(label τlabel)
            #:with (k_match τk_match) (stx-assoc #'label #'([k τk] ...))
            (typecheck? #'τk_match #'τlabel)])
         #'([l τl] ...))]
       [_ #f])))
  (define (∨-sub? τ1 τ2)
    (or
     (Top? τ2)
     (syntax-parse (list τ1 τ2)
       [((~∨ [k : τk] ...) (~∨ [l : τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(label τlabel)
            #:with (k_match τk_match) (stx-assoc #'label #'([k τk] ...))
            (typecheck? #'τk_match #'τlabel)])
         #'([l τl] ...))]
       [_ #f])))

  (define (join t1 t2)
    (cond
      [(typecheck? t1 t2) t2]
      [(typecheck? t2 t1) t1]
      [else (expand/df #'Top)]))
  (current-join join))