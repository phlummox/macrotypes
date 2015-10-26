#lang s-exp "typecheck.rkt"
(extends "stlc+cons.rkt" #:except + #%datum and tup × proj ~×)
(extends "stlc+occurrence+tup.rkt")

;; =============================================================================
;; === Lists

;; Subtyping for lists
(begin-for-syntax
 (define list-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1-stx τ2-stx)
       (define τ1 ((current-type-eval) τ1-stx))
       (define τ2 ((current-type-eval) τ2-stx))
       (or (Bot? τ1) (Top? τ2)
           (syntax-parse `(,τ1 ,τ2)
            [((~List τi1)
              (~List τi2))
             ((current-sub?) #'τi1 #'τi2)]
            [_
             (sub? τ1 τ2)])))))
 (current-sub? list-sub?)
 (current-typecheck-relation (current-sub?)))

;; --- Update Π for lists
(begin-for-syntax
 (define list-Π
   (let ([Π (current-Π)])
     (lambda (τ)
       (syntax-parse ((current-type-eval) τ)
        [(~List τi)
         (define f ((current-Π) #'τi))
         #`(lambda (v*)
             (and (list? v*)
                  (for/and ([v (in-list v*)])
                    (#,f v))))]
        [_ ;; Fall back
         (Π τ)]))))
 (current-Π list-Π))
