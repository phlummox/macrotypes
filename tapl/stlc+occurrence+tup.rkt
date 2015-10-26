#lang s-exp "typecheck.rkt"
(reuse tup × proj ~× #:from "stlc+tup.rkt")
(extends "stlc+occurrence.rkt" #:rename [test old-test])

(define-for-syntax (replace-at τ* n τ-new)
  (for/list ([τ-old (in-list τ*)]
             [i (in-naturals)])
    (if (= i n)
        τ-new
        τ-old)))

;; Add subtyping for tuples
(begin-for-syntax
 (define ×-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1-stx τ2-stx)
       (define τ1 ((current-type-eval) τ1-stx))
       (define τ2 ((current-type-eval) τ2-stx))
       (or (Bot? τ1) (Top? τ2)
           (syntax-parse `(,τ1 ,τ2)
            [((~× τi1* ...)
              (~× τi2* ...))
             (and (stx-length=? #'(τi1* ...)
                                #'(τi2* ...))
                  ;; Gotta use (current-sub?), because products may be recursive
                  (stx-andmap (current-sub?) #'(τi1* ...) #'(τi2* ...)))]
            [_
             (sub? τ1 τ2)])))))
 (current-sub? ×-sub?)
 (current-typecheck-relation (current-sub?)))

;; --- Update Π for products
(begin-for-syntax
 (define π-Π
   (let ([Π (current-Π)]
         [τ-eval (current-type-eval)])
     (lambda (τ)
       (syntax-parse (τ-eval τ)
        [(~× τ* ...)
         (define filter* (type*->filter* (syntax->list #'(τ* ...))))
         #`(lambda (v*)
             (and (list? v*)
                  (for/and ([v (in-list v*)]
                            [f (in-list (list #,@filter*))])
                    (f v))))]
        [_ ;; Fall back
         (Π τ)]))))
 (current-Π π-Π))

(define-typed-syntax test #:datum-literals (?)
  ;; -- THIS CASE BELONGS IN A NEW FILE
  [(_ [τ0+:type ? (unop x-stx:id n-stx:nat)] e1 e2)
   ;; 1. Check that we're using a known eliminator
   #:when (free-identifier=? #'proj #'unop)
   ;; 2. Make sure we're filtering with a valid type
   #:with f (type->filter #'τ0+)
   ;; 3. Typecheck the eliminator call. Remember the type & apply the filter.
   ;;    (This type is PROBABLY a union -- else why bother testing!)
   #:with (e0+ τ0) (infer+erase #'(unop x-stx n-stx))
   #:with τ0- (∖ #'τ0 #'τ0+)
   ;; 4. Build the +/- types for our identifier; the thing we apply the elim. + test to
   ;;    We know that x has a pair type because (proj x n) typechecked
   #:with (x (~× τi* ...)) (infer+erase #'x-stx)
   #:with τ+ #`(× #,@(replace-at (syntax->list #'(τi* ...)) (syntax-e #'n-stx) #'τ0+))
   #:with τ- #`(× #,@(replace-at (syntax->list #'(τi* ...)) (syntax-e #'n-stx) #'τ0-))
   ;; 5. Check the branches with the refined types
   #:with [x1 e1+ τ1] (infer/ctx+erase #'([x-stx : τ+]) #'e1)
   #:with [x2 e2+ τ2] (infer/ctx+erase #'([x-stx : τ-]) #'e2)
   ;; 6. Desugar, replacing the filtered identifier
   (⊢  (if (f e0+)
           ((lambda x1 e1+) x-stx)
           ((lambda x2 e2+) x-stx))
      : (∪ τ1 τ2))]
  [(_ e* ...)
   #'(old-test e* ...)])
