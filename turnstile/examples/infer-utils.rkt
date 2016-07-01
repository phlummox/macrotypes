#lang racket/base

(provide Some
         Cs
         (for-syntax ?∀
                     ?Some
                     Cs
                     ~?∀
                     ~?∀*
                     ~?Some
                     ~Cs
                     some/inst/generalize
                     tycons
                     ))

(require macrotypes/typecheck
         (only-in "stlc.rkt" define-type-constructor)
         (only-in "sysf.rkt" ∀ ~∀ ∀?)
         (for-syntax racket/base
                     syntax/parse
                     macrotypes/type-constraints))

;; (Some [X ...] τ_body (Constraints (Constraint τ_1 τ_2) ...))
(define-type-constructor Some #:arity = 2 #:bvs >= 0)
(define-type-constructor Constraint #:arity = 2)
(define-type-constructor Constraints #:arity >= 0)
(define-syntax Cs
  (syntax-parser
    [(_ [a b] ...)
     (Cs #'([a b] ...))]))
(begin-for-syntax
  (define (?∀ Xs τ)
    (if (stx-null? Xs)
        τ
        #`(∀ #,Xs #,τ)))
  (define (?Some Xs τ cs)
    (if (and (stx-null? Xs) (stx-null? cs))
        τ
        #`(Some #,Xs #,τ (Cs #,@cs))))
  (define (Cs cs)
    (syntax-parse cs
      [([a b] ...)
       #'(Constraints (Constraint a b) ...)]))
  (define-syntax ~?∀
    (pattern-expander
     (syntax-parser
       [(?∀ Xs-pat τ-pat)
        #'(~or (~∀ Xs-pat τ-pat)
               (~and (~not (~∀ _ _))
                     (~parse Xs-pat #'())
                     τ-pat))])))
  (define-syntax ~?∀*
    (pattern-expander
     (syntax-parser
       [(?∀* Xs-pat τ-pat)
        #:with Xs-orig (generate-temporary #'Xs-pat)
        #:with Xs* (generate-temporary #'Xs-pat)
        #:with τ-orig (generate-temporary #'τ-pat)
        #'(~and (~?∀ Xs-orig τ-orig)
                (~parse Xs* (generate-temporaries #'Xs-orig))
                (~parse Xs-pat #'Xs*)
                (~parse τ-pat (inst-type #'Xs* #'Xs-orig #'τ-orig)))])))
  (define-syntax ~?Some
    (pattern-expander
     (syntax-parser
       [(?Some Xs-pat τ-pat Cs-pat)
        #'(~or (~Some Xs-pat τ-pat Cs-pat)
               (~and (~not (~Some _ _ _))
                     (~parse Xs-pat #'[])
                     (~parse Cs-pat ((current-type-eval) #'(Cs)))
                     τ-pat))])))
  (define-syntax ~Cs
    (pattern-expander
     (syntax-parser #:literals (...)
       [(_ [a b] ooo:...)
        #:with cs (generate-temporary)
        #'(~and cs
                (~parse (~Constraints (~Constraint a b) ooo)
                        (if (syntax-e #'cs)
                            #'cs
                            ((current-type-eval) #'(Cs)))))]))))

(begin-for-syntax
  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (stx-contains-id? ty X))
      X))

  ;; constrainable-X? : Id Solved-Constraints (Stx-Listof Id) -> Boolean
  (define (constrainable-X? X cs Vs)
    (for/or ([c (in-list (stx->list cs))])
      (or (free-identifier=? X (stx-car c))
          (and (member (stx-car c) Vs free-identifier=?)
               (stx-contains-id? (stx-cadr c) X)
               ))))

  ;; find-constrainable-vars : (Stx-Listof Id) Solved-Constraints (Stx-Listof Id) -> (Listof Id)
  (define (find-constrainable-vars Xs cs Vs)
    (for/list ([X (in-list Xs)] #:when (constrainable-X? X cs Vs))
      X))

  ;; set-minus/Xs : (Listof Id) (Listof Id) -> (Listof Id)
  (define (set-minus/Xs Xs Ys)
    (for/list ([X (in-list Xs)]
               #:when (not (member X Ys free-identifier=?)))
      X))
  ;; set-intersect/Xs : (Listof Id) (Listof Id) -> (Listof Id)
  (define (set-intersect/Xs Xs Ys)
    (for/list ([X (in-list Xs)]
               #:when (member X Ys free-identifier=?))
      X))

  ;; some/inst/generalize : (Stx-Listof Id) Type-Stx Constraints -> Type-Stx
  (define (some/inst/generalize Xs* ty* cs1)
    (define Xs (stx->list Xs*))
    (define cs2 (add-constraints/var? Xs identifier? '() cs1))
    (define Vs (set-minus/Xs (stx-map stx-car cs2) Xs))
    (define constrainable-vars
      (find-constrainable-vars Xs cs2 Vs))
    (define constrainable-Xs
      (set-intersect/Xs Xs constrainable-vars))
    (define concrete-constrained-vars
      (for/list ([X (in-list constrainable-vars)]
                 #:when (empty? (find-free-Xs Xs (or (lookup X cs2) X))))
        X))
    (define unconstrainable-Xs
      (set-minus/Xs Xs constrainable-Xs))
    (define ty (inst-type/cs/orig constrainable-vars cs2 ty* datum=?))
    ;; pruning constraints that are useless now
    (define concrete-constrainable-Xs
      (for/list ([X (in-list constrainable-Xs)]
                 #:when (empty? (find-free-Xs constrainable-Xs (or (lookup X cs2) X))))
        X))
    (define cs3
      (for/list ([c (in-list cs2)]
                 #:when (not (member (stx-car c) concrete-constrainable-Xs free-identifier=?)))
        c))
    (?Some
     (set-minus/Xs constrainable-Xs concrete-constrainable-Xs)
     (?∀ (find-free-Xs unconstrainable-Xs ty) ty)
     cs3))

  (define (datum=? a b)
    (equal? (syntax->datum a) (syntax->datum b)))

  (define (tycons id args)
    (define/syntax-parse [X ...]
      (for/list ([arg (in-list (stx->list args))])
        (add-orig (generate-temporary arg) (get-orig arg))))
    (define/syntax-parse [arg ...] args)
    (define/syntax-parse (~∀ (X- ...) body)
      ((current-type-eval) #`(∀ (X ...) (#,id X ...))))
    (inst-type/cs #'[X- ...] #'([X- arg] ...) #'body))

  )

