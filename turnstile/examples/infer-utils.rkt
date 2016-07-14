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
                     could-be-var?
                     tycons
                     gen-alphabetical-tyvars
                     ))

(require macrotypes/typecheck
         (only-in "stlc.rkt" define-type-constructor #%type)
         (only-in "sysf.rkt" ∀ ~∀ ∀?)
         (for-syntax racket/base
                     syntax/parse
                     macrotypes/type-constraints))

(module+ test
  (require (for-syntax rackunit)))

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

  ;; find-free-Xs/type-order : (Stx-Listof Id) Type -> (Listof Id)
  (define (find-free-Xs/type-order Xs ty)
    (sort-ids/stx (find-free-Xs Xs ty) ty))

  ;; find-constrainable-vars : (Stx-Listof Id) Solved-Constraints (Stx-Listof Id) -> (Listof Id)
  (define (find-constrainable-vars Xs cs Vs)
    (syntax-parse cs
      [() Vs]
      [([a b] . rst)
       (cond
         [(member #'a Vs free-identifier=?)
          (find-constrainable-vars
           Xs
           #'rst
           (append (find-free-Xs Xs #'b) Vs))]
         ;; TODO: Generalize this for not-in-Xs identifiers deeper within #'b
         [(and (could-be-var? #'b) (not (member #'b Xs free-identifier=?)))
          (find-constrainable-vars
           Xs
           #'rst
           (cons #'a (cons #'b Vs)))]
         [else
          (define Vs*
            (find-constrainable-vars
             Xs
             #'rst
             Vs))
          (cond [(member #'a Vs* free-identifier=?)
                 (append (find-free-Xs Xs #'b) Vs*)]
                [else
                 (cons #'a Vs*)])])]))

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

  ;; could-be-var? : Any -> Boolean
  (define (could-be-var? v)
    (and (identifier? v)
         (not (free-identifier=? v #'#%type))))

  ;; some/inst/generalize : (Stx-Listof Id) Type-Stx (Listof Constraints) -> Type-Stx
  (define (some/inst/generalize Xs* ty* css1)
    (define Xs (stx->list Xs*))
    (define cs2 (add-constraintss/var? Xs could-be-var? '() css1))
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
     (?∀ (find-free-Xs/type-order unconstrainable-Xs ty) ty)
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

  ;; gen-alphabetical-tyvars : (Stx-Listof Any) -> (Listof Id)
  (define (gen-alphabetical-tyvars vs)
    (generate-temporaries
     (for/list ([i (in-range (stx-length vs))])
       (string-titlecase (alphabetical-string (add1 i))))))

  (define alphabet (string->list "abcdefghijklmnopqrstuvwxyz"))

  ;; alphabetical-string : Positive-Integer -> String
  (define (alphabetical-string i)
    (list->string (alphabetical-char-list i (list))))

  ;; alphabetic-char-list : Positive-Integer (Listof Char) -> (Listof Char)
  (define (alphabetical-char-list i acc)
    (define-values [q r]
      ;; anyone know why there's a sub1 here?
      (quotient/remainder (sub1 i) 26))
    (cond [(zero? q)
           (cons (list-ref alphabet r) acc)]
          [else
           (alphabetical-char-list q
             (cons (list-ref alphabet r) acc))]))

  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (begin-for-syntax
    (define alpha alphabetical-string)
    (check-equal? (alpha 1) "a")
    (check-equal? (alpha 2) "b")
    (check-equal? (alpha 3) "c")
    (check-equal? (alpha 26) "z")
    (check-equal? (alpha (+ (* 1 26) 1)) "aa")
    (check-equal? (alpha (+ (* 1 26) 2)) "ab")
    (check-equal? (alpha (+ (* 1 26) 3)) "ac")
    (check-equal? (alpha (+ (* 1 26) 26)) "az")
    (check-equal? (alpha (+ (* 2 26) 1)) "ba")
    (check-equal? (alpha (+ (* 2 26) 2)) "bb")
    (check-equal? (alpha (+ (* 2 26) 3)) "bc")
    (check-equal? (alpha (+ (* 2 26) 26)) "bz")
    (check-equal? (alpha (+ (* 3 26) 1)) "ca")
    (check-equal? (alpha (+ (* 3 26) 2)) "cb")
    (check-equal? (alpha (+ (* 3 26) 3)) "cc")
    (check-equal? (alpha (+ (* 3 26) 26)) "cz")
    (check-equal? (alpha (+ (* 26 26) 1)) "za")
    (check-equal? (alpha (+ (* 26 26) 2)) "zb")
    (check-equal? (alpha (+ (* 26 26) 3)) "zc")
    (check-equal? (alpha (+ (* 26 26) 26)) "zz")
    (check-equal? (alpha (+ (* 26 26) 1)) "za")
    (check-equal? (alpha (+ (* 26 26) 2)) "zb")
    (check-equal? (alpha (+ (* 26 26) 3)) "zc")
    (check-equal? (alpha (+ (* (+ (* 1 26) 1) 26) 1)) "aaa")
    (check-equal? (alpha (+ (* (+ (* 1 26) 1) 26) 2)) "aab")
    (check-equal? (alpha (+ (* (+ (* 1 26) 1) 26) 3)) "aac")
    (check-equal? (alpha (+ (* (+ (* 1 26) 2) 26) 1)) "aba")
    (check-equal? (alpha (+ (* (+ (* 1 26) 2) 26) 2)) "abb")
    (check-equal? (alpha (+ (* (+ (* 1 26) 2) 26) 3)) "abc")
    (check-equal? (alpha (+ (* (+ (* 1 26) 3) 26) 1)) "aca")
    (check-equal? (alpha (+ (* (+ (* 1 26) 3) 26) 2)) "acb")
    (check-equal? (alpha (+ (* (+ (* 1 26) 3) 26) 3)) "acc")
    (check-equal? (alpha (+ (* (+ (* 2 26) 1) 26) 1)) "baa")
    (check-equal? (alpha (+ (* (+ (* 2 26) 1) 26) 2)) "bab")
    (check-equal? (alpha (+ (* (+ (* 2 26) 1) 26) 3)) "bac")
    (check-equal? (alpha (+ (* (+ (* 2 26) 2) 26) 1)) "bba")
    (check-equal? (alpha (+ (* (+ (* 2 26) 2) 26) 2)) "bbb")
    (check-equal? (alpha (+ (* (+ (* 2 26) 2) 26) 3)) "bbc")
    (check-equal? (alpha (+ (* (+ (* 2 26) 3) 26) 1)) "bca")
    (check-equal? (alpha (+ (* (+ (* 2 26) 3) 26) 2)) "bcb")
    (check-equal? (alpha (+ (* (+ (* 2 26) 3) 26) 3)) "bcc")
    (check-equal? (alpha (+ (* (+ (* 3 26) 1) 26) 1)) "caa")
    (check-equal? (alpha (+ (* (+ (* 3 26) 1) 26) 2)) "cab")
    (check-equal? (alpha (+ (* (+ (* 3 26) 1) 26) 3)) "cac")
    (check-equal? (alpha (+ (* (+ (* 3 26) 2) 26) 1)) "cba")
    (check-equal? (alpha (+ (* (+ (* 3 26) 2) 26) 2)) "cbb")
    (check-equal? (alpha (+ (* (+ (* 3 26) 2) 26) 3)) "cbc")
    (check-equal? (alpha (+ (* (+ (* 3 26) 3) 26) 1)) "cca")
    (check-equal? (alpha (+ (* (+ (* 3 26) 3) 26) 2)) "ccb")
    (check-equal? (alpha (+ (* (+ (* 3 26) 3) 26) 3)) "ccc")
    ))

