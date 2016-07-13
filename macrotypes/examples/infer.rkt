#lang s-exp macrotypes/typecheck
(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not
         #:rename [~→ ~ext-stlc:→])
(require (only-in "sysf.rkt" ∀ ~∀ ∀? Λ))
(reuse cons [head hd] [tail tl] nil [isnil nil?] List list #:from "stlc+cons.rkt")
(require (only-in "stlc+cons.rkt" ~List))
(reuse tup × proj #:from "stlc+tup.rkt")
(reuse define-type-alias #:from "stlc+reco+var.rkt")
(require (for-syntax "../type-constraints.rkt"))
(provide hd tl nil?)
(provide →)

;; a language with partial (local) type inference using bidirectional type checking

(define-syntax → ; wrapping →
  (syntax-parser
    [(→ (~and Xs {X:id ...}) . rst)
     #:when (brace? #'Xs)
     (add-orig #'(∀ (X ...) (ext-stlc:→ . rst)) (get-orig this-syntax))]
    [(→ . rst) (add-orig #'(∀ () (ext-stlc:→ . rst)) (get-orig this-syntax))]))

(define-primop + : (→ Int Int Int))
(define-primop - : (→ Int Int Int))
(define-primop void : (→ Unit))
(define-primop = : (→ Int Int Bool))
(define-primop zero? : (→ Int Bool))
(define-primop sub1 : (→ Int Int))
(define-primop add1 : (→ Int Int))
(define-primop not : (→ Bool Bool))
(define-primop abs : (→ Int Int))

(begin-for-syntax
  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (stx-contains-id? ty X))
      X))

  ;; solve : (Stx-Listof Id) (Stx-Listof Stx) (Stx-Listof Type-Stx)
  ;;         -> (List Constraints (Listof (Stx-List Stx Type-Stx)))
  ;; Solves for the Xs by inferring the type of each arg and unifying it against
  ;; each corresponding expected-τ (which could have free Xs in them).
  ;; It returns list of 2 values if successful, else throws a type error
  ;;  - the constraints for substituting the types
  ;;  - a list containing of all the arguments paired with their types
  (define (solve Xs args expected-τs)
    (let-values
        ([(cs e+τs)
          (for/fold ([cs '()] [e+τs #'()])
                    ([e_arg (syntax->list args)]
                     [τ_inX (syntax->list expected-τs)])
            (define τ_in (inst-type/cs Xs cs τ_inX))
            (define/with-syntax [e τ]
              (infer+erase (if (empty? (find-free-Xs Xs τ_in))
                               (add-expected-ty e_arg τ_in)
                               e_arg)))
            ;             (displayln #'(e τ))
            (define cs* (add-constraints Xs cs #`([τ #,τ_in])))
            (values cs* (cons #'[e τ] e+τs)))])
      (list cs (reverse (stx->list e+τs))))))

(define-typed-syntax define
  [(define x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin-
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define- y e-))]
  [(define (~and Xs {X:id ...}) (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:when (brace? #'Xs)
   #:with g (generate-temporary #'f)
   #:with e_ann #'(add-expected e τ_out)
   #'(begin-
       (define-syntax f (make-rename-transformer
                         (⊢ g : #,(add-orig #'(∀ (X ...) (ext-stlc:→ τ ... τ_out))
                                            #'(→ τ ... τ_out)))))
       (define- g (Λ (X ...) (ext-stlc:λ ([x : τ] ...) e_ann))))]
  [(define (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:with g (generate-temporary #'f)
   #:with e_ann #'(add-expected e τ_out)
   #'(begin-
       (define-syntax f (make-rename-transformer (⊢ g : (→ τ ... τ_out))))
       (define- g (ext-stlc:λ ([x : τ] ...) e_ann)))])

; all λs have type (∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax λ #:datum-literals (:)
  [(λ (x:id ...) e) ; no annotations, try to infer from outer ctx, ie an application
   #:with given-τ-args (syntax-property stx 'given-τ-args)
   #:fail-unless (syntax-e #'given-τ-args) ; no inferred types or annotations, so error
                 (format "input types for ~a could not be inferred; add annotations"
                         (syntax->datum stx))
   #:with (τ_arg ...) #'given-τ-args
   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ ([x : τ_arg] ...) e))
   (⊢ fn- : #,(add-orig #'(∀ () τ_fn) (get-orig #'τ_fn)))]
  [(_ (x:id ...) ~! e) ; no annotations, couldnt infer from ctx (eg, unapplied lam), try to infer from body
   #:with (xs- e- τ_res) (infer/ctx+erase #'([x : x] ...) #'e)
   #:with env (get-env #'e-)
   #:fail-unless (syntax-e #'env)
                 (format "input types for ~a could not be inferred; add annotations"
                         (syntax->datum stx))
   #:with (τ_arg ...) (stx-map (λ (y) (lookup y #'env)) #'xs-)
   #:fail-unless (stx-andmap syntax-e #'(τ_arg ...))
                 (format "some input types for ~a could not be inferred; add annotations"
                         (syntax->datum stx))
   ;; propagate up inferred types of variables
   #:with res (add-env #'(λ- xs- e-) #'env)
;   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ ([x : x] ...) e))
   (⊢ res : #,(add-orig #'(∀ () (ext-stlc:→ τ_arg ... τ_res))
                        #`(→ #,@(stx-map get-orig #'(τ_arg ... τ_res)))))]
   ;(⊢ (λ- xs- e-) : (∀ () (ext-stlc:→ τ_arg ... τ_res)))]
  [(λ . rst)
   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ . rst))
   (⊢ fn- : #,(add-orig #'(∀ () τ_fn) (get-orig #'τ_fn)))])

(define-typed-syntax infer:#%app #:export-as #%app
  [(_ e_fn e_arg ...) ; infer args first
 ;  #:when (printf "args first ~a\n" (syntax->datum stx))
   #:with maybe-inferred-τs (with-handlers ([exn:fail:type:infer? (λ _ #f)])
                                 (infers+erase #'(e_arg ...)))
   #:when (syntax-e #'maybe-inferred-τs)
   #:with ([e_arg- τ_arg] ...) #'maybe-inferred-τs
   #:with e_fn_anno (syntax-property #'e_fn 'given-τ-args #'(τ_arg ...))
;   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn_anno as →)
   #:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn_anno as ∀)
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...)) ; check arity
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Wrong number of arguments given to function ~a.\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  (format "Expected: ~a arguments with types: "
                          (stx-length #'(τ_inX ...)))
                  (string-join (stx-map type->str #'(τ_inX ...)) ", " #:after-last "\n")
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n")))
   #:with cs (add-constraints #'(X ...) '() #'([τ_arg τ_inX] ...))
   #:with (τ_in ... τ_out) (inst-types/cs #'(X ...) #'cs #'(τ_inX ... τ_outX))
   ; some code duplication
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Arguments to function ~a have wrong type(s).\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(τ_in ...)))
                  (string-join (stx-map type->str #'(τ_in ...)) ", ")))
   ; propagate inferred types for variables up
   #:with env (stx-flatten (filter (λ (x) x) (stx-map get-env #'(e_arg- ...))))
   #:with result-app (add-env #'(#%app- e_fn- e_arg- ...) #'env)
   ;(⊢ (#%app- e_fn- e_arg- ...) : τ_out)]
   (⊢ result-app : τ_out)]
  [(_ e_fn e_arg ...) ; infer fn first ------------------------- ; TODO: remove code dup
;   #:when (printf "fn first ~a\n" (syntax->datum stx))
   #:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn as ∀)
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...)) ; check arity
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Wrong number of arguments given to function ~a.\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  (format "Expected: ~a arguments with types: "
                          (stx-length #'(τ_inX ...)))
                  (string-join (stx-map type->str #'(τ_inX ...)) ", " #:after-last "\n")
                  "Given args: "
                  (string-join (map ~a (syntax->datum #'(e_arg ...))) ", ")))
;   #:with ([e_arg- τ_arg] ...) #'(infers+erase #'(e_arg ...))
   #:with (cs ([e_arg- τ_arg] ...))
          (solve #'(X ...) #'(e_arg ...) #'(τ_inX ...))
   #:with env (stx-flatten (filter (λ (x) x) (stx-map get-env #'(e_arg- ...))))
   #:with (τ_in ... τ_out) (inst-types/cs #'(X ...) #'cs #'(τ_inX ... τ_outX))
   ; some code duplication
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (string-append
                  (format "~a (~a:~a) Arguments to function ~a have wrong type(s).\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(τ_in ...)))
                  (string-join (stx-map type->str #'(τ_in ...)) ", "))
  #:with result-app (add-env #'(#%app- e_fn- e_arg- ...) #'env)
  ;(⊢ (#%app- e_fn- e_arg- ...) : τ_out)])
  (⊢ result-app : τ_out)])
