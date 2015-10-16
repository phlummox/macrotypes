#lang s-exp "typecheck.rkt"
 
;; Simply-Typed Lambda Calculus
;; - no base types; can't write any terms
;; Types: multi-arg → (1+)
;; Terms:
;; - var
;; - multi-arg λ (0+)
;; - multi-arg #%app (0+)
;; Other:
;; - "type" syntax category; defines:
;;   - define-base-type
;;   - define-type-constructor
;; Typechecking forms:
;; - current-type-eval

(begin-for-syntax
  ;; type eval
  ;; - type-eval == full expansion == canonical type representation
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  ;;   - checks for valid types, ow can't distinguish types and terms
  ;;     - could parse types but separate parser leads to duplicate code
  ;;   - later, expanding enables reuse of same mechanisms for kind checking
  ;;     and type application
  (define (type-eval τ)
    ; TODO: optimization: don't expand if expanded
    ; currently, this causes problems when
    ; combining unexpanded and expanded types to create new types
    (add-orig (expand/df τ) τ))

  (current-type-eval type-eval)
  )
  
(define-syntax-category type)

(define-type-constructor → #:arity >= 1
  #:sub? (λ (this other)
           (syntax-parse (list this other)
             [[(~→ in1 ... out1) (~→ in2 ... out2)]
              (and (typecheck? #'out1 #'out2)
                   (typechecks? #'(in2 ...) #'(in1 ...)))]
             [_ #f])))

(define-typed-syntax λ
  [(_ bvs:type-ctx e)
   #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
   (⊢ (λ xs- e-) : (→ bvs.type ... τ_res))])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...)
   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn as →)
   #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (string-append
                  (format "~a (~a:~a) Arguments to function ~a have wrong type(s), "
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  "or wrong number of arguments:\nGiven:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(τ_in ...)))
                  (string-join (stx-map type->str #'(τ_in ...)) ", "))
  (⊢ (#%app e_fn- e_arg- ...) : τ_out)])
