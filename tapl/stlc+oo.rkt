#lang s-exp "typecheck.rkt"
(extends "stlc.rkt" #:rename [#%app stlc:#%app] [λ stlc:λ])
(extends "stlc+overloading.rkt")
(extends "stlc+occurrence+cons.rkt")

(begin-for-syntax
 (define (∪-resolve ℜ τ-∪)
   (syntax-parse τ-∪
    [(~∪ τ* ...)
     ;; Create a lambda that does run-time type tests for all the known types
     ;;  in the union
     (define dyn-id (generate-temporary))
     (define dyn-fail
       (⊢ (raise-user-error (format "Dynamic resolution failed for '~a' at value '~a'" '#,(syntax->datum (ℜ-name ℜ)) #,dyn-id))
          : Bot))
     (define dyn-body
       (for/fold ([body dyn-fail])
                 ([τ (in-syntax #'(τ* ...))])
         (let ([e ((current-overload-resolver) ℜ τ)])
           (if e
               #`(test (#,τ ? #,dyn-id)
                       (stlc:#%app #,e #,dyn-id)
                       #,body)
               body))))
     (and (not (eq? dyn-body dyn-fail))
          #`(stlc:λ ([#,dyn-id : (∪ τ* ...)]) #,dyn-body))]
    [_ ;; Lookup failed
     #f]))

 ;; Add the new fallback case to the old resolver.
 ;; If resolving for =? or <: fails, try destructuring the ∪ type
 (current-overload-resolver
   (let ([old-resolve (current-overload-resolver)])
     (lambda (ℜ τ)
       (or (old-resolve ℜ τ)
           (∪-resolve ℜ τ)))))
)

