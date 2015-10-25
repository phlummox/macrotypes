#lang s-exp "typecheck.rkt"
(extends "stlc+overloading.rkt")
(extends "stlc+occurrence.rkt")

(begin-for-syntax
 (define (∪-resolve ℜ τ-∪)
   (syntax-parse τ-∪
    [(~∪ τ* ...)
     ;; Create a lambda that does run-time type tests for all the known types
     ;;  in the union
     (define dyn-id (generate-temporary))
     (define dyn-fail #`(raise-user-error (format "Dynamic resolution failed for '~a' at value '~a'" '#,(syntax->datum (ℜ-name ℜ)) #,dyn-id)))
     (define dyn-body ;; The untyped version
       (for/fold ([body dyn-fail])
                 ([τ (in-syntax #'(τ* ...))])
         (let ([e ((current-overload-resolver) ℜ τ)])
           (if e
               #`(if (#,((current-Π) τ) #,dyn-id)
                     (#,e #,dyn-id)
                     #,body)
               body))))
     #`(lambda (#,dyn-id) #,dyn-body)]
     ;; (define dyn-body ;; Typed version, currently broken
     ;;   (for/fold ([body dyn-fail])
     ;;             ([τ (in-syntax #'(τ* ...))])
     ;;     (let ([e ((current-overload-resolver) ℜ τ)])
     ;;       (if e
     ;;           #`(test (#,τ ? #,dyn-id)
     ;;                   (#,e #,dyn-id)
     ;;                   #,body)
     ;;           body))))
     ;; #`(λ ([#,dyn-id : (∪ τ* ...)]) #,dyn-body)]
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

