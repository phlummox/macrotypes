#lang s-exp "typecheck.rkt"
(reuse List cons nil #:from "stlc+cons.rkt")
(extends "stlc+sub.rkt")
(provide (for-syntax current-overload-resolver))

;; Revision of overloading, using identifier macros instead of overriding #%app

;; =============================================================================
;; === Resolvers

(begin-for-syntax

 ;; Resolver data structures stand for overloaded functions
 ;; - name : identifier for the overloaded function
 ;; - dom* : domains of the overloaded function
 ;; - cod  : range of the overloaded function
 ;; For now, only the domain can be overloaded
 ;;  and the domain must be one type (single-argument function).
 ;; TODO generalize to have 1 signature (with holes) and unifying types
 (struct ℜ (
   name ;; Syntax, an identifier
   dom* ;; (Box (Listof (Pairof Type Expr)))
   cod  ;; Type, (also syntax)
 ) #:constructor-name make-ℜ
;   #:prefab ;; Tried to avoid 3D syntax with this, but prefabs can't store syntax objs
 )

 ;; Register an expression `e` at type `τ`.
 ;; Future resolves looking for `τ` should return `e`.
 (define (ℜ-add! ℜ τ e) ; Rad!
   (define dom* (ℜ-dom* ℜ))
   (set-box! dom* (cons (cons τ e) (unbox dom*))))

 ;; Create an empty resolver -- an overloadable function with no instances
 (define (ℜ-init name τ-cod)
   (make-ℜ name (box '()) τ-cod))

 ;; Get the type represented by the resolver
 ;; Optional arguments fill in the holes
 (define (ℜ->type ℜ #:subst [τ-dom (assign-type #''α #'#%type)])
   ((current-type-eval) #`(→ #,τ-dom #,(ℜ-cod ℜ))))

 ;; Search the resolver's instances for one matching `τ`,
 ;;  according to comparator `=?`
 (define (ℜ-find ℜ τ #:=? =?)
   (define (τ=? τ2)
     (=? τ τ2))
   (assf τ=? (unbox (ℜ-dom* ℜ))))

 ;; Resolve a type into an instance
 (define (ℜ-resolve ℜ τ-or-e)
   (if (syntax? τ-or-e) ;; Can I ask "type?"
       (ℜ-resolve-syntax ℜ τ-or-e)
       (ℜ-resolve-value  ℜ τ-or-e)))

 (define (ℜ-resolve-syntax ℜ τ)
   ;; First try =? matches, then fall back to the typecheck relation
   ;; (In the fallback, the ORDER instances are stored resolves ties)
   (define result
     (or (ℜ-find ℜ τ #:=? (current-type=?))
         (and (not (eq? (current-type=?) (current-typecheck-relation)))
              (ℜ-find ℜ τ #:=? (current-typecheck-relation)))))
   (and (pair? result)
        (cdr result)))

 (define (ℜ-resolve-value ℜ e)
   (error 'ℜ (format "Runtime resolution not implemented. Anyway your value was ~a" e)))

 ;; True if the resolver does not have a binding for `τ`
 (define (ℜ-unbound? ℜ τ)
   (not (parameterize ([current-typecheck-relation (current-type=?)])
          (ℜ-resolve-syntax ℜ τ))))

 ;; Reflect an identifier into a resolver
 ;; - Trigger the identifier macro for `id`
 ;; - Parse the syntax-object result into a resolver structure
 (define (syntax->ℜ id)
   ;; Don't care about the type
   (define stx+τ (infer+erase id))
   ;; Boy, I wish I had a monad
   (define (fail)
     (error 'resolve (format "Identifier '~a' is not overloaded" (syntax->datum id))))
   (unless (pair? stx+τ) (fail))
   (define stx (car stx+τ))
   (unless (syntax? stx) (fail))
   (define ℜ-stx (syntax->datum (car stx+τ)))
   (unless (and (list? ℜ-stx)
                (not (null? ℜ-stx))
                (not (null? (cdr ℜ-stx))))
     (fail))
   (define ℜ (cadr ℜ-stx))
   (unless (ℜ? ℜ) (fail))
   ℜ)

 (define-syntax-rule (error-template sym id τ reason)
   (error sym (format "Failure for '~a' at type '~a'. ~a"
                      (syntax->datum id)
                      (syntax->datum τ)
                      reason)))

 (define-syntax-rule (instance-error id τ reason)
   (error-template 'instance id τ reason))

 (define-syntax-rule (resolve-error id τ)
   (error-template 'resolve id τ "Could not resolve instance."))

 (define current-overload-resolver (make-parameter ℜ-resolve))
)

;; =============================================================================
;; === Overloaded signature environment

(define-typed-syntax signature
  [(_ (name:id α:id) τ)
   #:with ((α+) (~→ τ_α:id τ-cod) _) (infer/tyctx+erase #'([α : #%type]) #'τ)
   (define ℜ (ℜ-init #'name #'τ-cod))
   (⊢ (define-syntax name
        (syntax-parser
         [_:id
          #'(quote #,ℜ)] ;; Is there a way to transmit ℜ directly?
         [(_ e)
          #:with [e+ τ+] (infer+erase #'e)
          #:with n+ ((current-overload-resolver) #,ℜ #'τ+)
          (unless (syntax-e #'n+)
            (resolve-error #'name #'τ+))
          (⊢ (#%app n+ e+)
             : τ-cod)]
         [(_ e* (... ...))
          #'(raise-arity-error (syntax->datum name) 1 e* (... ...))]))
      : Bot)]
  [(_ e* ...)
   (error 'signature (format "Expected (signature (NAME VAR) (→ VAR τ)), got ~a" (syntax->datum #'(e* ...))))])

(define-typed-syntax resolve/tc #:export-as resolve
  [(_ name:id τ)
   #:with τ+ ((current-type-eval) #'τ)
   ;; Extract a resolver from the syntax object
   (define ℜ (syntax->ℜ #'name))
   ;; Apply the resolver to the argument type. woo-wee!
   (define e (parameterize ([current-typecheck-relation (current-type=?)])
               ((current-overload-resolver) ℜ #'τ+)))
   (unless e (resolve-error #'name #'τ+))
   (⊢ #,e : #,(ℜ->type ℜ #:subst #'τ+))])

(define-typed-syntax instance
  [(_ (name:id τ-stx) e)
   #:with τ ((current-type-eval) #'τ-stx)
   #:with [e+ τ+] (infer+erase #'e)
   (define ℜ (syntax->ℜ #'name))
   (unless (ℜ-unbound? ℜ #'τ) (instance-error #'name #'τ "Overlaps with existing instance."))
   (define _unify ;; Should be a helper function
     (syntax-parse #`(τ+ #,(ℜ->type ℜ))
      [((~→ τ_dom1 τ_cod1)
        (~→ _      τ_cod2))
       ;; Really, need to unify this type with the template
       ;; (unless ((current-type=?) τ_dom1 τ_dom2)
       ;;   (instance-error #'name #'τ (format "Domain '~a' must unify with template domain '~a'."
       ;;                                      (syntax->datum #'τ_dom1) (syntax->datum #'τ_dom2))))
       (unless ((current-type=?) ((current-type-eval) #'τ) #'τ_dom1)
         (instance-error #'name #'τ (format "Domain '~a' must be the instance type, for now (2015-10-20)." (syntax->datum #'τ_dom1))))
       (unless ((current-type=?) #'τ_cod1 #'τ_cod2)
         (instance-error #'name #'τ (format "Codomain '~a' must match template codomain '~a'"
                                            (syntax->datum #'τ_cod1) (syntax->datum #'τ_cod2))))
       (void)]
      [(a b)
       (instance-error #'name #'τ (format "May only overload single-argument functions. (Got ~a and ~a)"
                                          (syntax->datum #'a) (syntax->datum #'b))
                                          )]))
   ;; Should we use syntax instead of e+ ?
   (ℜ-add! ℜ #'τ #'e+)
   (⊢ (void) : Bot)]
  [_
   (error 'instance "Expected (instance (id τ) e).")])
   
