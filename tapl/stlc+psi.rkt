#lang s-exp "typecheck.rkt"
;; (extends "stlc+sub.rkt" #:except #%datum #:rename [#%app stlc:#%app])
;(extends "stlc+tup.rkt" #:except + #%datum and)
;(extends "stlc+cons.rkt" #:except + #%datum and)
(reuse current-Π #:from "stlc+occurrence.rkt") ;; Install current-Π
(extends "sysf.rkt" #:except #%datum) ; load current-type=?

;; Parametric overloading.
;; - define overloadable functions with "template" types
;; - later, add implementations
;; -- typecheck the impl
;; -- save in a table
;; - for app, lookup the overloaded ID
;; - allow higher-order positions

;; Implementation strategy
;; - make explicit type for overloadables
;;   showing the __free variables__ and __instance carrier__
;; - new instances update the carrier
;; - lookups query the type; the type contains the lookup table

;; TODO
;; - constructors in carrier
;; - partially-applied constructors in carrier (× $ Int)
;; - subtyping (also resolve, in the middle of things... this is where Σ ∈ τ might be good)
;; - multiple params
;; - multiple methods (separate extension)

;; =============================================================================

(define-base-type Bot)
(define-base-type String)

(define-typed-syntax #%datum
  [(_ . n:str) (⊢ (#%datum . n) : String)]
  [(_ . x) #'(sysf:#%datum . x)])

;; =============================================================================
;; === ψ types

;; (ψ (α) § τ)
;; - α is a bound variable
;; - § is the carrier set for the algebra of types the ψ is defined on
;; - τ is a type with α free
(define-type-constructor ψ #:arity = 2 #:bvs = 1)
;; For representing carrier sets. The first argument to ψ should be an §-type
(define-type-constructor § #:arity >= 0)

;; TODO put these in typecheck.rkt
(begin-for-syntax
 (define (τ->symbol τ)
   (syntax-parse τ
    [(_ κ)
     (syntax->datum #'κ)]
    [(_ κ (_ () _ τ* ...))
     (define κ-str (symbol->string (syntax->datum #'κ)))
     (define τ-str*
       (map (compose1 symbol->string τ->symbol) (syntax->list #'(τ* ...))))
     (string->symbol
      (string-append
       (apply string-append "(" κ-str τ-str*)
       ")"))]
    [_
     (error 'τ->symbol (~a (syntax->datum τ)))]))

 ;; Canonicalize a set of types
 ;; (Sort & remove duplicates)
 (define (cannonize τ*)
   (sort (remove-duplicates τ* (current-type=?))
         symbol<?
         #:key τ->symbol))
)

(begin-for-syntax

 ;; (Lots of overlap with ∪-eval here)
 (define §-eval
   (let ([τ-eval (current-type-eval)])
     (lambda (τ-stx)
       ;; (printf "§-eval ~a\n" (syntax->datum τ-stx))
       (syntax-parse (τ-eval τ-stx)
        [(~§ τ-stx* ...)
         ;; Recursively evaluate members, should get a list of types
         ;; (Currently can't handle ∀, ∃, etc but idk a good way to detect that "class"
         (define τ*
           (for/list ([τ (in-syntax #'(τ-stx* ...))])
             (let ([τ+ ((current-type-eval) τ)])
               (if (§? τ+)
                   (error '§-eval (format "recursive carrier '~a'" (syntax->datum τ-stx)))
                   τ+))))
         ;; Remove duplicates, sort members
         (τ-eval #`(§ #,@(cannonize τ*)))]
        [τ
         #'τ]))))
 (current-type-eval §-eval)

 ;; Destruct ψ types into carrier & template.
 ;; - carriers should be τ=?* (zip & check),
 ;; - templates should be equal as ∀ types
 (define ψ=?
   (let ([τ=? (current-type=?)])
     (lambda (τ1 τ2)
       (syntax-parse (list τ1 τ2)
        [((~ψ (α) §1 τ_α)
          (~ψ (β) §2 τ_β))
         ;; WOW, I'm not even getting here
         (and (τ=? #'§1 #'§2)
              (τ=? ((current-type-eval) #`(∀ (α) τ_α))
                   ((current-type-eval) #`(∀ (β) τ_β))))]
        [_ (τ=? τ1 τ2)]))))

 ;; TODO add subtyping
 (current-type=? ψ=?)
 (current-typecheck-relation (current-type=?))
)

;; =============================================================================
;; === Signature maps
;; Covert a type to an implementation. Use current-type-eval to normalize keys.
;; These are the values with ψ type

 (define (Σ-print Σ port mode)
   ;; TODO why are tests triggering this?
   (displayln "*")
   (displayln (Σ->carrier Σ) port))

 (struct Σ (
   map ;; (Listof (Pairof τ* expr)), maps types to implementations
   ;; TODO may want a MUTALBE structure here instead
   ;; Hmm, if Σ is a #:mutable struct, am I certain untrusted people (outside this module)
   ;;  cannot modify it?
 ) #:constructor-name make-Σ
   #:property prop:procedure
   (lambda (self arg)
     (error 'Σ "Cannot apply struct, don't yet know how to turn types into predicates"))
   ;; #:methods gen:custom-write
   ;; [(define write-proc Σ-print)])
) 

 (define (Σ-init)
   (make-Σ '()))

 ;; Return the type representing Σ's carrier
 (define (Σ->carrier Σ)
   #`(§ #,@(map car (Σ-map Σ))))
   ;; ((current-type-eval) #`(§ #,@(map car (Σ-map Σ)))))
  
(define-syntax-rule (Σ-add Σ τ e)
  (make-Σ (cons (cons τ e) (Σ-map Σ))))


;; =============================================================================

(begin-for-syntax

 (define-syntax-rule (error-template sym reason)
   (error sym reason))

 (define-syntax-rule (instance-error reason)
   (error-template 'instance reason))

 (define-syntax-rule (resolve-error id τ reason)
   (error-template 'resolve id τ reason))
 
 (define-syntax-rule (signature-error τ reason)
   (error 'signature (format "Cannot declare signature at type '~a'. ~a"
                             (syntax->datum τ)
                             reason)))

)

(define-typed-syntax signature
  [(_ (α:id) τ)
   ;; Expand the type τ with α bound as a valid type
   #:with ((α+) τ+ _) (infer/tyctx+erase #'([α : #%type]) #'τ)
   ;; Make sure τ is (→ α τ') for some real type τ'
   #:when (syntax-parse #'τ+
           [(~→ τ-dom τ-cod)
            ;; τ-dom MUST be the (expanded) identifier α+
            (unless (and (identifier? #'τ-dom)
                         (free-identifier=? #'τ-dom #'α+))
              (signature-error #'τ
                               (format "Variable '~a' must be free in the signature type." (syntax->datum #'α))))]
           [_
            (signature-error #'τ "We only support single-argument functions with overloaded domains.")])
   ;; TODO duplicate the map, into the keys?
   ;; Do we save anything by putting it in the type, as opposed to tracking the value?
   ;; (I ddon't think soo.... either need the value or value's type annotation
   ;;  but maybe it's easier to propogate types than values across the type-checker)
   (⊢ (Σ-init)
      : (ψ (α) (§) τ))])

(define-typed-syntax instance
  [(_ Σ e)
   #:with [Σ+ τ_Σ] (infer+erase #'Σ)
   #:with [e+ τ_e] (infer+erase #'e)
   ;; τ_Σ should be a ψ type
   ;; τ_e should be an arrow (for now, really it should match τ_α)
   (syntax-parse #'(τ_Σ τ_e)
    [((~ψ (α) (~§ τ* ...) (~→ τ_α τ_cod1))
      (~→ τ_dom τ_cod2))
     (define τ=? (current-type=?))
     ;; Unify types (just ignore τ_α for now)
     (when (for/or ([τ (in-syntax #'(τ* ...))])
             (τ=? #'τ_dom τ))
       (instance-error (format "Duplicate instance at type '~a'" (syntax->datum #'τ_dom))))
     (unless (τ=? #'τ_cod1 #'τ_cod2)
       (printf "OH SNAP not eq ~a and ~a\n" (syntax->datum #'τ_cod1) (syntax->datum #'τ_cod2))
       (instance-error (format "Cannot unify '~a' with template '~a'"
                               (syntax->datum #'(→ τ_dom τ_cod2))
                               (syntax->datum #'(→ τ_α τ_cod1)))))
     
     (⊢ (Σ-add Σ+ #,((current-Π) #'τ_dom) e+)
        ;; (Hm, maybe just get type from the updated Σ
        ;; Just add τ_dom to the type --- TODO use a helper function
        : (ψ (α) (§ τ_dom τ* ...) (→ τ_α τ_cod1)))]
    ;; Error cases
    [(_
      (~→ τ* ...))
     (instance-error (format "cannot declare instance for non-overloadable type '~a'"
                             (syntax->datum #'τ_Σ)))]
    [((~ψ _ _ _)
      _)
     (instance-error (format "only → types can be instances, for now"))]
    [_
     (error (format "cannot unify types ~a and ~a\n"
                    (syntax->datum #'τ_Σ)
                    (syntax->datum #'τ_e)))])])

;; Eventually, take a list of types to an instance where the supplied types fill the holes.
;; TODO make available to user, use define-typed-syntax
#;(define-syntax (resolve stx)
 (syntax-parse stx
  [(_ e τ)
   ;; #:when (error (format "ORIGINAL TYPE ~a" (syntax->datum (typeof #'e))))
   #:with [e+ τ+] (⇑ e as ψ)
   ;; #:with [e+ ((α) Σ ((~→ τ_α τ_cod)))] (⇑ e as ψ)
   ;; (Temporary) Check that the type is a single-arg, overloaded-domain arrow
   ;; TODO we should be able to do fine without a λ in the way
   (error (format "my type is ~a\n" (syntax->datum #'τ+)))
   ;; #:fail-unless (free-identifier=? #'α #'τ_α)
   ;;   (format "Unsuppoted ψ-type ~a" (syntax->datum #'(→ τ_α τ_cod)))
   ;; #:when (printf "HEY my Σ is ~a\n" #'Σ)
   ;; ;; Lookup an implementation using the type (should this be a total function?)
   ;; ;; (We statically know, via keys in Σ, whether the lookup succeeds)
   ;; #:with e++ (#'Σ #'τ)
   #;(⊢ e++
      : (→ τ τ_cod))] ;; Fill in holes of the final type. TODO how does sysf fill holes?
  #;[(_ e τ)
   ;; Resolve any expression with a type. Why not.
   #:with [e+ τ+] (infer+erase #'e)
   #:fail-unless ((current-typecheck-relation) #'τ+ #'τ)
     (format "Cannot resolve type of expression ~a. Expected ~a, but actual type is ~a"
             (syntax->datum #'e+) (syntax->datum #'τ) (syntax->datum #'τ+))
   (⊢ e+ : τ)]))

;; Oh wait now, I really don't want to override #%app.
;; Lets just do resolve first, and make it explicit.
#;(define-typed-syntax #%app
  [(_ e_fn e_arg)
   ;; Check for overloaded e_fn
   #:with [e_fn+ _] (⇑ e_fn as ψ)
   ;; Infer the argument type
   #:with [e_arg+ τ_arg] (infer+erase #'e_arg)
   ;; Call out to resolve, then try apply again
   #`(#%app (resolve e_fn+ τ_arg) e_arg+)]
  [(_ e* ...)
   #'(#%app e* ...)])

