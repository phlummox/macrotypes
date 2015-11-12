#lang s-exp "typecheck.rkt"
;; (extends "stlc+sub.rkt" #:except #%datum #:rename [#%app stlc:#%app])
;(extends "stlc+tup.rkt" #:except + #%datum and)
;(extends "stlc+cons.rkt" #:except + #%datum and)
(reuse [#%datum stlc+occurrence:#%datum] current-Π current-sub? Nat Bot Str Boolean #:from "stlc+occurrence.rkt")
(extends "sysf.rkt" #:except #%datum + #:rename [#%app stlc:#%app]) ; load current-type=?

;; Parametric overloading.
;; - (signature (α) τ) : define overloadable function with type τ
;; - (instance σ e)    : add implementation `e` to the overloaded `σ`
;; -- `e` is typechecked against the declared signature
;; -- code for `e` is associated with the type it replaces `α` with
;; - (resolve σ τ) : uses the type `τ` to convert the overloaded `σ` to an exact instance

;; Overloaded functions are first class, and can be passed as arguments etc.
;; They try to resolve at compile-time, but will resort to run-time tag checks

;; Implementation strategy
;; - make explicit type for overloadables
;;   showing the __free variables__ and __instance carrier__
;; - new instances update the carrier
;; - lookups query the type; the type contains the lookup table

;; TODO
;; - constructors in carrier (× α α)
;; - partially-applied constructors in carrier (× $ Int)
;; - subtyping (also resolve, in the middle of things... this is where Σ ∈ τ might be good)
;; - multiple params
;; - multiple methods (separate extension)

(define-typed-syntax #%datum
  [(_ . n)
   ;; TODO why is this getting called? is datum called on types?
   #:when (⟦Σ⟧? (syntax-e #'n))
   (⊢ (#%datum . n) : #%type)]
  [(_ . x) #'(stlc+occurrence:#%datum . x)])
   

;; =============================================================================
;; === ψ types

;; (ψ (α) § τ)
;; - α is a bound variable
;; - § is the carrier set for the algebra of types the ψ is defined on
;; - τ is a type with α free
;; TODO : round2, § now contains a compile-time map
(define-type-constructor ψ #:arity = 2 #:bvs = 1)
;; For representing carrier sets. The first argument to ψ should be an §-type
(define-type-constructor § #:arity >= 0)

;; =============================================================================
;; === Type->Expr maps

;; § is compile-time, Σ lives at runtime

(struct Σ (
  map ;; (Listof (Pairof (-> Any Boolean) Expr)), maps type predicates to implementations
 ) #:transparent
   #:constructor-name make-Σ
   #:property prop:procedure
   (lambda (self arg)
     (define fn (Σ-lookup self arg))
     (fn arg)))

(define (Σ-add Σ τ e)
  (make-Σ (cons (cons τ e) (Σ-map Σ))))

(define (Σ-init)
  (make-Σ '()))

(define (Σ-lookup Σ e)
  (or
   (for/first ([τ+e (in-list (Σ-map Σ))] #:when ((car τ+e) e))
     (cdr τ+e))
   (error 'Σ (format "Runtime type dispatch failed: no match for argument '~a'" e))))

;; -----------------------------------------------------------------------------

(begin-for-syntax
 (define (⟦Σ⟧-write ⟦Σ⟧ port mode)
   ;; Synthesize a §-type
   (define s ((current-type-eval) #`(§ #,@(map car (⟦Σ⟧-map ⟦Σ⟧)))))
   (if mode
       (write   s port)
       (display s port)))

 (struct ⟦Σ⟧ (
   map
  ) #:transparent
    #:constructor-name make-⟦Σ⟧
    #:methods gen:custom-write
    [(define write-proc ⟦Σ⟧-write)]
 )

 (define (⟦Σ⟧-add ⟦Σ⟧ τ e)
   (make-⟦Σ⟧ (cons (cons τ e) (⟦Σ⟧-map ⟦Σ⟧))))

;; Update the type τ with the new map Σ
;; TODO does not check "τ consistent with Σ"
;;      better to weave this into ⟦Σ⟧-add ?
 (define (⟦Σ⟧->type τ Σ)
   (syntax-parse τ
    [(~ψ A _ τ)
     #`(ψ A #,(assign-type #`#,Σ #'#%type) τ)]))

 ;; mem uses =?, and returns a boolean.
 ;; If this returns true, runtime lookups will succeed (even if compile-time fails)
 (define (⟦Σ⟧-mem? ⟦Σ⟧ τ [τ<=? (current-type=?)])
   (for/or ([τ+e (in-list (⟦Σ⟧-map ⟦Σ⟧))])
     (τ<=? τ (car τ+e))))

 (define (⟦Σ⟧-init)
   (make-⟦Σ⟧ '()))

 ;; lookup uses <=?, and returns the function
 ;; if you want =?, override the parameter first
 (define (⟦Σ⟧-lookup ⟦Σ⟧ τ [τ<=? (current-type=?)])
   (for/first ([τ+e (in-list (⟦Σ⟧-map ⟦Σ⟧))]
               #:when (τ<=? τ (car τ+e)))
     (cdr τ+e)))

 ;; Check that all the types (keys) are the same
 (define (⟦Σ⟧=? τ=? ⟦Σ⟧1 ⟦Σ⟧2)
   ;; idk if τ=? should be a parameter or not
   (let loop ([τ1* (cannonize (map car (⟦Σ⟧-map ⟦Σ⟧1)))]
              [τ2* (cannonize (map car (⟦Σ⟧-map ⟦Σ⟧2)))])
     (cond
      [(and (null? τ1*) (null? τ2*))
       #t]
      [(and (not (null? τ1*)) (not (null? τ2*)))
       (and (τ=? (car τ1*) (car τ2*))
            (loop (cdr τ1*) (cdr τ2*)))]
      [else 
       #f])))

 ;; Reflect an §-type to a syntax map, for uniformity
 (define (§->⟦Σ⟧ τ*)
   (make-⟦Σ⟧ (for/list ([τ (in-list (cannonize τ*))]) (cons τ #f))))
)

;; =============================================================================

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

;; τ eval+equality
(begin-for-syntax
 (define ψ-eval
   (let ([τ-eval (current-type-eval)])
     (lambda (τ-stx)
       (syntax-parse (τ-eval τ-stx)
        [(~ψ (α* ...) (~§ τ* ...) τ_α)
         ;; Assert § is a valid carrier set (no variables besides α, not recursive)
         ;; (Currently can't handle ∀, ∃, etc but idk a good way to detect that "class")
         (define τ*+ 
           ;; By the way, collect results in a list for the upcoming call to `cannonize`
           (for/list ([τ (in-syntax #'(τ* ...))])
             (when (§? τ)
               (error 'ψ-eval (format "Recursive carrier set '~a'" (syntax->datum #'(τ* ...)))))
             τ))
         ;; ... could also check well-formedness of τ_α, not sure if this is the best place
         ;;(§ #,@(cannonize τ*))
         (τ-eval #`(ψ (α* ...) #,(assign-type #`#,(§->⟦Σ⟧ (cannonize τ*+)) #'#%type) τ_α))]
        [τ
         #'τ]))))
 (current-type-eval ψ-eval)

 ;; Destruct ψ types into carrier & template.
 ;; - carriers should be τ=?* (zip & check),
 ;; - templates should be equal as ∀ types
 (define ψ=?
   (let ([τ=? (current-type=?)])
     (lambda (τ1 τ2)
       (syntax-parse (list τ1 τ2)
        [((~ψ (α) ⟦Σ⟧1 τ_α)
          (~ψ (β) ⟦Σ⟧2 τ_β))
         (and (⟦Σ⟧=? τ=? (syntax->struct #'⟦Σ⟧1) (syntax->struct #'⟦Σ⟧2))
              (τ=? ((current-type-eval) #`(∀ (α) τ_α))
                   ((current-type-eval) #`(∀ (β) τ_β))))]
        [_ (τ=? τ1 τ2)]))))

 (define (syntax->struct stx)
   (unless (syntax? stx)
     (error 'syntax->struct (format "expected a syntax object, got '~a'" stx)))
   (define e (syntax-e stx))
   (unless (and (list? e) (not (null? e)) (not (null? (cdr e))))
     (error 'syntax->struct (format "expected a quoted value, got '~a'" e)))
   (define e+ (cadr e))
   (unless (syntax? e+)
     (error 'syntax->struct (format "expected a nested syntax object, got '~a'" e+)))
   (syntax-e e+))

 (current-type=? ψ=?)
 (current-typecheck-relation (current-sub?))
)

;; =============================================================================

(begin-for-syntax

 (define-syntax-rule (error-template sym reason)
   (error sym reason))

 (define-syntax-rule (instance-error reason)
   (error-template 'instance reason))

 (define-syntax-rule (resolve-error τ reason)
   (error-template 'resolve (format "Cannot resolve at type '~a'. ~a"
                                    (syntax->datum τ)
                                    reason)))
 
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
   (⊢ (Σ-init)
      : (ψ (α) #,(assign-type #`#,(⟦Σ⟧-init) #'#%type) τ))])

(define-typed-syntax instance
  [(_ Σ e)
   #:with [Σ+ τ_Σ] (infer+erase #'Σ)
   #:with [e+ τ_e] (infer+erase #'e)
   ;; τ_Σ should be a ψ type
   ;; τ_e should be an arrow (for now, really it should match τ_α)
   (syntax-parse #'(τ_Σ τ_e)
    [((~ψ (α) ⟦Σ⟧-stx (~→ τ_α τ_cod_template))
      (~→ τ_dom τ_cod_actual))
     (define ⟦Σ⟧ (syntax->struct #'⟦Σ⟧-stx))
     ;; Assert τ_dom is new
     (when (⟦Σ⟧-mem? ⟦Σ⟧ #'τ_dom)
       (instance-error (format "Duplicate instance at type '~a'" (syntax->datum #'τ_dom))))
     ;; Unify codomains (just ignore τ_α for now)
     (unless ((current-typecheck-relation) #'τ_cod_actual #'τ_cod_template)
       (instance-error (format "Cannot unify '~a' with template '~a'"
                               (syntax->datum #'(→ τ_dom τ_cod_actual))
                               (syntax->datum #'(→ τ_α τ_cod_template)))))
     (⊢ (Σ-add Σ+ #,((current-Π) #'τ_dom) e+)
        : #,(⟦Σ⟧->type #'τ_Σ (⟦Σ⟧-add ⟦Σ⟧ #'τ_dom #'e+)))]
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

(define-for-syntax (resolve/internal e τ τ<=?)
  ;; TODO don't unfold the type to an →, instead [τ / α]
  (syntax-parse (infer+erase e)
   [(Σ (~ψ (α) ⟦Σ⟧-stx (~→ τ_α τ_cod)))
    #:with τ+ ((current-type-eval) τ)
    (define ⟦Σ⟧ (syntax->struct #'⟦Σ⟧-stx))
    (unless (⟦Σ⟧-mem? ⟦Σ⟧ #'τ+ τ<=?)
      (resolve-error τ "No matching instance."))
    ;; Try resolving statically, else use the actual term Σ as a dictionary
    (define f (or (⟦Σ⟧-lookup ⟦Σ⟧ #'τ+ τ<=?) #'Σ))
    (⊢ #,f
      ;; TODO use subst on the type, don't unfold into an →
      : (→ τ+ τ_cod))]))

(define-typed-syntax resolve
  [(_ e τ)
   (resolve/internal #'e #'τ (current-type=?))])

;; Hijack application to typecheck
(define-typed-syntax app/tc #:export-as #%app
  [(_ e_1 e_2)
   ;; Check that e_1 is a ψ-type after expanding
   #:with [e_1+ τ_1+] (infer+erase #'e_1)
   #:when (ψ? #'τ_1+)
   #:with [e_2+ τ_2+] (infer+erase #'e_2)
   ;; Try resolving, then #%app like normal
   #`(stlc:#%app #,(resolve/internal #'e_1+ #'τ_2+ (current-sub?)) e_2+)]
  [(_ e* ...)
   #'(stlc:#%app e* ...)])
