#lang s-exp "typecheck.rkt"
;; (extends "stlc+sub.rkt" #:except #%datum #:rename [#%app stlc:#%app])
;(extends "stlc+tup.rkt" #:except + #%datum and)
;(extends "stlc+cons.rkt" #:except + #%datum and)
(reuse [#%datum stlc+occurrence:#%datum] current-Π current-sub? Nat Num Bot Str Boolean #:from "stlc+occurrence.rkt")
(extends "sysf.rkt" #:except #%datum + #:rename [#%app stlc:#%app]) ; load current-type=?

;; Parametric overloading.
;; - (signature (α) τ) : define overloadable function with type τ
;; - (instance σ e)    : add implementation `e` to the overloaded `σ`
;; -- `e` is typechecked against the declared signature
;; -- code for `e` is associated with the type it replaces `α` with
;; - (resolve σ τ) : uses the type `τ` to convert the overloaded `σ` to an exact instance

;; Overloaded functions are first class, and can be passed as arguments etc.
;; They try to resolve at compile-time, but will resort to run-time typecase

;; TODO
;; - poly. constructors in carrier (× α α)
;; - partially-applied constructors in carrier (× $ Int)
;; - multiple methods (separate extension)
;; - overload codomain
;; - overload non-functions
;; INFERENCE
;; lambda, resolve S=t to a plain arrow
;; lambda, infer argument use (via flow) on a poly, resolve to plain arrow
;; var-arity, one arg instantiates the rest

(define-typed-syntax #%datum
  [(_ . n)
   #:when (⟦Σ⟧? (syntax-e #'n))
   (⊢ (#%datum . n) : #%type)]
  [(_ . x) #'(stlc+occurrence:#%datum . x)])

;; =============================================================================
;; === ψ types

(define-type-constructor ψ #:arity = 2 #:bvs >= 1)
;; (ψ (α) § τ)
;; - α is a bound variable
;; - § is the carrier set for the algebra of types the ψ is defined on
;; - τ is a type with α free

(define-type-constructor § #:arity >= 0)
;; (§ τ* ...)
;; For representing carrier sets. The first argument to ψ should be an §-type

(define-type-constructor · #:arity >= 1)
;; (· τ* ...)
;; Internal to §, should only appear as (§ (· τ* ...) ...)

;; =============================================================================
;; === Type->Expr maps

(define *log-dynamic-resolve* (make-parameter #t))
(define-syntax-rule (log-dynamic-resolve Σ arg*)
  (when (*log-dynamic-resolve*)
    (printf "[DYN.RESOLVE] numcases: ~a, arg: ~a\n" (Σ-count Σ) arg*)))

;; § is compile-time, Σ lives at runtime

(struct Σ (
  map
  ;; (Listof (Pairof (Listof (-> Any Boolean)) Expr))
  ;; maps type predicates to implementations
  ;; there's 1 predicate for each free variable

  posn**
  ;; (Listof (Listof Natural))
  ;; positions in the domain where free variables (for each type variable) appear
 ) #:transparent
   #:constructor-name make-Σ
   #:property prop:procedure
   (lambda (self . arg*)
     (log-dynamic-resolve self arg*)
     ;; Lookup finds a function, we apply this function to the lookup argument.
     ;; (Guess we could make this tail recursive)
     (define fn (Σ-lookup self arg*))
     (apply fn arg*)))

(define (Σ-add Σ τ* e)
  (make-Σ (cons (cons τ* e) (Σ-map Σ)) (Σ-posn** Σ)))

(define (Σ-count Σ)
  (length (Σ-map Σ)))

(define (Σ-init posn**)
  (make-Σ '() posn**))

(define (Σ-lookup Σ e*)
  (or
   (for/first ([τ*+e (in-list (Σ-map Σ))]
               #:when (for/and ([τ (in-list (car τ*+e))]
                                [posn* (in-list (Σ-posn** Σ))])
                        (andmap τ (positional-filter posn* e*))))
     (cdr τ*+e))
   (error 'Σ (format "Runtime type dispatch failed: no match for arguments '~a'" e*))))

;; Helper for Σ-lookup
(define (positional-filter posn* e*)
  (for/list ([e (in-list e*)] [i (in-naturals)]
             #:when (member i posn* =))  e))

;; -----------------------------------------------------------------------------

(begin-for-syntax
 (define (⟦Σ⟧-write ⟦Σ⟧ port mode)
   ;; Synthesize a §-type
   (define s ((current-type-eval) #`(§ #,@(map (lambda (τ*+e) #`(· #,@(car τ*+e)))
                                               (⟦Σ⟧-map ⟦Σ⟧)))))
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

 (define (⟦Σ⟧-add ⟦Σ⟧ τ* e)
   (make-⟦Σ⟧ (cons (cons τ* e) (⟦Σ⟧-map ⟦Σ⟧))))

 ;; Update the type τ with the new map Σ
 ;; TODO does not check "τ consistent with Σ"
 ;;      better to weave this into ⟦Σ⟧-add ?
 (define (⟦Σ⟧->type τ Σ)
   (syntax-parse τ
    [(~ψ A* _ τ)
     #`(ψ A* #,(assign-type #`#,Σ #'#%type) τ)]))

 ;; mem uses =?, and returns a boolean.
 ;; If this returns true, runtime lookups will succeed (even if compile-time fails)
 (define (⟦Σ⟧-mem? ⟦Σ⟧ τ* [τ<=? (current-type=?)])
   (for/or ([τ*+e (in-list (⟦Σ⟧-map ⟦Σ⟧))])
     (andmap τ<=? τ* (car τ*+e))))

 (define (⟦Σ⟧-init)
   (make-⟦Σ⟧ '()))

 (define (⟦Σ⟧-lookup ⟦Σ⟧ τ* [τ<=? (current-type=?)])
   (for/first ([τ*+e (in-list (⟦Σ⟧-map ⟦Σ⟧))]
               #:when (andmap τ<=? τ* (car τ*+e)))
     (cdr τ*+e)))

 ;; Check that all the types (keys) are the same
 (define (⟦Σ⟧=? τ=? ⟦Σ⟧1 ⟦Σ⟧2)
   ;; idk if τ=? should be a parameter or not
   (let loop ([τ1** (cannonize* (map car (⟦Σ⟧-map ⟦Σ⟧1)))]
              [τ2** (cannonize* (map car (⟦Σ⟧-map ⟦Σ⟧2)))])
     (cond
      [(and (null? τ1**) (null? τ2**))
       #t]
      [(and (not (null? τ1**)) (not (null? τ2**)))
       (and (andmap τ=? (car τ1**) (car τ2**))
            (loop (cdr τ1**) (cdr τ2**)))]
      [else
       #f])))

 ;; Reflect an list of types to a syntax map
 (define (τ**->⟦Σ⟧ τ**)
   (make-⟦Σ⟧ (for/list ([τ* (in-list (cannonize* τ**))])
               ;; Remove the · constructor before storing
               (syntax-parse τ*
                [(~· τ* ...)
                 (cons (syntax->list #'(τ* ...)) #f)]
                [(τ* ...)
                 (cons (syntax->list #'(τ* ...)) #f)]
                [τ
                 (cons (list #'τ) #f)]))))

 (define (⟦Σ⟧->τ** ⟦Σ⟧)
   (map car (⟦Σ⟧-map ⟦Σ⟧)))

)

;; =============================================================================

(begin-for-syntax ;; TODO put these in typecheck.rkt
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

 (define (cannonize* τ**)
   (define τ=? (current-type=?))
   (define (lift=? τ1* τ2*)
     (andmap τ=? τ1* τ2*))
   (define (lift<? τ1* τ2*)
     (andmap symbol<? τ1* τ2*))
   (define (lift->key τ*)
     (map τ->symbol τ*))
   (sort (remove-duplicates τ** lift=?)
         lift<?
         #:key lift->key))

 ;; True if one list of types is a prefix of another.
 (define (subset? x* y* #:leq [cmp (current-typecheck-relation)])
   (for/and ([x (in-list x*)])
     (for/or ([y (in-list y*)])
       (cmp x y))))
)

;; τ eval+equality
(begin-for-syntax
 (define ψ-eval
   (let ([τ-eval (current-type-eval)])
     (lambda (τ-stx)
       (syntax-parse (τ-eval τ-stx)
        [(~ψ (α* ...) (~§ (~· τ** ...) ...) τ_α)
         (define τ**+
           (for/list ([τ* (in-syntax #'((τ** ...) ...))])
             (when (or (stx-ormap §? τ*) (stx-ormap ·? τ*))
               (error 'ψ-eval (format "Recursive carrier '~a'" (syntax->datum #'((τ** ...) ...)))))
             (syntax->list τ*)))
         (τ-eval #`(ψ (α* ...) #,(assign-type #`#,(τ**->⟦Σ⟧ τ**+) #'#%type) τ_α))]
        [(~ψ (α* ...) (~§ τ* ...) τ_α)
         ;; Wrap everything in the · constructor
         (ψ-eval #`(ψ (α* ...) (§ #,@(stx-map (lambda (τ) #`(· #,τ)) #'(τ* ...))) τ_α))]
        ;; [(~ψ (α* ...) (~§) τ_α)
        ;;  (τ-eval #`(ψ (α* ...) #,(assign-type #`#,(
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

 ;; TODO doesn't belong here
 (define ∀-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1 τ2)
       (syntax-parse (list τ1 τ2)
        [((~∀ (x ...) t1)
          (~∀ (y ...) t2))
         (and (stx-length=? #'(x ...) #'(y ...))
              ((current-sub?) (substs #'(x ...) #'(x ...) #'t1)
                              (substs #'(x ...) #'(y ...) #'t2)))]
       [_
        (sub? τ1 τ2)]))))
 (current-sub? ∀-sub?)

 (define ψ-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1 τ2)
       (syntax-parse (list τ1 τ2)
        [((~ψ (A*:id ...)
              ⟦Σ⟧_A-stx
              τ_A)
          (~ψ (B*:id ...)
              ⟦Σ⟧_B-stx
              τ_B))
         (define ⟦Σ⟧_A (syntax->struct #'⟦Σ⟧_A-stx))
         (define ⟦Σ⟧_B (syntax->struct #'⟦Σ⟧_B-stx))
         (define lift-sub?
           (let ([sub? (current-sub?)])
             (lambda (τ1* τ2*)
               (andmap sub? τ1* τ2*))))
         ;; Compatible templates (also, same number of variables)
         (and ((current-sub?)
               ((current-type-eval) #'(∀ (A* ...) τ_A))
               ((current-type-eval) #'(∀ (B* ...) τ_B)))
              (subset? (⟦Σ⟧->τ** ⟦Σ⟧_B) (⟦Σ⟧->τ** ⟦Σ⟧_A) #:leq lift-sub?))]
        [_
         (sub? τ1 τ2)]))))

 (define (syntax->struct stx)
   (unless (syntax? stx)
     (error 'syntax->struct (format "expected a syntax object, got '~a'" stx)))
   (syntax-parse stx
    [(~§ (~· τ** ...) ...)
     (τ**->⟦Σ⟧ (for/list ([τ* (in-syntax #'((τ** ...) ...))])
                 (syntax->list τ*)))]
    [(~§ τ* ...)
     (τ**->⟦Σ⟧ (for/list ([τ (in-syntax #'(τ* ...))]) (list τ)))]
    [(_ e+)
     (syntax-e #'e+)]
    [_
     (error 'syntax->struct (format "could not handle ~a\n" stx))]))

 (current-type=? ψ=?)
 (current-sub? ψ-sub?)
 (current-typecheck-relation ψ-sub?)
)

;; =============================================================================

(begin-for-syntax

 (define-syntax-rule (error-template sym reason)
   (error sym reason))

 (define-syntax-rule (instance-error reason)
   (error-template 'instance reason))

 (define-syntax-rule (resolve-error τ reason)
   (error-template 'resolve (format "Cannot resolve at type '~a'. ~a"
                                    τ
                                    reason)))
 
 (define-syntax-rule (signature-error τ reason)
   (error 'signature (format "Cannot declare signature at type '~a'. ~a"
                             (syntax->datum τ)
                             reason)))

 (define-syntax-rule (unify-error reason)
   (error-template 'unify reason))
 
)

(define-typed-syntax signature
  [(_ (α*:id ...) τ)
   ;; Expand the type τ with α bound as a valid type
   #:with ((α+* ...) τ+ _) (infer/tyctx+erase #'([α* : #%type] ...) #'τ)
   ;; Collect domain positions where α appears
   (define α-posn**
     (syntax-parse #'τ+
      [(~→ τ_dom* ... τ_cod)
       (when (and (identifier? #'τ_cod)
                  (for/or ([α (in-syntax #'(α+* ...))])
                    (free-identifier=? #'τ_cod α)))
         (signature-error #'τ
                          (format "Codomain of '~a' cannot be a variable, for now." (syntax->datum #'τ))))
       ;; One of τ_dom MUST be the (expanded) identifier α+
       (for/list ([α (in-syntax #'(α+* ...))])
         (for/list ([τ_dom (in-syntax #'(τ_dom* ...))]
                    [i (in-naturals)]
                    #:when (and (identifier? τ_dom) (free-identifier=? τ_dom α)))
           i))]
      [_
       (signature-error #'τ (format "Cannot overload non-function '~a', for now." (syntax->datum #'τ)))]))
   (when (ormap null? α-posn**)
     (signature-error #'τ (format "All declared variables '~a' must appear in the domain of the signature type." (syntax->datum #'(α+* ...)))))
   (⊢ (Σ-init '#,α-posn**)
      : (ψ (α* ...) #,(assign-type #`#,(⟦Σ⟧-init) #'#%type) τ))])

(define-typed-syntax instance
  [(_ Σ e)
   #:with [Σ+ τ_Σ] (infer+erase #'Σ)
   #:with [e+ τ_e] (infer+erase #'e)
   ;; τ_Σ should be a ψ type
   ;; τ_e should be an arrow (for now, really it should match τ_α)
   (syntax-parse #'(τ_Σ τ_e)
    [((~ψ (α* ...) ⟦Σ⟧-stx (~→ τ_α* ... τ_cod_template))
      (~→ τ_dom* ... τ_cod_actual))
     ;; Unify the concrete domain against the template domain
     (define τ_new* (unify-dom #'(α* ...) #'(τ_α* ...) #'(τ_dom* ...)))
     ;; Assert τ_dom is new in the struct-dict
     (define ⟦Σ⟧ (syntax->struct #'⟦Σ⟧-stx))
     (when (⟦Σ⟧-mem? ⟦Σ⟧ τ_new*)
       (instance-error (format "Duplicate instance at type '~a'" (syntax->datum τ_new*))))
     ;; Unify codomains (just ignore τ_α for now)
     (unless ((current-typecheck-relation) #'τ_cod_actual #'τ_cod_template)
       (instance-error (format "Cannot unify '~a' with template '~a'"
                               (syntax->datum #'τ_e)
                               (syntax->datum #'τ_Σ))))
     (⊢ (Σ-add Σ+ (list #,@(map (current-Π) τ_new*)) e+)
        : #,(⟦Σ⟧->type #'τ_Σ (⟦Σ⟧-add ⟦Σ⟧ τ_new* #'e+)))]
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

;; TODO id-set?
(define-for-syntax (unify-dom α* τ_α* τ_dom*)
  (unless (= (stx-length τ_α*) (stx-length τ_dom*))
    (unify-error (format "Different length domains '~a' vs. '~a'" (syntax->datum τ_α*) (syntax->datum τ_dom*))))
  (for/list ([α (in-syntax α*)])
    (define (α=? τ)
      (and (identifier? τ) (free-identifier=? τ α)))
    (for/fold ([τ_new #f])
        ([τ_α (in-syntax τ_α*)]
         [τ_dom (in-syntax τ_dom*)]
         [arg-num (in-naturals)])
      (cond
       [(α=? τ_α)
        ;; Get the concrete type that replaces this variable; make sure all replacements agree
        (cond
         [(not τ_new)  τ_dom]
         [((current-typecheck-relation) τ_new τ_dom)  τ_dom]
         [((current-typecheck-relation) τ_dom τ_new)  τ_new]
         [else  (unify-error
                 (format "Incompatible types '~a' and '~a' used for variable '~a'."
                         (syntax->datum τ_new) (syntax->datum τ_dom) (syntax->datum τ_α)))])]
       [(and (identifier? τ_α) (for/or ([α (in-syntax α*)]) (free-identifier=? τ_α α)))
        ;; Skip other variables
        τ_new]
       [else
        ;; Make sure template and instance agree here
        ;; (We will replace τ_α with τ_dom, so they must be <: compatible.)
        (unless ((current-typecheck-relation) τ_α τ_dom)
          (unify-error (format "Type '~a' does not match signature '~a' (position ~a)"
                               (syntax->datum τ_dom) (syntax->datum τ_α) arg-num)))
        τ_new]))))

(define-for-syntax (resolve/internal e τ* τ<=?)
  (syntax-parse (infer+erase e)
   [(Σ (~ψ (α* ...) ⟦Σ⟧-stx τ_α))
    #:with (τ+* ...) (stx-map (current-type-eval) τ*)
    (define τ+*-list (syntax->list #'(τ+* ...)))
    (define ⟦Σ⟧ (syntax->struct #'⟦Σ⟧-stx))
    (unless (⟦Σ⟧-mem? ⟦Σ⟧ τ+*-list τ<=?)
      (resolve-error τ* "No matching instance."))
    ;; Try resolving statically, else use the actual term Σ as a dictionary
    (define f (or (⟦Σ⟧-lookup ⟦Σ⟧ τ+*-list τ<=?) #'Σ))
    (define τ/α (substs #'(τ+* ...) #'(α* ...) #'τ_α))
    (⊢ #,f : #,τ/α)]))

(define-typed-syntax resolve
  [(_ e τ* ...)
   (resolve/internal #'e #'(τ* ...) (current-type=?))])

;; Hijack application to typecheck
(define-typed-syntax app/tc #:export-as #%app
  [(_ e_1 e_2* ...)
   #:with (e_1+ τ_1+) (infer+erase #'e_1)
   #:when (ψ? #'τ_1+)
   ;; Destruct τ_1 to filter the overloading arguments from (e_2* ...)
   (syntax-parse #'τ_1+
    [(~ψ (α* ...) _ (~→ τ_dom* ... τ_cod))
     #:with ([e_2*+ τ_2*+] ...) (infers+erase #'(e_2* ...))
     (define τ_new* (unify-dom #'(α* ...) #'(τ_dom* ...) #'(τ_2*+ ...)))
     ;; Try resolving, then #%app like normal
     #`(stlc:#%app #,(resolve/internal #'e_1+ τ_new* (current-sub?)) e_2*+ ...)]
    [_ (error 'ψ-app (format "internal error parsing ~a" (syntax->datum #'(e_1 e_2* ...))))])]
  [(_ e* ...)
   #'(stlc:#%app e* ...)])
