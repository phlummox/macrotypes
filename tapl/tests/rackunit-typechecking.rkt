#lang racket/base
(require (for-syntax rackunit syntax/srcloc) rackunit "../typecheck.rkt")
(provide check-type typecheck-fail check-not-type check-props check-runtime-exn)

(begin-for-syntax
  (define (add-esc s) (string-append "\\" s))
  (define escs (map add-esc '("(" ")" "[" "]")))
  (define (replace-brackets str)
    (regexp-replace* "\\]" (regexp-replace* "\\[" str "(") ")"))
  (define (add-escs str)
    (replace-brackets
        (foldl (lambda (c s) (regexp-replace* c s (add-esc c))) str escs)))
  (define (expected tys #:given [givens ""] #:note [note ""])
    (string-append  
     note ".*Expected.+argument\\(s\\) with type\\(s\\).+" 
     (add-escs tys) ".*Given:.*" 
     (string-join (map add-escs (string-split givens ", ")) ".*"))))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (: ⇒ ->)
    ;; duplicate code to avoid redundant expansions
    [(_ e : τ-expected (~or ⇒ ->) v)
     #:with e+ (expand/df #'(add-expected e τ-expected))
     #:with τ (typeof #'e+)
     #:fail-unless (typecheck? #'τ ((current-type-eval) #'τ-expected))
                   (format
                    "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
                    (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
                    (type->str #'τ) (type->str #'τ-expected))
     (syntax/loc stx (check-equal? e+ (add-expected v τ-expected)))]
    [(_ e : τ-expected)
     #:with τ (typeof (expand/df #'(add-expected e τ-expected)))
     ;; #:when (pretty-print (syntax->datum #'τ))
     ;; #:when (pretty-print (syntax->datum ((current-type-eval) #'τ-expected)))
     #:fail-unless
     (typecheck? #'τ ((current-type-eval) #'τ-expected))
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (type->str #'τ) (type->str #'τ-expected))
     #'(void)]))

;; for checking properties other than types
(define-syntax (check-props stx)
  (syntax-parse stx #:datum-literals (: ⇒ ->)
    [(_ prop e : v ... (~optional (~seq (~or ⇒ ->) v2) #:defaults ([v2 #'e])))
     #:with props (or (syntax-property (expand/df #'e) (syntax->datum #'prop))
                      #'())
     #:fail-unless (set=? (apply set (syntax->datum #'(v ...)))
                          (apply set (syntax->datum #'props)))
     (format
      "Expression ~a [loc ~a:~a:~a] does not have prop ~a, actual: ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e) (syntax-position #'e)
      (syntax->datum #'(v ...)) (syntax->datum #'props))
     (syntax/loc stx (check-equal? e v2))]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : not-τ)
     #:with τ (typeof (expand/df #'e))
     #:fail-when
     (typecheck? #'τ ((current-type-eval) #'not-τ))
     (format
      "(~a:~a) Expression ~a has type ~a; should not typecheck with ~a"
      (syntax-line stx) (syntax-column stx)
      (syntax->datum #'e) (type->str #'τ) (type->str #'not-τ))
     #'(void)]))

(define-syntax (typecheck-fail stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e (~optional (~seq #:with-msg msg-pat) #:defaults ([msg-pat #'""])))
     #:with msg:str 
            (eval-syntax (datum->syntax #'here (syntax->datum #'msg-pat)))
     #:when (with-check-info*
             (list (make-check-location (build-source-location-list stx)))
             (λ ()
               (check-exn
                (λ (ex) (or (exn:fail? ex) (exn:test:check? ex)))
                (λ ()
                  (with-handlers
                      ; check err msg matches
                      ([exn:fail?
                        (λ (ex)
                          (unless (regexp-match? (syntax-e #'msg) (exn-message ex))
                            (printf
                             (string-append
                              "ERROR-MSG ERROR: wrong err msg produced by expression ~v:\n"
                              "EXPECTED:\nmsg matching pattern ~v,\nGOT:\n~v\n")
                             (syntax->datum #'e) (syntax-e #'msg) (exn-message ex)))
                          (raise ex))])
                    (expand/df #'e)))
                (format
                 "Expected type check failure but expression ~a has valid type, OR wrong err msg received."
                 (syntax->datum #'e)))))
     #'(void)]))

(define-syntax (check-runtime-exn stx)
  (syntax-parse stx
    [(_ e)
     #:with e- (expand/df #'e)
     (syntax/loc stx (check-exn exn:fail? (lambda () e-)))]))
