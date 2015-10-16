#lang s-exp "../stlc+occurrence.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; basic types & syntax

(check-type 1 : Int)
(check-type #f : Boolean)
(check-type "hello" : Str)
(check-type 1 : Top)
(check-type (λ ([x : (∪ Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))

(typecheck-fail
 (λ ([x : ∪]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (1 ∪)]) x)
 #:with-msg "")
(typecheck-fail
 (λ ([x : (Int ∪)]) x)
 #:with-msg "expected identifier")
(typecheck-fail
 (λ ([x : (→ ∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (→ Int ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪ Int →)]) x)
 #:with-msg "Improper usage of type constructor →: →, expected >= 1 arguments")

;; -----------------------------------------------------------------------------
;; --- type evaluation

(check-type (λ ([x : (∪ Int Int Int Int)]) x)
            : (→ Int Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ Boolean Int) Int))
(check-type (λ ([x : (∪ Int Boolean Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))
(check-type (λ ([x : (∪ (∪ Int Boolean))]) 42)
            : (→ (∪ Int Boolean) Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ (∪ Int Boolean)) Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ (∪ Int Boolean) (∪ Int Boolean)) Int))


;; -----------------------------------------------------------------------------
;; --- subtyping

;; ---- basics
(check-type 1 : (∪ Int))
(check-type 1 : (∪ (∪ Int)))
(check-type (λ ([x : Int]) x)
            : (→ Bot Top))

(check-not-type 1 : (∪ Boolean))

;; - AMB : t <: t' => t <: (U ... t' ...)
(check-type 1 : (∪ Boolean Int))
(check-type -1 : (∪ Int Boolean))
(check-type 1 : (∪ Boolean Int (→ Boolean Boolean)))
(check-type 1 : (∪ (∪ Int Boolean) (∪ Int Boolean)))

(check-not-type 1 : (∪ Boolean (→ Int Int)))

;; --- EXT : (U t' ...) <: (U t t' ...)
(check-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Int Boolean) (∪ Int Boolean Str)))
(check-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Boolean) (∪ Int Boolean Str)))

(check-not-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Int Boolean) (∪ Int)))
(check-not-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Boolean Int Str) (∪ Int Boolean)))

;; --- SUB : a<:b => (U a t' ...) <: (U b t' ...)
(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Int Str) (∪ Num Str)))
(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Nat Str) (∪ Num Str)))

(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Int Str) Top))

(check-not-type (λ ([x : (∪ Int Str)]) x)
            : (→ Top (∪ Num Str)))

;; --- ALL
(check-type (λ ([x : (∪ Boolean Int Str)]) x)
            : (→ (∪ Boolean Int Str) Top))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ (∪ Nat Int Num) Num))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ Nat Num))

;; --- misc
;; Because Int<:(U Int ...)
(check-type (λ ([x : (∪ Int Nat)]) #t)
                  : (→ Int Boolean))

;; -----------------------------------------------------------------------------
;; --- Basic Filters (applying functions)

;; --- is-boolean?
(check-type
 (λ ([x : (∪ Boolean Int)])
    (test [Boolean ? x]
          #t
          #f))
 : (→ (∪ Boolean Int) Boolean))
(check-type-and-result
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) #t)
  : Boolean ⇒ #t)
(check-type-and-result
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) 902)
  : Boolean ⇒ #f)

;; --- successor
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0))
 : (→ (∪ Int Boolean) (∪ Num Nat)))
(check-type-and-result
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0)) #f)
 : Num ⇒ 0)
(check-type-and-result
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          1)) #t)
 : Num ⇒ 1)
(check-type-and-result
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0)) 9000)
 : Num ⇒ 9001)

;; ;; --- Do-nothing filter
(check-type
 (λ ([x : Int])
    (test (Int ? x) #t #f))
 : (→ Int Boolean))
(check-type
 (λ ([x : Int])
    (test (Boolean ? x) 0 x))
 : (→ Int (∪ Nat Int)))

;; --- Filter a subtype
(check-type
 (λ ([x : (∪ Nat Boolean)])
    (test (Int ? x)
          x
          x))
 : (→ (∪ Nat Boolean) (∪ Int (∪ Nat Boolean))))

(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Nat ? x)
          x
          x))
 : (→ (∪ Boolean Int) (∪ Int Nat Boolean)))

;; --- Filter a supertype
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Num ? x)
          1
          x))
 : (→ (∪ Boolean Int) (∪ Nat Boolean)))

(check-type-and-result
 ((λ ([x : (∪ Int Boolean)])
     (test (Num ? x)
           #f
           x)) #t)
 : Boolean
 ⇒ #t)

;; Should filter all the impossible types 
(check-type-and-result
 ((λ ([x : (∪ Nat Int Num Boolean)])
     (test (Num ? x)
           #f
           x)) #t)
 : Boolean
 ⇒ #t)

;; ----------------------------------------------------------------------------- 
;; --- misc subtyping + filters (regression tests)
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Boolean) Nat))
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Boolean) Int))

;; -----------------------------------------------------------------------------
;; --- Invalid filters

(typecheck-fail
 (λ ([x : (∪ Int Boolean)])
    (test (1 ? x) #t #f))
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (#f ? #t) #t #f)
 #:with-msg "not a valid type")

;; -----------------------------------------------------------------------------
;; --- Subtypes should not be collapsed

(check-not-type (λ ([x : (∪ Int Nat)]) #t)
                : (→ Num Boolean))
(check-type ((λ ([x : (∪ Int Nat Boolean)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             #t)
            : Nat ⇒ 0)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Nat ? x)
                      1
                      (test (Int ? x)
                            2
                            0)))
             1)
            : Nat ⇒ 1)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             -10)
            : Nat ⇒ 2)
               
;; -----------------------------------------------------------------------------
;; --- Functions in union

(check-type (λ ([x : (∪ Int (∪ Nat) (∪ (→ Int Str Int)) (→ (→ (→ Int Int)) Int))]) #t)
            : (→ (∪ Int Nat (→ Int Str Int) (→ (→ (→ Int Int)) Int)) Boolean))

(check-type (λ ([x : (∪ Int (→ Int Int))]) #t)
            : (→ Int Boolean))

;; --- filter functions
(check-type
 (λ ([x : (∪ Int (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
          x))
 : (→ (∪ Int (→ Int Int)) Int))

(check-type
 (λ ([x : (∪ (→ Int Int Int) (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0))))
 : (→ (∪ (→ Int Int Int) (→ Int Int)) Int))

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) 1)
 : Int ⇒ 1)

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int]) 5))
 : Int ⇒ 5)

(check-type-and-result
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int] [z : Int]) z))
 : Int ⇒ 0)

;; -----------------------------------------------------------------------------
;; --- Filter with unions

(check-type
 (λ ([x : (∪ Int Str)])
  (test ((∪ Int Str) ? x)
        x
        "nope"))
 : (→ (∪ Int Str) (∪ Int Str)))

(check-type
 (λ ([x : (∪ Int Str Boolean)])
    (test ((∪ Int Str) ? x)
          x
          "Nope"))
 : (→ (∪ Int Str Boolean) (∪ Int Str)))

(check-type
 (λ ([x : (∪ Int Str Boolean)])
    (test ((∪ Int Str) ? x)
          (test (Str ? x)
                "yes"
                "int")
          "bool"))
 : (→ (∪ Int Str Boolean) Str))

(check-type-and-result
 ((λ ([x : (∪ Str Boolean)])
     (test ((∪ Int Nat Num) ? x)
           x
           (+ 1 2))) "hi")
 : Num ⇒ 3)

(check-type-and-result
  ((λ ([x : (∪ Str Int Boolean)])
      (test ((∪ Int Str) ? x)
            x
            "error")) 1)
  : (∪ Str Int) ⇒ 1)

(check-type-and-result
  ((λ ([x : (∪ Str Int Boolean)])
      (test ((∪ Int Str) ? x)
            x
            "error")) "hi")
  : (∪ Int Str) ⇒ "hi")

;; -----------------------------------------------------------------------------
;; --- CPS filters

(check-type (λ ([x : Int]) x)
            : (∪ (→ Int Int) (→ Str Str)))

(check-type
 (λ ([x : (∪ (→ Int Str) (→ Str Str))])
    (test ((→ Int Str) ? x)
          (x 42)
          (x "hello")))
 : (→ (∪ (→ Int Str) (→ Str Str)) Str))

(check-type-and-result
 ((λ ([x : (∪ (→ Int Str) (→ Str Str))])
    (test ((→ Int Str) ? x)
          (x 42)
          "booo")) (λ ([x : Int]) "int"))
 : Str ⇒ "int")

(check-type-and-result
 ((λ ([x : (∪ (→ Int Str) (→ Str Str))])
    (test ((→ Int Str) ? x)
          (x 42)
          "success")) (λ ([x : Str]) x))
 : Str ⇒ "success")

(check-type-and-result
 ((λ ([x : (∪ (→ Boolean Num) (→ Int Num))])
    (test ((→ Boolean Num) ? x)
          (x #t)
          (x 0))) (λ ([y : Int]) (+ y 42)))
 : Num ⇒ 42)

;; ;; PROBLEMOS (these are keeping the CPS filters out of the limelight)
;; (check-type-and-result
;;  ((λ ([x : (∪ (→ Int Str) (→ Str Str))])
;;     (test ((→ Int Str) ? x)
;;           (x 42)
;;           "success")) (λ ([x : Str]) "uncaught type error"))
;;  : Str ⇒ "success")

;; (check-type-and-result
;;  ((λ ([x : (∪ (→ Int Str) (→ Str Str))])
;;     (test ((→ Int Str) ? x)
;;           "uncaught type error"
;;           "success")) (λ ([x : Str]) x))
;;  : Str ⇒ "success")

;; -----------------------------------------------------------------------------
;; --- TODO Filter on values (should do nothing)

;; (check-type
;;  (test (Int ? 1) #t #f)
;;  : Boolean)

;; -----------------------------------------------------------------------------
;; --- TODO Values as filters (check equality)

;; -----------------------------------------------------------------------------
;; --- TODO Latent filters (on data structures)

