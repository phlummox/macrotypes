#lang s-exp "../stlc+oo.rkt"
(require "rackunit-typechecking.rkt")

(signature (to-string α) (→ α String))

;; -- overload at union type

(instance (to-string (∪ Int String))
          (λ ([x : (∪ Int String)])
             (test (Int ? x)
                   "int"
                   "str")))

(check-type-and-result
 (to-string 42)
 : String ⇒ "int")

(check-type-and-result
 (to-string "hello")
 : String ⇒ "str")

(check-type-and-result
 ((λ ([x : (∪ String Int)])
     (to-string x))
  1)
 : String ⇒ "int")

(check-type-and-result
 ((λ ([x : (∪ String Int)])
     (to-string x))
  "two")
 : String ⇒ "str")

;; -- 
