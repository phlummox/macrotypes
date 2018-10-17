#lang info

(define collection 'multi)

(define deps '(("base" #:version "7.0")))

(define build-deps
  '("scribble-lib"
    "sandbox-lib"
    ("turnstile-lib" #:version "0.3.1")))

(define pkg-desc "Documentation for \"Turnstile\".")
(define pkg-authors '(stchang))

(define version "0.3.1")