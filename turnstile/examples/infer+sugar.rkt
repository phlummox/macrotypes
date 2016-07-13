#lang turnstile
(extends "infer.rkt")
(require "infer.rkt")

(define-typed-syntax list
  [(list) ≫
   --------
   [_ ≻ empty]]
  [(list a:expr b:expr ...) ≫
   --------
   [_ ≻ (cons a (list b ...))]])

(define-typed-syntax let*
  [(let* () body:expr) ≫
   --------
   [_ ≻ body]]
  [(let* ([x:id v:expr] [y:id w:expr] ...) body:expr) ≫
   --------
   [_ ≻ (let ([x v]) (let* ([y w] ...) body))]])

(define-typed-syntax do #:datum-literals (->)
  [(do bind:id body:expr) ≫
   --------
   [_ ≻ body]]
  [(do bind:id [x:id <- v:expr] . rst) ≫
   --------
   [_ ≻ (bind
         v
         (λ (x)
           (do bind . rst)))]]
  [(do bind:id [v:expr] . rst) ≫
   --------
   [_ ≻ (bind
         v
         (λ (dummy)
           (do bind . rst)))]])

(define-typed-syntax begin
  [(begin e:expr ... e_body:expr) ≫
   [#:with [x ...] (generate-temporaries #'[e ...])]
   --------
   [_ ≻ (let ([x e] ...) e_body)]])

