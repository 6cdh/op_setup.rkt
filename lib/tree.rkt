#lang racket

(provide (all-defined-out))

(require "array.rkt")
(require "syntax.rkt")
(require "utils.rkt")

(struct Tree-Info
  [size
   root
   depth-of
   parent-of
   children-of])

(define (tree-traverse children root)
  (define size 1)
  (for ([(_ adjs) (in-hash children)])
    (set! size (+ size (length adjs))))

  (define depths (make-vector (+ size 1) 0))
  (define parents (make-vector (+ size 1) root))

  (define (traverse node depth)
    (aset! depths node depth)
    (for ([child (in-list (hash-ref children node '()))])
      (aset! parents child node)
      (traverse child (add1 depth))))

  (traverse root 0)
  (Tree-Info
    size
    root
    (λ (x) (aref depths x))
    (λ (x) (aref parents x))
    (λ (x) (hash-ref children x '()))))

(define (precompute-lca tree-info)
  (define n (Tree-Info-size tree-info))
  (define parent-of (Tree-Info-parent-of tree-info))
  (define depth-of (Tree-Info-depth-of tree-info))
  (define limit (exact-ceiling (log n 2)))

  ;; steps-th ancestor of node `u`
  (define (up u steps)
    (for/fold ([u u])
              ([i (in-range limit)]
               #:when (bitwise-bit-set? steps i))
      (up-p2 u i)))

  ;; (2^steps)-th ancestor of node `u`
  (define/cache-vec (up-p2 u steps)
                    ((add1 n) limit #f)
                    (values u steps)
    (if (= steps 0)
        (parent-of u)
        (up-p2 (up-p2 u (sub1 steps)) (sub1 steps))))

  (define (lca-of/same-depth u v)
    (for/fold ([u u]
               [v v]
               #:result (up-p2 u 0))
              ([steps (in-reverse-range 0 limit)])
      (define ua (up-p2 u steps))
      (define va (up-p2 v steps))
      (if (not (= ua va))
          (values ua va)
          (values u v))))

  (define (lca-of u v)
    (define du (depth-of u))
    (define dv (depth-of v))
    (cond [(< du dv)
           (lca-of v u)]
          [else
           (define diff (- du dv))
           (define ua (up u diff))
           (if (= ua v)
               ua
               (lca-of/same-depth ua v))]))

  lca-of)

;; Utils for array representation of Binary Tree ;;

; root is 1

(define (tree1-father k)
  (quotient k 2))

(define (tree1-left k)
  (* 2 k))

(define (tree1-right k)
  (add1 (* 2 k)))

(define (tree1-sibling k)
  (bitwise-xor k 1))

; root is 0

(define (tree0-father k)
  (quotient (sub1 k) 2))

(define (tree0-left k)
  (+ (* 2 k) 1))

(define (tree0-right k)
  (+ (* 2 k) 2))

