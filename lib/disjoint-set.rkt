#lang racket

(provide (all-defined-out))

(require "array.rkt")

;; Disjoint Set ;;

;; Initially, every element is in its own set.

;; make disjoint set of (inclusive-range 0 n)
;; O(n)
(define (make-dsu n)
  (build-vector n values))

;; dsu-rootof
;; query the root of the set of a given element or which set it belongs to.
;; almost constant complexity
(define (dsu-rootof dsu x)
  (match (aref dsu x)
    [(== x) x]
    [fa (let ([r (dsu-rootof dsu fa)])
          (aset! dsu x r)
          r)]))

;; dsu-union!
;; merge two set into a larger set.
;; almost constant complexity
(define (dsu-union! dsu a b)
  (aset! dsu (dsu-rootof dsu a) (dsu-rootof dsu b)))

