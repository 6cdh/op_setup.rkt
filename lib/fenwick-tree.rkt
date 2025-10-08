#lang racket

(provide (all-defined-out))

(require "array.rkt")
(require "bitwise.rkt")

;; Fenwick Tree ;;

; Fenwick tree provides a vector abstraction, and
; O(log n) range sum query
; O(log n) update

;; make a fenwick tree with (inclusive-range 0 n)
;; O(n)
(define (make-fenwick-tree n)
  (make-vector n 0))

;; fenwick-tree[i] += delta
;; O(log n)
(define (ft-add! fenwick-tree i delta)
  (let loop ([i i])
    (when (< i (vector-length fenwick-tree))
      (aupd! fenwick-tree i (λ (x) (+ x delta)))
      (loop (bs-set-lowest-zero-to-one i)))))

;; query the sum of (inclusive-range i j)
;; O(log n)
(define (ft-sum fenwick-tree i j)
  (let loop ([sum 0]
             [i i]
             [j j])
    (cond [(> j i)
           (loop (+ sum (aref fenwick-tree (sub1 j)))
                 i
                 (bs-set-highest-one-to-zero j))]
          [(> i j)
           (loop (- sum (aref fenwick-tree (sub1 i)))
                 (bs-set-highest-one-to-zero i)
                 j)]
          [else sum])))

