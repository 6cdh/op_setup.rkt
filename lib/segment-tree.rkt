#lang racket

(provide (all-defined-out))

(require "array.rkt")
(require "tree.rkt")

;; Segment Tree ;;

;; Segment Tree provide a vector abstraction, and
;; O(log n) range sum query
;; O(log n) update

;; It also allows a custom operation to be provided
;; instead of maximum, minimum, etc.

;; the lowest layer of the segment tree is the minimum power of 2
;; that is not less than `len`

(struct SegmentTree
  (vec size op))

;; O(len)
(define (make-segtree len init op)
  (let ([n (max 2 (expt 2 (exact-ceiling (log len 2))))])
    (SegmentTree (make-vector (* 2 n) init) n op)))

;; O(1)
(define (segtree-ref segtree i)
  (match-let ([(SegmentTree tree n op) segtree])
    (aref tree (+ i n))))

;; O(log n)
(define (segtree-query segtree left right)
  (match-let ([(SegmentTree tree n op) segtree])
    (let loop ([l (+ left n)] [r (+ right n)] [result (aref tree 0)])
      (cond [(> l r) result]
            [(odd? l) (loop (add1 l) r (op result (aref tree l)))]
            [(even? r) (loop l (sub1 r) (op result (aref tree r)))]
            [else (loop (tree1-father l) (tree1-father r) result)]))))

;; O(log n)
(define (segtree-set! segtree key newv)
  (match-let ([(SegmentTree tree n op) segtree])
    (aset! tree (+ key n) newv)

    (let loop ([k (tree1-father (+ key n))])
      (when (>= k 1)
        (aset! tree k
               (op (aref tree (tree1-left k))
                   (aref tree (tree1-right k))))
        (loop (tree1-father k))))))

