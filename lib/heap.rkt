#lang racket

(provide (all-defined-out))

(require data/heap)
(require "counter.rkt")

;; utils for heap

; heap-max is the same as heap-min.
; When you know the heap is a max-heap, use heap-max.
(define heap-max heap-min)
(define heap-remove-max! heap-remove-min!)

(define (heap-empty? h)
  (= 0 (heap-count h)))

;; Lazy Heap ;;

;; provide O(log n) lazy delete compared normal heap O(n) delete.

(struct LazyHeap
  [deleted heap])

(define (make-lazyheap <=)
  (LazyHeap (make-hash) (make-heap <=)))

(define (lazyheap-add! lh x)
  (heap-add! (LazyHeap-heap lh) x))

(define (lazyheap-delete! lh x)
  (counter-add! (LazyHeap-deleted lh) x))

(define (lazyheap-min lh)
  (match-define (LazyHeap deleted heap) lh)
  (let loop ()
    (define minv (heap-min heap))
    (cond [(hash-has-key? deleted minv)
           (counter-remove! deleted minv)
           (heap-remove-min! heap)
           (loop)]
          [else minv])))

(define (lazyheap-remove-min! lh)
  (lazyheap-min lh)
  (heap-remove-min! (LazyHeap-heap lh)))

