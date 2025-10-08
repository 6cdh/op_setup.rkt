#lang racket

(provide (all-defined-out))

(require data/heap)
(require "heap.rkt")

(define (make-graph)
  (make-hash))

(define (graph-add-dir-edge! g from to)
  (hash-update! g from (λ (old) (cons to old)) '()))

(define (graph-add-dir-weight-edge! g from to weight)
  (hash-update! g from (λ (old) (cons (cons to weight) old)) '()))

(define (graph-add-undir-edge! g u v)
  (graph-add-dir-edge! g u v)
  (graph-add-dir-edge! g v u))

(define (graph-add-undir-weight-edge! g u v w)
  (graph-add-dir-weight-edge! g u v w)
  (graph-add-dir-weight-edge! g v u w))

;; build graph

(define (undir-edges->graph edges)
  (define g (make-graph))
  (for ([e edges])
    (match e
      [(list u v) (graph-add-undir-edge! g u v)]))
  g)

(define (undir-weight-edges->graph edges)
  (define g (make-graph))
  (for ([e edges])
    (match e
      [(list u v w) (graph-add-undir-weight-edge! g u v w)]))
  g)

(define (dir-edges->graph edges)
  (define g (make-hash))
  (for ([e edges])
    (match e
      [(list u v) (graph-add-dir-edge! g u v)]))
  g)

(define (dir-weight-edges->graph edges)
  (define g (make-hash))
  (for ([e edges])
    (match e
      [(list u v w) (graph-add-dir-weight-edge! g u v w)]))
  g)

(define (undir-edges->tree edges root from)
  (define g (undir-edges->graph edges))
  (define tree-edges '())

  (define (go root from)
    (for ([c (in-list (hash-ref g root '()))]
          #:when (not (equal? c from)))
      (set! tree-edges (cons (list root c) tree-edges))
      (go c root)))

  (go root from)
  (dir-edges->graph tree-edges))

;; dijkstra algorithm
;; solve single source shortest path problem
;; return the shortest distance hash table and
;; the previous node hash table
; graph/dijkstra : (node, edgeof) -> (list dist prev)
; edgeof : (node, cost) -> (listof (cons node cost))
; node : any
; cost : non-negative number
; dist : (hash node cost)
; prev : (hash node node)
(define (graph/dijkstra s edgeof)
  (define dist (make-hash))
  (define prev (make-hash))

  (define (rec h)
    (cond [(heap-empty? h)
           (list dist prev)]
          [else
           (match-define (cons closest d) (heap-min h))
           (heap-remove-min! h)
           (for ([edge (in-list (edgeof closest d))])
             (match-define (cons to cost) edge)
             (define d1 (+ d cost))
             (when (or (not (hash-has-key? dist to))
                       (< d1 (hash-ref dist to)))
               (hash-set! dist to d1)
               (hash-set! prev to closest)
               (heap-add! h (cons to d1))))

           (rec h)]))

  (define h (make-heap (λ (a b) (<= (cdr a) (cdr b)))))
  (heap-add! h (cons s 0))
  (hash-set! dist s 0)
  (rec h))

;; find the shortest path from `s` to `t` and cost
; graph/shortest : (node, node, edgeof) -> (list path cost)
; edgeof : node -> (listof (cons node cost))
; node : any
; cost : non-negative number
; path : (and (listof node) (= s (first path)) (= t (last path)))
(define (graph/shortest s t edgeof)
  (match-define (list dist prev) (graph/dijkstra s edgeof))

  (define (build-path path)
    (define node (first path))
    (cond [(= node s) path]
          [else (build-path (cons (hash-ref prev node) path))]))

  (list (build-path (list t)) (hash-ref dist t)))

(define (bfs starts edgeof)
  (define dist (make-hash))

  (define (loop nodes steps)
    (define new-nodes
      (for*/list ([node nodes]
                  [nei (edgeof node steps)]
                  #:when (not (hash-has-key? dist nei)))
        (hash-set! dist nei (add1 steps))
        nei))

    (when (not (null? new-nodes))
      (loop new-nodes (add1 steps))))

  (loop starts 0)
  dist)

