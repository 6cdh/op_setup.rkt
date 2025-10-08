#lang racket

(provide (all-defined-out))

(require data/splay-tree)

(define splay-tree-update!
  (case-lambda
    [(sl key fn)
     (splay-tree-set! sl key
                      (fn (splay-tree-ref sl key)))]
    [(sl key fn default)
     (splay-tree-set! sl key
                      (fn (splay-tree-ref sl key default)))]))

