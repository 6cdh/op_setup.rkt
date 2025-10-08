#lang racket
(require "lib/syntax.rkt")
(require "lib/array.rkt")
(require "lib/utils.rkt")

(define (test)
  (define arr (make-array 3 3 0))
  (C arr [1 + 1] [1 - 1] = 1)
  (aupd! arr 0 1 sub1)
  (P arr))

(test)
