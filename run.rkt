#lang racket
(require "lib.rkt")

(define (test)
  (define arr (make-array 3 3 0))
  (C arr [1 + 1] [1 - 1] = 1)
  (aupd! arr 0 1 sub1)
  (debugv arr))

(test)
