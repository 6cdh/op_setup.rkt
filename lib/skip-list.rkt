#lang racket

(provide (all-defined-out))

(require data/skip-list)

;; ** Skip List

(define skip-list-update!
  (case-lambda
    [(sl key fn)
     (skip-list-set! sl key
                     (fn (skip-list-ref sl key)))]
    [(sl key fn default)
     (skip-list-set! sl key
                     (fn (skip-list-ref sl key default)))]))

;; return a list of keys in (inclusive-range beg end)
(define (skip-list-range sl beg end)
  (let loop ([lst '()]
             [it (skip-list-iterate-least/>=? sl beg)])
    (cond [(not it) lst]
          [(> (skip-list-iterate-key sl it) end) lst]
          [else (loop (cons (skip-list-iterate-key sl it) lst)
                      (skip-list-iterate-next sl it))])))

