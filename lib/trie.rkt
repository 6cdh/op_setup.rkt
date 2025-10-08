#lang racket

(provide (all-defined-out))

(require "utils.rkt")

;; Trie ;;

;; only for lowercase characters

(define (make-trie)
  (make-vector 26 #f))

(define (trie-add! alphabet str)
  (for/fold ([ab (in-vector alphabet)])
            ([c (in-string str)])
    (define x (lower-char->integer c))
    (when (false? (vector-ref ab x))
      (vector-set! ab x (make-trie)))
    (vector-ref ab x)))

(define (trie-longest-prefix-len trie str [start 0] [end (string-length str)])
  (define ab trie)
  (define unmatch-idx
    (or (for*/first ([i (in-range start end)]
                     [x (in-value (lower-char->integer (string-ref str i)))]
                     #:when (let ()
                              (set! ab (vector-ref ab x))
                              (false? ab)))
          i)
        end))
  (- unmatch-idx start))

