#lang racket

(provide (all-defined-out))

(define bs<< arithmetic-shift)
(define bs& bitwise-and)
(define bs|| bitwise-ior)
(define bs! bitwise-not)
(define bs-has? bitwise-bit-set?)
(define bs^ bitwise-xor)

(define (bs-set-lowest-zero-to-one x)
  (bitwise-ior x (add1 x)))

(define (bs-set-highest-one-to-zero x)
  (bitwise-and x (sub1 x)))

;; is `bitset` a subset of `bits`?
;; bs-subset? : (integer, integer) -> boolean
(define (bs-subset? bits bitset)
  (= bitset (bitwise-ior bits bitset)))

(define (bs-count-ones num)
  (if (= num 0)
      0
      (add1 (bs-count-ones (bitwise-and num (sub1 num))))))

;; BitSet ;;

;; a simple abstraction of a bitset of a list.

;; full-bitset
;; a full bitset of size n
(define (full-bitset n)
  (sub1 (expt 2 n)))

;; empty-bitset
;; an empty bitset
(define (empty-bitset)
  0)

(define (bitset-has? bits index)
  (positive? (bitwise-and bits (expt 2 index))))

(define (bitset-empty? bits)
  (zero? bits))

(define (bitset-full? bs bits)
  (= bits bs))

(define (bitset-add bits index)
  (bitwise-ior bits (expt 2 index)))

(define (bitset-remove bits index)
  (bitwise-and bits (bitwise-not (expt 2 index))))

(define (bitset-count bits)
  (if (zero? bits)
      0
      (add1 (bitset-count (bitwise-and bits (sub1 bits))))))

(define (bitset-union bits1 bits2)
  (bitwise-ior bits1 bits2))

(define (bitset-intersect bits1 bits2)
  (bitwise-and bits1 bits2))

(define (bitset-subtract bits1 bits2)
  (bitwise-xor bits1 (bitset-intersect bits1 bits2)))

