#lang racket

(provide (all-defined-out))

;; Counter ;;

;; convert a sequence that can iterate with `for` to hash table counter
(define (sequence->counter seq)
  (for/fold ([h (make-hash)])
            ([v seq])
    (counter-add! h v)
    h))

(define (make-counter [seq #f])
  (if (false? seq)
      (make-hash)
      (sequence->counter seq)))

(define (counter-ref cter val)
  (hash-ref cter val 0))

(define (counter-add! cter val)
  (hash-update! cter val add1 0))

(define (counter-remove! cter val)
  (hash-update! cter val sub1)
  (when (= 0 (hash-ref cter val))
    (hash-remove! cter val)))

