#lang racket

(provide (all-defined-out))

(require "list.rkt")

;; Multidimensional Array ;;

;; make a multi-dimension array
;; (make-array dims ... init)
(define-syntax make-array
  (syntax-rules ()
    [(_ n init)
     (build-vector n (λ _ init))]
    [(_ n args ...)
     (build-vector n (λ _ (make-array args ...)))]))

;; array-ref
;; (aref array dims ...)
(define-syntax aref
  (syntax-rules ()
    [(_ arr) arr]
    [(_ arr i dims ...)
     (aref (vector-ref arr i) dims ...)]))

;; array-set!
;; (aset! array dims ... new-value)
(define-syntax aset!
  (syntax-rules ()
    [(_ arr dim new-val)
     (vector-set! arr dim new-val)]
    [(_ arr dim1 dims ... new-val)
     (aset! (vector-ref arr dim1) dims ... new-val)]))

;; array-update!
;; (aupd! array dims ... updater)
;; updater : T -> T
(define-syntax-rule (aupd! arr dims ... updater)
  (aset! arr dims ... (updater (aref arr dims ...))))

;; array-swap!
;; (aswap! array (dims1 ...) (dims2 ...))
(define-syntax-rule (aswap! arr (dims1 ...) (dims2 ...))
  (let ([t (aref arr dims1 ...)])
    (aset! arr dims1 ... (aref arr dims2 ...))
    (aset! arr dims2 ... t)))

;; vector-expand
;; Expand a vector to a new size, and return the new expanded vector.
;; It does not modify the old vector.
(define (vector-expand vec size init)
  (define (expand-strategy old-size wanted-size)
    (max wanted-size (+ 2 (* 2 old-size))))

  (define new-size (expand-strategy (vector-length vec) size))
  (let ([new-vec (make-vector new-size init)])
    (vector-copy! new-vec 0 vec)
    new-vec))

;; vector-try-expand
;; If the vector does not have enough elements,
;; expand it and return the expanded vector.
;; Otherwise, return the original vector.
(define (vector-try-expand arr dim init)
  (if (>= dim (vector-length arr))
      (vector-expand arr (add1 dim) init)
      arr))

;; array-can-ref?
;; (array-can-ref? array dims ...)
;; If dims ... are valid references in array, return true.
(define-syntax array-can-ref?
  (syntax-rules ()
    [(_ arr dim)
     (< dim (vector-length arr))]
    [(_ arr dim1 dims ...)
     (let ([dim1v dim1])
       (and (< dim1v (vector-length arr))
            (array-can-ref? (vector-ref arr dim1v) dims ...)))]))

;; array-expand!
;; (aexpand! array dims ... init)
;; If dims ... are not valid references (too large) in array,
;; expand array to make them valid, and return the new expanded array.
;; Otherwise, return the original array.
(define-syntax aexpand!
  (syntax-rules ()
    [(_ arr dim init)
     (vector-try-expand arr dim init)]
    [(_ arr dim1 dims ... init)
     (let* ([dim1v dim1]
            [new-vec (vector-try-expand arr dim1v #())])
       (vector-set! new-vec dim1v (aexpand! (vector-ref new-vec dim1v) dims ... init))
       new-vec)]))

;; Flattened Multidimensional Array ;;

(struct FlatArray
  (vec ds))

(define (flat-array/args->index fa dims)
  (for/sum ([d (in-vector dims)]
            [w (in-list (FlatArray-ds fa))])
    (* d w)))

(define (make-flat-array dims init)
  (define ds (cdr (reverse (list-scanl * 1 (reverse dims)))))
  (FlatArray (make-vector (list-product dims) init) ds))

(define (flat-array-ref fa dims)
  (vector-ref (FlatArray-vec fa) (flat-array/args->index fa dims)))

(define (flat-array-set! fa dims val)
  (vector-set! (FlatArray-vec fa) (flat-array/args->index fa dims) val))

(define (flat-array-update! fa dims updater)
  (define vec (FlatArray-vec fa))
  (define index (flat-array/args->index fa dims))
  (vector-set! vec index (updater (vector-ref vec index))))

