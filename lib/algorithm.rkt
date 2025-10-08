#lang racket

(provide (all-defined-out))

(require "array.rkt")
(require "fenwick-tree.rkt")
(require "utils.rkt")

;; ** Range Sum

;; range-sum : (listof number) -> procedure
;; return a procedure that calculates (sum (sublist arr (range i j)))

;; O(n) where n is the length of `arr`
;; the result function runs in O(1)
(define (range-sum arr)
  (let* ([n (length arr)]
         [prefix (make-vector (add1 n) 0)])
    (for ([v (in-list arr)]
          [i (in-inclusive-range 1 n)])
      (aset! prefix i (+ v (aref prefix (sub1 i)))))
    (λ (i j) (- (aref prefix j) (aref prefix i)))))

;; ** Expmod

;; expmod : (number, number, number) -> number
;; return expt(a, b) mod m
;;
;; O(log b)
(define (expmod a b m)
  (cond [(= b 0) 1]
        [(even? b) (modulo (sqr (expmod a (/ b 2) m)) m)]
        [else (modulo (* a (expmod a (sub1 b) m)) m)]))

;; ** Count Inversion

;; count-inversions : (fenwick-tree, (listof number)) -> natural-number
;; count inversions of the fenwick tree
;; O(n log n)
(define (count-inversions fenwick-tree lst)
  (let* ([n (vector-length fenwick-tree)]
         [res (for/fold ([res 0])
                        ([v (in-list lst)])
                (ft-add! fenwick-tree v 1)
                (+ res (ft-sum fenwick-tree (add1 v) n)))])
    (for ([v (in-list lst)])
      (ft-add! fenwick-tree v -1))
    res))

;; ** Binary Search

;; bsearch-least: (number, number, (number -> bool)) -> number
;; binary search the first element that meets `op`
;; Requires:
;; If search on a vector, there should be a
;; index i so for every j < i, (op j) is false,
;; for k >= i, (op k) is true. Then this function
;; returns i.
;; returns #f if not found.
(define (bsearch-least left right op)
  (let loop ([l left]
             [r right])
    (define m (quotient (+ l r) 2))
    (cond [(= l r) (if (op l) l #f)]
          [(op m) (loop l m)]
          [else (loop (add1 m) r)])))

;; median of a sorted list
;; O(1)
(define (median sorted-lst)
  (define vec (list->vector sorted-lst))
  (define n (vector-length vec))
  (vector-ref vec (quotient n 2)))

;; O(2^n * n) in total
;; example: (in-subset lst #f)
;; iterate all subsets of list `lst`
(define (in-subset lst stop)
  (let* ([bits 0]
         [n (length lst)]
         [subset-size (expt 2 n)])
    (define (gen)
      (match bits
        [(== subset-size) stop]
        [_ (define res
             (for/list ([i (in-range n)]
                        [val (in-list lst)]
                        #:when (bitwise-bit-set? bits i))
               val))
           (set! bits (add1 bits))
           res]))
    (in-producer gen stop)))

;; faster group-by for sorted list (increasing/decreasing)
(define (group-by-consecutive key lst [same? equal?])
  (match (length lst)
    [0 '()]
    [1 (list lst)]
    [_ (reverse
         (map reverse
              (for/fold ([res '()])
                        ([p (in-list lst)]
                         [v (in-list (cdr lst))])
                (match* [res (same? (key p) (key v))]
                  [('() #t)
                   (list (list v p))]
                  [('() #f)
                   (list (list v) (list p))]
                  [((cons fst rem) #t)
                   (cons (cons v fst) rem)]
                  [(res #f)
                   (cons (list v) res)]))))]))

;; Return O(n^2) pairs of a list
(define (pairs lst)
  (define vec (list->vector lst))
  (define n (vector-length vec))
  (for*/list ([j (in-range n)]
              [i (in-range j)])
    (cons (vector-ref vec i) (vector-ref vec j))))

(define (generate-prime-table limit)
  (let ([table (make-vector (add1 limit) #t)])
    (aset! table 0 #f)
    (aset! table 1 #f)
    (for ([i (in-range 2 (add1 limit))])
      (when (aref table i)
        (for ([j (in-range (* 2 i) (add1 limit) i)])
          (aset! table j #f))))
    (λ (i) (aref table i))))

;; return a list a indexes `ans`, for each index `i`, `ans[i]` is the
;; index of the previous element that satisfy
;; `(pred (aref lst (aref ans i)) (aref lst i))`
;; O(n)
(define (find-prev lst pred)
  (vec! lst)
  (define ans (make-vector (vector-length lst) -1))

  (for/fold ([stack '()])
            ([(v i) (in-indexed lst)])
    (define rems (or (memf (λ (j) (pred (aref lst j) v)) stack) '()))
    (when (not (null? rems))
      (aset! ans i (car rems)))
    (cons i rems))

  (vector->list ans))

;; like `find-prev`, but the index is for the next element
(define (find-next lst pred)
  (define n (length lst))
  (reverse (map (λ (i) (- n 1 i))
                (find-prev (reverse lst) pred))))

;; return a function lcp.
;; (lcp i) is the longest prefix substring which is also
;; the suffix of substring str[0..i]
(define (longest-common-prefix-function str)
  (define n (string-length str))
  (define prefix (make-vector n 0))
  (for ([i (in-range 1 n)])
    (let loop ([j (aref prefix (sub1 i))])
      (cond [(char=? (string-ref str i) (string-ref str j))
             (aset! prefix i (add1 j))]
            [(= j 0)
             (void)]
            [else
             (loop (aref prefix (sub1 j)))])))
  (λ (i) (aref prefix i)))

(define (identity-matrix n)
  (for/vector ([i (in-range n)])
    (for/vector ([j (in-range n)])
      (if (= i j) 1 0))))

(define (matrix/* mat1 mat2)
  (define m (vector-length mat1))
  (define n (vector-length mat2))
  (for/vector ([i (in-range 0 m)])
    (for/vector ([j (in-range 0 n)])
      (for/sum ([k (in-range 0 n)])
        (* (aref mat1 i k) (aref mat2 k j))))))

;; O(log n) matrix exponent operation
;; unsually used in some algorithms like
;; O(log n) fibonacci function.
(define (matrix-expmod mat p modfn)
  (cond [(= p 0)
         (identity-matrix (vector-length (aref mat 0)))]
        [else
         (define mat/2 (matrix-expmod mat (quotient p 2) modfn))
         (define ans (if (odd? p)
                         (matrix/* mat (matrix/* mat/2 mat/2))
                         (matrix/* mat/2 mat/2)))
         (for/vector ([row (in-range ans)])
           (for/vector ([v (in-range row)])
             (modfn v)))]))

