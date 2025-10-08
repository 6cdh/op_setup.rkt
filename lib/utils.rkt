#lang racket

(provide (all-defined-out))

(require "array.rkt")
(require syntax/parse/define)

(define (enumerate seq)
  (for/list ([(v i) (in-indexed seq)])
    (cons i v)))

(define (digit-char->integer c)
  (- (char->integer c) (char->integer #\0)))

(define (lower-char->integer c)
  (- (char->integer c) (char->integer #\a)))

(define (integer->lower-char i)
  (integer->char (+ i (char->integer #\a))))

(define (uppercase-char->integer c)
  (- (char->integer c) (char->integer #\A)))

(define (compare x y)
  (cond [(= x y) '=]
        [(< x y) '<]
        [else '>]))

(define (if-false-then val default)
  (if (false? val)
      default
      val))

(define-syntax in-reverse-range
  (syntax-rules ()
    [(_ to)
     (in-reverse-range 0 to)]
    [(_ from to)
     (in-range (sub1 to) (sub1 from) -1)]))

(define-syntax in-inclusive-reverse-range
  (syntax-rules ()
    [(_ to)
     (in-inclusive-reverse-range 0 to)]
    [(_ from to)
     (in-reverse-range from (add1 to))]))

;; convert (vectorof (vectorof x)) to (listof (listof x))
(define (vector2d->list2d mat)
  (map vector->list (vector->list mat)))

;; reverse function of `vector2d->list2d`
(define (list2d->vector2d lst)
  (list->vector (map list->vector lst)))

(define *alphabet-table*
  (map integer->char
       (inclusive-range (char->integer #\a) (char->integer #\z))))

;; make a alphabet list from lowercase a to z
(define (alphabet)
  *alphabet-table*)

(define-syntax-rule (cons! lst element)
  (set! lst (cons element lst)))

(define (vector-reverse vec)
  (list->vector (reverse (vector->list vec))))

(define (set->immutable s)
  (list->set (set->list s)))

(define (vector2d-dims vecvec)
  (define m (vector-length vecvec))
  (define n (if (= 0 m) 0 (vector-length (vector-ref vecvec 0))))
  (values m n))

(define (string-reverse str)
  (list->string (reverse (string->list str))))

(define (abs-diff x y)
  (abs (- x y)))

(define (divisible x p)
  (= 0 (modulo x p)))

;; leetcode modulo
(define lc-mod-const (+ #e1e9 7))

(define (lc-mod-fn x)
  (modulo x lc-mod-const))

;; mod for nested expression
;; example:
;; (lc-mod + (* #e1e9 #e1e8) (+ #e1e6 #e1e6))
(define-syntax-parser lc-mod
  [(_ v)
   #'(lc-mod-fn v)]
  [(_ op args ...)
   #'(lc-mod (op (lc-mod args) ...))])

;; anoymous function macro with arguments placeholders
(define-syntax (cut1 stx)
  (syntax-case stx ()
    [(_ exprs ...)
     (with-syntax ([_1 (datum->syntax stx '_1)])
       #'(λ (_1) exprs ...))]))

(define-syntax (cut2 stx)
  (syntax-case stx ()
    [(_ exprs ...)
     (with-syntax ([_1 (datum->syntax stx '_1)]
                   [_2 (datum->syntax stx '_2)])
       #'(λ (_1 _2) exprs ...))]))

;; as function

;; make a function proxy for a list/vector/hash table

(define ((vector->function vec) i)
  (vector-ref vec i))

(define-syntax-rule (vector->function! vec)
  (set! vec (vector->function vec)))

(define-syntax-rule (vector*->function! vec args ...)
  (set! vec (λ (args ...) (aref vec args ...))))

(define ((hash->function hash) k)
  (hash-ref hash k))

(define-syntax-rule (hash->function! hash)
  (set! hash (hash->function hash)))

(define (list->function lst)
  (define vec (list->vector lst))
  (λ (i) (vector-ref vec i)))

(define-syntax-rule (list->function! lst)
  (set! lst (list->function lst)))

;; others

;; update a variable with a updater
;; (upd! num add1) is a shorthand for (set! num (add1 num))
(define-syntax-parse-rule (upd! var:id updater)
  (set! var (updater var)))

;; like vec1! but for multiple variables
(define-syntax-parse-rule (vec! var:id ...)
  (let ()
    (vec1! var) ...))

;; convert a string or list into a vector, and reuse the variable name
;; (vec1! lst)
(define-syntax-parse-rule (vec1! var:id)
  (set! var
        (cond [(string? var) (list->vector (string->list var))]
              [(list? var) (list->vector var)]
              [else var])))

;; sort a list and reuse the variable name
(define-syntax-parse-rule (sort! lst:id less-than?:expr args ...)
  (set! lst (sort lst less-than? args ...)))

;; while loop
(define-syntax-rule (while condition body ...)
  (do () ((not condition))
    body ...))

;; print expr and their value
(define-syntax P
  (syntax-rules ()
    [(_ expr)
     (debug (quote expr) expr)]
    [(_ exprs ...)
     (debug (list (quote exprs) ...) (list exprs ...))]))

(define-syntax-rule (debug tag form)
  (let ([res form])
    (display tag)
    (display ": ")
    (pretty-print res)
    res))

;; replace recursive function `fn` with a new same function except it
;; print input/output
(define-syntax-parse-rule (debugf! fn:id)
  (set! fn (tracef (quote fn) fn)))

;; functional version of `debugf!`
(define (tracef tag fn)
  (let ([cnt 0])
    (lambda args
      (define call-indent
        (string-join
          (append (make-list (max 0 (sub1 cnt)) "\u2502  ")
                  (make-list (min 1 cnt) "\u251C\u2500\u2500"))
          ""))
      (define return-indent (string-append* (make-list cnt "\u2502  ")))
      (displayln (format "~a~a~a" call-indent tag args))
      (set! cnt (add1 cnt))
      (define res (apply fn args))
      (set! cnt (sub1 cnt))
      (displayln (format "~a\u2514\u2500 ~a" return-indent res))
      res)))

;; (timeout time expr)
;; limit the expr runs complete in `time` seconds
;; or
;; (timeout expr)
(define-syntax timeout
  (syntax-rules ()
    [(_ form)
     (with-limits 1 10 (time form))]
    [(_ t form)
     (with-limits t 10 (time form))]))

;; assert invariant
(define (assert cond . msg)
  (unless cond
    (apply error msg)))

;; display each argument and newline
(define (displaysln . args)
  (for ([arg args])
    (display arg))
  (newline))

;; for each argument, display it and newline
(define (displaylns . args)
  (for ([arg args])
    (displayln arg)))

;; swap two variables
(define-syntax-rule (swap! x y)
  (set!-values (x y) (values y x)))

;; threading macro
;; example:
;; (~> x (doA x other-arg) (doB x other-arg))
(define-syntax-parse-rule (~> x:id exprs ...)
  (let* ([x exprs] ...)
    x))

;; for

(define-syntax-rule (for/max init-minimum-value args ... last-expr)
  (for/fold ([maxv init-minimum-value])
            args ...
    (max maxv last-expr)))

(define-syntax-rule (for*/max init-minimum-value args ... last-expr)
  (for*/fold ([maxv init-minimum-value])
             args ...
    (max maxv last-expr)))

(define-syntax-rule (for/min init-maximum-value args ... last-expr)
  (for/fold ([mini init-maximum-value])
            args ...
    (min mini last-expr)))

(define-syntax-rule (for*/min init-maximum-value args ... last-expr)
  (for*/fold ([mini init-maximum-value])
             args ...
    (min mini last-expr)))

(define-syntax-rule (for/count args ... last-expr)
  (for/sum args ...
    (if last-expr 1 0)))

(define-syntax-rule (for*/count args ... last-expr)
  (for*/sum args ...
    (if last-expr 1 0)))
