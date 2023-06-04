#lang racket

;; TOC
;; * requires
;; * array utils
;; * fenwick tree
;; * array representation of tree
;; * segment tree
;; * disjoint set
;; * algorithms
;; * data structure helpers
;; * syntax
;; * other functions

;; requires

(require data/heap)
(require data/skip-list)
(require (for-syntax syntax/parse))
(require racket/sandbox)

;; array utils

;; make a multi-dimension array
(define-syntax make-array
  (syntax-rules ()
    [(_ n init)
     (make-vector n init)]
    [(_ n args ...)
     (build-vector n (lambda _ (make-array args ...)))]))

;; array-ref
(define-syntax aref
  (syntax-rules ()
    [(_ arr) arr]
    [(_ arr i args ...)
     (aref (vector-ref arr i) args ...)]))

;; array-set!
(define-syntax aset!
  (syntax-rules ()
    [(_ arr i v)
     (vector-set! arr i v)]
    [(_ arr i args ... v)
     (aset! (vector-ref arr i) args ... v)]))

;; array-update!
(define-syntax-rule (aupd! arr dims ... fn)
  (aset! arr dims ... (fn (aref arr dims ...))))

;; array-swap!
(define-syntax-rule (aswap! arr (index1 ...) (index2 ...))
  (let ([t (aref arr index1 ...)])
    (aset! arr index1 ... (aref arr index2 ...))
    (aset! arr index2 ... t)))

;; fenwick tree

;; make a fenwick tree with (range 0 n)
;; O(n)
(define (make-fenwick-tree n)
  (make-vector n 0))

;; fenwick-tree[i] += delta
;; O(log n)
(define (ft-add! fenwick-tree i delta)
  (let loop ([i i])
    (when (< i (vector-length fenwick-tree))
      (aupd! fenwick-tree i (lambda (x) (+ x delta)))
      (loop (bitwise-ior i (add1 i))))))

;; (sum (sublist fenwick-tree (range i j)))
(define (ft-sum fenwick-tree i j)
  (let loop ([sum 0]
             [i i]
             [j j])
    (cond [(> j i)
           (loop (+ sum (aref fenwick-tree (sub1 j)))
                 i
                 (bitwise-and j (sub1 j)))]
          [(> i j)
           (loop (- sum (aref fenwick-tree (sub1 i)))
                 (bitwise-and i (sub1 i))
                 j)]
          [(= i j)
           sum])))

;; array representation of tree ;;

(define (tree-father k)
  (quotient k 2))

(define (tree-left k)
  (* 2 k))

(define (tree-right k)
  (add1 (* 2 k)))

(define (tree-sibling k)
  (bitwise-xor k 1))

;; segment tree ;;

(define (make-segtree len init op)
  (let ([n (max 2 (expt 2 (exact-ceiling (log len 2))))])
    (list (make-array (* 2 n) init) n op)))

(define (segtree-ref segtree k)
  (match-let ([(list tree n op) segtree])
    (aref tree (+ k n))))

(define (segtree-query segtree left right)
  (match-let ([(list tree n op) segtree])
    (let loop ([l (+ left n)] [r (+ right n)] [result (aref tree 0)])
      (cond [(> l r) result]
            [(odd? l) (loop (add1 l) r (op result (aref tree l)))]
            [(even? r) (loop l (sub1 r) (op result (aref tree r)))]
            [else (loop (tree-father l) (tree-father r) result)]))))

(define (segtree-set! segtree key newv)
  (match-let ([(list tree n op) segtree])
    (aset! tree (+ key n) newv)

    (let loop ([k (tree-father (+ key n))])
      (when (>= k 1)
        (aset! tree k
               (op (aref tree (tree-left k)) (aref tree (tree-right k))))
        (loop (tree-father k))))))

;; disjoint set

(define (make-dsu n)
  (build-vector n values))

(define (dsu-rootof dsu x)
  (define r (aref dsu x))
  (cond [(= r x)
         x]
        [else
         (aset! dsu x (dsu-rootof dsu r))
         (aref dsu x)]))

(define (dsu-union! dsu a b)
  (aset! dsu (dsu-rootof dsu a) (dsu-rootof dsu b)))

;; algorithms

;; range-sum : (listof number) -> procedure
;; return a procedure that calculates (sum (sublist arr (range i j)))
;;
;; O(n) where n is the length of `arr`
;; the result function runs in O(1)
(define (range-sum arr)
  (let* ([n (length arr)]
         [prefix (make-vector (add1 n) 0)])
    (for ([v arr]
          [i (in-inclusive-range 1 n)])
      (aset! prefix i (+ v (aref prefix (sub1 i)))))
    (λ (i j) (- (aref prefix j) (aref prefix i)))))

;; expmod : (number, number, number) -> number
;; return expt(a, b) mod m
;;
;; O(log b)
(define (expmod a b m)
  (cond [(= b 0) 1]
        [(even? b) (modulo (sqr (expmod a (/ b 2) m)) m)]
        [else (modulo (* a (expmod a (sub1 b) m)) m)]))

;; count-inversions : (fenwick-tree, (listof number)) -> non-negative-integer
;; O(n log n)
(define (count-inversions fenwick-tree lst)
  (let* ([n (vector-length fenwick-tree)]
         [res (for/fold ([res 0])
                        ([v lst])
                (ft-add! fenwick-tree v 1)
                (+ res (ft-sum fenwick-tree (add1 v) n)))])
    (for ([v lst])
      (ft-add! fenwick-tree v -1))
    res))

;; binary search the first element that meets `op`
(define (bsearch-least l r op)
  (define m (quotient (+ l r) 2))
  (cond [(= l r) l]
        [(op m) (bsearch-least l m op)]
        [else (bsearch-least (add1 m) r op)]))

;; dijkstra algorithm
;; path-finding/dijkstra : (node, node, edgeof) -> (list path cost)
;; edgeof : node -> (listof (list node cost))
;; path : (listof node)
;; cost : number
;; node : any
(define (path-finding/dijkstra s t edgeof)
  (define dist (make-hash))
  (define prev (make-hash))

  (define (build-path prev)
    (define (rec node path)
      (cond [(= node s) (cons s path)]
            [else (rec (hash-ref prev node) (cons node path))]))

    (rec t '()))

  (define (rec h)
    (match-define (cons d closest) (heap-min h))
    (heap-remove-min! h)
    (cond [(equal? closest t)
           (cons (build-path prev) d)]
          [else
           (for ([edge (edgeof closest)])
             (match-define (cons to cost) edge)
             (define d1 (+ d cost))
             (when (or (not (hash-has-key? dist to))
                       (< d1 (hash-ref dist to)))
               (hash-set! dist to d1)
               (hash-set! prev to closest)
               (heap-add! h (cons d1 to))))

           (if (zero? (heap-count h))
               #f
               (rec h))]))

  (define h (make-heap (λ (a b) (<= (car a) (car b)))))
  (heap-add! h (cons 0 s))
  (rec h))

;; data structure helpers

(define (skip-list-update! sl key fn default)
  (skip-list-set! sl key
                  (fn (skip-list-ref sl key default))))

;; return a list of keys in (inclusive-range beg end)
(define (skip-list-range sl beg end)
  (let loop ([lst '()]
             [it (skip-list-iterate-least/>=? sl beg)])
    (cond [(not it) lst]
          [(> (skip-list-iterate-key sl it) end) lst]
          [else (loop (cons (skip-list-iterate-key sl it) lst)
                      (skip-list-iterate-next sl it))])))

;; syntax

;; while loop
(define-syntax-rule (while condition body ...)
  (do () ((not condition))
    body ...))

;; replace recursive function `fn` with a new same function except it
;; print input/output
(define-syntax-rule (debugf! fn)
  (set! fn (tracef (quote fn) fn)))

;; print a expr and its value
(define-syntax-rule (debugv var ...)
  (let ()
    (debug (quote var) var) ...))

(define-syntax-rule (debug tag form)
  (let ([res form])
    (display tag)
    (display ": ")
    (pretty-display res)
    res))

;; functional version of `debugf!`
(define (tracef tag fn)
  (let ([cnt 0])
    (lambda args
      (let ([c cnt])
        (displayln (format "~a [frame ~a] <- ~a" tag c args))
        (set! cnt (add1 cnt))
        (define res (apply fn args))
        (set! cnt (sub1 cnt))
        (displayln (format "~a [frame ~a] -> ~a" tag c res))
        res))))

;; cache the function `fn`
(define-syntax-rule (cachef! fn)
  (set! fn (cachef-hash fn)))

;; return a hash table cached version of function `fn`
(define (cachef-hash fn)
  (let ([cache (make-hash)])
    (lambda args
      (when (not (hash-has-key? cache args))
        (hash-set! cache args (apply fn args)))
      (hash-ref cache args))))

;; return a 3d array cached version of function `fn`
(define (cachef-vec3 fn vec)
  (let ([init (aref vec 0 0 0)])
    (lambda (x y z)
      (when (= init (aref vec x y z))
        (aset! vec x y z (fn x y z)))
      (aref vec x y z))))

;; return a 2d array cached version of function `fn`
(define (cachef-vec2 fn vec)
  (let ([init (aref vec 0 0)])
    (lambda (x y)
      (when (= init (aref vec x y))
        (aset! vec x y (fn x y)))
      (aref vec x y))))

;; return a 1d array cached version of function `fn`
(define (cachef-vec fn vec)
  (let ([init (aref vec 0)])
    (lambda (x)
      (when (= init (aref vec x))
        (aset! vec x (fn x)))
      (aref vec x))))

;; (timeout time expr)
;; limit the expr runs complete in `time` seconds
(define-syntax timeout
  (syntax-rules ()
    [(_ form)
     (with-limits 1 10 (time form))]
    [(_ t form)
     (with-limits t 10 (time form))]))

;; return a new function that same with `fn`,
;; but record the number of calls, and can obtain
;; it by running `(fn 'query)`.
(define (log-call-times fn)
  (let ([cnt 0])
    (define (call . args)
      (set! cnt (add1 cnt))
      (apply fn args))

    (define (dispatch method . args)
      (match method
        ['query cnt]
        [_ (apply call method args)]))
    dispatch))

;; replace `fn` with its `log-call-times` version
(define (log-call-times! fn)
  (set! fn (log-call-times fn)))

;; assert invariant
(define (assert cond . msg)
  (unless cond
    (apply error msg)))

;; let `proc1` runs before every time `proc` is called
(define-syntax-rule (call-before! proc proc1)
  (set! proc
        (lambda args
          (proc1)
          (apply proc args))))

;; let `proc1` runs after every time `proc` is called
(define-syntax-rule (call-after! proc proc1)
  (set! proc
        (lambda args
          (let ([res (apply proc args)])
            (proc1)
            res))))

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
;; `%` as placeholder
(define-syntax (~> stx)
  (syntax-parse stx
                #:datum-literals (%)
                [(_ v)
                 #'v]
                [(_ v (fn args1 ... % args2 ...) rems ...)
                 #'(~> (fn args1 ... v args2 ...) rems ...)]))

;; leetcode modulo
(define (lc-mod x)
  (modulo x (+ 7 #e1e9)))

;; call `lc-mod` after operation `op`
(define-syntax modop
  (syntax-rules ()
    [(_ val)
     val]
    [(_ op val)
     val]
    [(_ op val1 val2 rems ...)
     (modop op (lc-mod (op val1 val2)) rems ...)]))

;; C like language syntax
;; for bitwise/array heavy program.
;; it also provide nested infix expr
;; for example, `(C ((1 + 1) + 2))`
(define-syntax C
  (syntax-rules ()
    [(_ (expr ...) then ...)
     (C1 (C expr ...) then ...)]
    [(_ expr ...)
     (C1 expr ...)]))

;; like `C` but the first argument would not be expanded
;; should not be used externally
(define-syntax C1
  (syntax-rules (= - % shl ~ & OR ^ << >>)
    [(_ v)
     v]
    [(_ ident = expr ...)
     (set! ident (C1 expr ...))]
    [(_ - a)
     (- a)]
    [(_ a - b then ...)
     (C1 (- a (C b)) then ...)]
    [(_ a % b then ...)
     (C1 (modulo a (C b)) then ...)]
    [(_ a shl b then ...)
     (C1 (arithmetic-shift a (C b)) then ...)]
    [(_ ~ a then ...)
     (C1 (bitwise-not (C a)) then ...)]
    [(_ a & b then ...)
     (C1 (bitwise-and a (C b)) then ...)]
    [(_ a OR b then ...)
     (C1 (bitwise-ior a (C b)) then ...)]
    [(_ a ^ b then ...)
     (C1 (bitwise-xor a (C b)) then ...)]
    [(_ a [idx ...] = expr ...)
     (vector-set! a (C idx ...) (C expr ...))]
    [(_ a [idx ...] then ...)
     (C1 (vector-ref a (C idx ...)) then ...)]
    [(_ a << b then ...)
     (C1 (a (C b)) then ...)]
    [(_ a >> b then ...)
     (C1 (b a) then ...)]
    [(_ a op b then ...)
     (C1 (op a (C b)) then ...)]))

;; other functions

;; convert (vectorof (vectorof any)) to (listof (listof any))
(define (vector2d->list2d mat)
  (map vector->list (vector->list mat)))

;; reverse function of `vector2d->list2d`
(define (list2d->vector2d lst)
  (list->vector (map list->vector lst)))

;; list->hash : (listof pair) -> hash
(define (list->hash lst)
  (for/fold ([h (hash)])
            ([pair lst])
    (hash-set h (car pair) (cdr pair))))

;; convert a sequence that can iterate with `for` to hash table counter
(define (sequence->counter seq)
  (for/fold ([h (hash)])
            ([v seq])
    (hash-update h v add1 0)))

;; is `bitset` a subset of `bits`?
;; bitset-subset? : (integer, integer) -> boolean
(define (bitset-subset? bits bitset)
  (= bitset (bitwise-ior bits bitset)))

(define (compare x y)
  (cond [(= x y) '=]
        [(< x y) '<]
        [else '>]))

;; some function with same length name
(define nth0 car)
(define nth1 cadr)
(define nth2 caddr)

(define (∈ x set) (set-member? set x))
(define (∉ x set) (not (set-member? set x)))
(define U set-union)
(define ∩ set-intersect)

;; make a alphabet list from lowercase a to z
(define (alphabet)
  (map integer->char
       (inclusive-range (char->integer #\a) (char->integer #\z))))

(define (list-sum lst)
  (foldl + 0 lst))

(define (list-product lst)
  (foldl * 1 lst))

(define (maximum lst)
  (foldl max (car lst) lst))

(define (minimum lst)
  (foldl min (car lst) lst))

(define (digit-char->integer c)
  (- (char->integer c) (char->integer #\0)))

(define (alphabet-char->integer c)
  (- (char->integer c) (char->integer #\a)))

(define (uppercase-char->integer c)
  (- (char->integer c) (char->integer #\A)))

(define (scanl proc init lst)
  (for/list ([v lst])
    (set! init (proc v init))
    init))

(define (scanr proc init lst)
  (reverse
    (for/list ([v (reverse lst)])
      (set! init (proc v init))
      init)))

(define (sublist lst from to)
  (drop (take lst to) from))

(define (vector-reverse vec)
  (list->vector (reverse (vector->list vec))))

;; median of a sorted list
;; O(1)
(define (median sorted-lst)
  (define vec (list->vector sorted-lst))
  (define n (vector-length vec))
  (vector-ref vec (quotient n 2)))

(define in-reverse-range
  (case-lambda
    [(from to) (in-range (sub1 to) (sub1 from) -1)]
    [(from to delta) (in-range (- to delta) (- from delta) (- delta))]))

(define (string-ref-default str i default)
  (if (< -1 i (string-length str))
      (string-ref str i)
      default))

(define (sort< lst)
  (sort lst <))

(define (sort> lst)
  (sort lst >))

;; O(2^n * n)
;; example: (in-producer (subsetof lst #f) #f)
(define (subsetof lst stop)
  (let* ([bits 0]
         [n (length lst)]
         [subset-size (expt 2 n)])
    (lambda ()
      (match bits
        [(== subset-size) stop]
        [_ (define res
             (for/list ([i n]
                        [val lst]
                        #:when (bitwise-bit-set? bits i))
               val))
           (set! bits (add1 bits))
           res]))))

(define (set->immutable s)
  (list->set (set->list s)))

(define (list2d-dims lstlst)
  (match lstlst
    ['()
     (cons 0 0)]
    [(cons fst _rems)
     (cons (length lstlst) (length fst))]))

;; faster group-by for sorted list (increasing/decreasing)
(define (group-by-sorted key lst [same? equal?])
  (match (length lst)
    [0 '()]
    [1 (list lst)]
    [_ (reverse
         (map reverse
              (for/fold ([res '()])
                        ([p lst]
                         [v (cdr lst)])
                (match* [res (same? (key p) (key v))]
                  [('() #t)
                   (list (list v p))]
                  [('() #f)
                   (list (list v) (list p))]
                  [((cons fst rem) #t)
                   (cons (cons v fst) rem)]
                  [(res #f)
                   (cons (list v) res)]))))]))

(provide (all-defined-out))

