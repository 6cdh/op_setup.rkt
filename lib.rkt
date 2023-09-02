#lang racket

;; TOC
;; * requires
;; * array utils
;; * fenwick tree
;; * array representation of tree
;; * segment tree
;; * disjoint set
;; * static BST
;; * fast-set
;; * bitset
;; * algorithms
;; * data structure helpers
;; * syntax
;; * other functions

;; performance note:
;; * use pair instead of 2 element list
;; * use (cons x y) not (list x y ...) in pattern match

;; requires

(require data/heap)
(require data/skip-list)
(require syntax/parse/define)
(require racket/sandbox)
(require (rename-in racket/unsafe/ops
                    [unsafe-fxquotient quotient]))

;; array utils

;; make a multi-dimension array
;; (make-array dims ... init-value)
(define-syntax make-array
  (syntax-rules ()
    [(_ n init)
     (make-vector n init)]
    [(_ n args ...)
     (build-vector n (lambda _ (make-array args ...)))]))

;; array-ref
;; (aref array dims ...)
(define-syntax aref
  (syntax-rules ()
    [(_ arr) arr]
    [(_ arr i args ...)
     (aref (vector-ref arr i) args ...)]))

;; array-set!
;; (aset! array dims ... new-value)
(define-syntax aset!
  (syntax-rules ()
    [(_ arr i v)
     (vector-set! arr i v)]
    [(_ arr i args ... v)
     (aset! (vector-ref arr i) args ... v)]))

;; array-update!
;; (aupd! array dims ... updater)
;; updater : x -> x
(define-syntax-rule (aupd! arr dims ... fn)
  (aset! arr dims ... (fn (aref arr dims ...))))

;; array-swap!
;; (aswap! array (dims1 ...) (dims2 ...))
(define-syntax-rule (aswap! arr (index1 ...) (index2 ...))
  (let ([t (aref arr index1 ...)])
    (aset! arr index1 ... (aref arr index2 ...))
    (aset! arr index2 ... t)))

(define-syntax-rule (alen arr)
  (vector-length arr))

;; string

(define-syntax-rule (sref str i)
  (string-ref str i))

(define-syntax-rule (slen str)
  (string-length str))

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
;; the root is 1

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

;; make disjoint set of (range 0 n)
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

;; static BST

;; Binary Search Tree on a predefined sorted vector

(struct SBST
  (keys vals none))

(define (make-sbst lst none)
  (define keys (list->vector lst))
  (SBST keys (make-vector (vector-length keys) none) none))

(define (sbst-search-index sbst key)
  (define keys (SBST-keys sbst))
  (define n (vector-length keys))
  (let loop ([l 0]
             [r n])
    (define mid (quotient (+ l r) 2))
    (cond [(= l r) l]
          [(<= key (vector-ref keys mid)) (loop l mid)]
          [else (loop (+ 1 mid) r)])))

(define (sbst-ref sbst key default)
  (define index (sbst-search-index sbst key))
  (define vals (SBST-vals sbst))
  (if (or (>= index (vector-length vals))
          (equal? (vector-ref vals index) (SBST-none sbst)))
      default
      (vector-ref vals index)))

(define (sbst-set! sbst key new-val)
  (vector-set! (SBST-vals sbst) (sbst-search-index sbst key) new-val))

(define (sbst-remove! sbst key)
  (sbst-set! sbst key (SBST-none sbst)))

(define (sbst-update! sbst key updater default)
  (sbst-set! sbst key (updater (sbst-ref sbst key default))))

(define (sbst-iter sbst key)
  (sbst-search-index sbst key))

(define (sbst-iter-next sbst it)
  (if (= (+ 1 it) (vector-length (SBST-keys sbst)))
      #f
      (+ 1 it)))

(define (sbst-iter-prev sbst it)
  (if (= -1 (- it 1))
      #f
      (- it 1)))

;; fast-set

(define (make-fset)
  (make-hash))

(define (fset-has? fs v)
  (hash-has-key? fs v))

(define (fset-add! fs v)
  (hash-set! fs v #t))

(define (fset-remove! fs v)
  (hash-remove! fs v))

(define (list->fset lst)
  (for/fold ([fs (make-fset)])
            ([v lst])
    (fset-add! fs v)
    fs))

;; bitset

(struct Bitset
  (bits val->mask full)
  #:transparent)

(define (make-bitset lst)
  (define h (make-hash))
  (for ([(v i) (in-indexed lst)])
    (hash-set! h v (expt 2 i)))
  (Bitset 0 h (sub1 (expt 2 (length lst)))))

(define (bitset-has? bs val)
  (positive? (bitwise-and (Bitset-bits bs)
                          (hash-ref (Bitset-val->mask bs) val))))

(define (bitset-empty? bs)
  (zero? (Bitset-bits bs)))

(define (bitset-full? bs)
  (= (Bitset-bits bs) (Bitset-full bs)))

(define (bitset-add bs val)
  (match bs
    [(Bitset bits val->mask full)
     (Bitset (bitwise-ior bits (hash-ref val->mask val)) val->mask full)]))

(define (bitset-remove bs val)
  (match bs
    [(Bitset bits val->mask full)
     (Bitset (bitwise-and bits (bitwise-not (hash-ref val->mask val)))
             val->mask full)]))

;; is `bitset` a subset of `bits`?
;; bitset-subset? : (integer, integer) -> boolean
(define (bitset-subset? bits bitset)
  (= bitset (bitwise-ior bits bitset)))

;; multiset

(define (make-multiset)
  (make-adjustable-skip-list))

(define (multiset-add! mset val)
  (skip-list-update! mset val add1 0))

(define (multiset-remove! mset val)
  (skip-list-update! mset val sub1 1)
  (when (= 0 (skip-list-ref mset val))
    (skip-list-remove! mset val)))

(define (multiset-minimum mset)
  (define it (skip-list-iterate-first mset))
  (if it
      (skip-list-iterate-key mset it)
      #f))

(define (multiset-maximum mset limit)
  (define it (skip-list-iterate-greatest/<=? mset limit))
  (if it
      (skip-list-iterate-key mset it)
      #f))

;; algorithms

;; range-sum : (listof number) -> procedure
;; return a procedure that calculates (sum (sublist arr (range i j)))

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
;; path-finding/dijkstra : (node, node, edgeof) -> (cons path cost)
;; edgeof : node -> (listof (cons node cost))
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

;; print expr and their value
(define-syntax-rule (debugv expr ...)
  (let ()
    (debug (quote expr) expr) ...))

(define-syntax-rule (debug tag form)
  (let ([res form])
    (display tag)
    (display ": ")
    (println res)
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

;; cache the function `fn`
;; (cachef! function-name)
;; It use a hashtable for cache.

;; The second usage is
;; (cachef! function-name dims ... not-exist-value)
;; Then it would use vector for cache.
;; dims are number or expression that evaluate to number
;; not-exist-value is the value that indicate that the
;; key-value pair is not exist.
(define-syntax-parse-rule (cachef! fn:id args:expr ...)
  (set! fn (cachef fn args ...)))

(define-syntax-parser cachef
  [(_ fn:id)
   #'(cachef-hash fn)]
  [(_ fn:id hints:expr ... init)
   (with-syntax ([(args ...) (generate-temporaries #'(hints ...))])
     #'(let* ([cache (make-array hints ... init)]
              [ori-fn fn])
         (lambda (args ...)
           (cond [(or (< args 0) ...
                      (>= args hints) ...)
                  (ori-fn args ...)]
                 [else
                  (when (equal? init (aref cache args ...))
                    (aset! cache args ... (ori-fn args ...)))
                  (aref cache args ...)]))))])

;; return a hash table cached version of function `fn`
(define (cachef-hash fn)
  (let ([cache (make-hash)])
    (lambda args
      (when (not (hash-has-key? cache args))
        (hash-set! cache args (apply fn args)))
      (hash-ref cache args))))

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

;; replace `fn` with its `log-call-times` version
(define-syntax-rule (log-call-times! fn)
  (set! fn (log-call-times fn)))

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
;; example:
;; (~> x (doA x other-arg) (doB x other-arg))
(define-syntax-parse-rule (~> x:id exprs ...)
  (let* ([x exprs] ...)
    x))

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

;; C like language syntax
;; for bitwise/array heavy program.
;; it also provide nested infix expr
;; example:
;; (C x := 1) ; (define x 1)
;; (C (1 + 1) + 2)
;; (C array [dim1] [dim2])
;; (C array [dim1] [dim2] = new-value)
;; (C x = new-value) ; assignment
;; special infix operator:
;; % : modulo
;; shl : arithmetic-shift
;; ~ : bitwise-not
;; & : bitwise-and
;; OR : bitwise-ior
;; ^ : bitwise-xor
;; other function fallback to Racket function, for example,
;; (C 1 / 2)
(define-syntax-parser C
  [(_ (expr ...) then ...)
   #'(C1 (C expr ...) then ...)]
  [(_ expr ...)
   #'(C1 expr ...)])

;; like `C` but the first argument would not be expanded
;; should not be used externally
(define-syntax-parser C1
  #:datum-literals (:= = - % shl ~ & OR ^ $)
  [(_ result)
   #'result]
  [(_ ident:id := expr ...)
   #'(define ident (C expr ...))]
  [(_ ident:id = expr ...)
   #'(set! ident (C expr ...))]
  [(_ - a)
   #'(- a)]
  [(_ ($ expr ...))
   #'(expr ...)]
  [(_ a - b then ...)
   #'(C1 (- a (C b)) then ...)]
  [(_ a % b then ...)
   #'(C1 (modulo a (C b)) then ...)]
  [(_ a shl b then ...)
   #'(C1 (arithmetic-shift a (C b)) then ...)]
  [(_ ~ a then ...)
   #'(C1 (bitwise-not (C a)) then ...)]
  [(_ a & b then ...)
   #'(C1 (bitwise-and a (C b)) then ...)]
  [(_ a OR b then ...)
   #'(C1 (bitwise-ior a (C b)) then ...)]
  [(_ a ^ b then ...)
   #'(C1 (bitwise-xor a (C b)) then ...)]
  [(_ arr:id [idx ...] = expr ...)
   #'(vector-set! arr (C idx ...) (C expr ...))]
  [(_ arr:id [idx ...] then ...)
   #'(C1 (vector-ref arr (C idx ...)) then ...)]
  [(_ a op b then ...)
   #'(C1 (op a (C b)) then ...)])

;; for

(define-syntax-rule (for/max init-minimum-value args ... last-expr)
  (for/fold ([maxv init-minimum-value])
            args ...
    (max maxv last-expr)))

(define-syntax-rule (for/min init-maximum-value args ... last-expr)
  (for/fold ([mini init-maximum-value])
            args ...
    (min mini last-expr)))

(define-syntax-rule (for*/max init-minimum-value args ... last-expr)
  (for*/fold ([maxv init-minimum-value])
             args ...
    (max maxv last-expr)))

(define-syntax-rule (for*/min init-maximum-value args ... last-expr)
  (for*/fold ([mini init-maximum-value])
             args ...
    (min mini last-expr)))

;; others

(define-syntax-parse-rule (upd! var:id updater)
  (set! var (updater var)))

(define-syntax-parse-rule (vec! var:id ...)
  (let ()
    (vec1! var) ...))

(define-syntax-parse-rule (vec1! var:id)
  (set! var
        (cond [(string? var) (list->vector (string->list var))]
              [(list? var) (list->vector var)]
              [else var])))

;; other functions

;; convert (vectorof (vectorof x)) to (listof (listof x))
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

;; ranges

(define in-closed-range in-inclusive-range)

(define in-rev-range
  (case-lambda
    [(from to) (in-range (sub1 to) (sub1 from) -1)]
    [(from to delta) (in-range (- to delta) (- from delta) (- delta))]))

(define in-closed-rev-range
  (case-lambda
    [(from to) (in-rev-range from (add1 to))]
    [(from to delta) (in-rev-range from (+ to delta) delta)]))

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

(define-syntax-parse-rule (sort! lst:id less-than?:expr args ...)
  (set! lst (sort lst less-than? args ...)))

;; list->binary : binary-list -> integer
;; binary-list : a list of number 0 or 1
(define (list->binary lst)
  (for/sum ([v lst]
            [i (in-naturals 0)])
    (* v (expt 2 i))))

;; Return O(n^2) pairs of n length list
(define (pairs lst)
  (let loop ([prev '()]
             [lst lst]
             [result '()])
    (match* [prev lst]
      [(_ '()) result]
      [('() (cons cur rem))
       (loop (cons cur prev) rem result)]
      [(prev (cons cur rem))
       (loop (cons cur prev) rem
             (append (map (λ (p) (cons p cur)) prev) result))])))

(define (counter-add! cter val)
  (hash-update! cter val add1 0))

(define (counter-remove! cter val)
  (hash-update! cter val sub1)
  (when (= 0 (hash-ref cter val))
    (hash-remove! cter val)))

(define (string-reverse str)
  (list->string (reverse (string->list str))))

(define (bitcount x)
  (for/sum ([i 64])
    (if (bitwise-bit-set? x i) 1 0)))

(define (generate-primes limit)
  (let ([table (make-vector (add1 limit) #t)])
    (aset! table 0 #f)
    (aset! table 1 #f)
    (for ([i (in-range 2 (add1 limit))])
      (when (aref table i)
        (for ([j (in-range (* 2 i) (add1 limit) i)])
          (aset! table j #f))))
    (λ (i) (aref table i))))

(define (abs-diff x y)
  (abs (- x y)))

(define (divisible x p)
  (= 0 (modulo x p)))

;; return a list a indexes `ans`, for each index `i`, `ans[i]` is the
;; index of the previous element that satisfy
;; `(pred (aref lst (aref ans i)) (aref lst i))`
;; O(n)
(define (find-prev lst pred)
  (vec! lst)
  (define ans (make-vector (alen lst) -1))

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

(define (boolean->number x)
  (if x 1 0))

(provide (all-defined-out))

