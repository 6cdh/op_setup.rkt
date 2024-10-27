#lang racket

;; TOC
;; * Data structure
;; ** Helpers
;; ** Multidimensional Array
;; ** Flattened Multidimensional Array
;; ** Fenwick Tree
;; ** Array representation of Binary Tree
;; ** Segment Tree
;; ** Disjoint Set
;; ** Static BST
;; ** BitSet
;; ** Lazy Heap
;; ** Skip List
;; ** Counter
;; ** Trie
;; ** Char Table
;; * Algorithm
;; ** Range Sum
;; ** Expmod
;; ** Count Inversion
;; ** Binary Search
;; ** Graph
;; * Functional
;; ** Range
;; ** Bitwise
;; ** Points
;; ** Others
;; * Syntax

;; Implementation Performance Note:
;; * use pair instead of 2 element list
;; * use (cons x y) not (list x y ...) in pattern match
;; * use mutable hashtable instead of immutable hashtable or set

;; Design
;; * use values to return multiple values

;; requires

(require data/heap)
(require data/skip-list)
(require data/splay-tree)
(require syntax/parse/define)
(require racket/sandbox)
(require (rename-in racket/unsafe/ops
                    [unsafe-fxquotient quotient]))
(require racket/fixnum)

;; * Data structure

;; ** Helpers

(define slen string-length)
(define vlen vector-length)
(define sref string-ref)

;; ** Performance

(define first car)
(define second cadr)
(define third caddr)

;; ** Multidimensional Array

;; make a multi-dimension array
;; (make-array dims ... init-value)
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
;; updater : x -> x
(define-syntax-rule (aupd! arr dims ... updater)
  (aset! arr dims ... (updater (aref arr dims ...))))

;; array-swap!
;; (aswap! array (dims1 ...) (dims2 ...))
(define-syntax-rule (aswap! arr (dims1 ...) (dims2 ...))
  (let ([t (aref arr dims1 ...)])
    (aset! arr dims1 ... (aref arr dims2 ...))
    (aset! arr dims2 ... t)))

;; ** Flattened Multidimensional Array

(struct FlattenedArray
  (vec ds))

(define (farray/args->index fa dims)
  (for/sum ([d dims]
            [w (FlattenedArray-ds fa)])
    (* d w)))

(define (make-farray dims init)
  (define ds (cdr (reverse (scanl * 1 (reverse dims)))))
  (FlattenedArray (make-vector (product dims) init) ds))

(define (farray-ref fa dims)
  (vector-ref (FlattenedArray-vec fa) (farray/args->index fa dims)))

(define (farray-set! fa dims val)
  (vector-set! (FlattenedArray-vec fa) (farray/args->index fa dims) val))

(define (farray-update! fa dims updater)
  (define vec (FlattenedArray-vec fa))
  (define index (farray/args->index fa dims))
  (vector-set! vec index (updater (vector-ref vec index))))

;; ** Fenwick Tree
;; Fenwick tree provides a vector abstraction, and
;; O(log n) update
;; O(log n) range sum query

;; make a fenwick tree with (range 0 n)
;; O(n)
(define (make-fenwick-tree n)
  (make-vector n 0))

;; fenwick-tree[i] += delta
;; O(log n)
(define (ft-add! fenwick-tree i delta)
  (let loop ([i i])
    (when (< i (vector-length fenwick-tree))
      (aupd! fenwick-tree i (λ (x) (+ x delta)))
      (loop (bs-set-lowest-zero-to-one i)))))

;; query the sum of (range i j)
;; O(log n)
(define (ft-sum fenwick-tree i j)
  (let loop ([sum 0]
             [i i]
             [j j])
    (cond [(> j i)
           (loop (+ sum (aref fenwick-tree (sub1 j)))
                 i
                 (bs-set-highest-one-to-zero j))]
          [(> i j)
           (loop (- sum (aref fenwick-tree (sub1 i)))
                 (bs-set-highest-one-to-zero i)
                 j)]
          [else sum])))

;; ** Array representation of Binary Tree

; root is 1

(define (tree1-father k)
  (quotient k 2))

(define (tree1-left k)
  (* 2 k))

(define (tree1-right k)
  (add1 (* 2 k)))

(define (tree1-sibling k)
  (bitwise-xor k 1))

; root is 0

(define (tree0-father k)
  (quotient (sub1 k) 2))

(define (tree0-left k)
  (+ (* 2 k) 1))

(define (tree0-right k)
  (+ (* 2 k) 2))

;; ** Segment Tree
;; Segment Tree provide a vector abstraction, and
;; O(log n) range sum query (allows a custom operation
;;          and extends to maximum, minimum, etc query)
;; O(log n) update

;; the lowest layer of the segment tree is the minimum power of 2
;; that is not less than `len`

;; O(len)
(define (make-segtree len init op)
  (let ([n (max 2 (expt 2 (exact-ceiling (log len 2))))])
    (list (make-vector (* 2 n) init) n op)))

;; O(1)
(define (segtree-ref segtree k)
  (match-let ([(list tree n op) segtree])
    (aref tree (+ k n))))

;; O(log n)
(define (segtree-query segtree left right)
  (match-let ([(list tree n op) segtree])
    (let loop ([l (+ left n)] [r (+ right n)] [result (aref tree 0)])
      (cond [(> l r) result]
            [(odd? l) (loop (add1 l) r (op result (aref tree l)))]
            [(even? r) (loop l (sub1 r) (op result (aref tree r)))]
            [else (loop (tree1-father l) (tree1-father r) result)]))))

;; O(log n)
(define (segtree-set! segtree key newv)
  (match-let ([(list tree n op) segtree])
    (aset! tree (+ key n) newv)

    (let loop ([k (tree1-father (+ key n))])
      (when (>= k 1)
        (aset! tree k
               (op (aref tree (tree1-left k))
                   (aref tree (tree1-right k))))
        (loop (tree1-father k))))))


;; ** Disjoint Set
;; Initially, every element is in its own set
;; union! operation merge two set into a larger set
;; rootof operation query the root of the set of a given element
;;                  or which set it belongs to

;; make disjoint set of (range 0 n)
;; O(n)
(define (make-dsu n)
  (build-vector n values))

;; almost constant complexity
(define (dsu-rootof dsu x)
  (match (aref dsu x)
    [(== x) x]
    [fa (let ([r (dsu-rootof dsu fa)])
          (aset! dsu x r)
          r)]))

;; almost constant complexity
(define (dsu-union! dsu a b)
  (aset! dsu (dsu-rootof dsu a) (dsu-rootof dsu b)))

;; ** Static BST

;; Binary Search Tree on a predefined sorted vector
;; The only usage is that it's much faster than
;; data/skip-list or data/splay-tree

(struct SBST
  (keys vals none))

(define (make-sbst sorted-lst none)
  (define keys (list->vector sorted-lst))
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

;; ** BitSet

;; a simple abstraction of a bitset of a list

(define (full-bitset lst)
  (sub1 (expt 2 (length lst))))

(define (empty-bitset)
  0)

(define (bitset-has? bits val)
  (positive? (bitwise-and bits (expt 2 val))))

(define (bitset-empty? bits)
  (zero? bits))

(define (bitset-full? bs bits)
  (= bits bs))

(define (bitset-add bits val)
  (bitwise-ior bits (expt 2 val)))

(define (bitset-remove bits val)
  (bitwise-and bits (bitwise-not (expt 2 val))))

(define (bitset-count bits)
  (if (zero? bits)
      0
      (add1 (bitset-count (bitwise-and bits (sub1 bits))))))

;; ** Heap

(define heap-max heap-min)
(define heap-remove-max! heap-remove-min!)

(define (heap-empty? h)
  (= 0 (heap-count h)))

;; ** Lazy Heap

;; provide O(log n) lazy delete compared normal heap O(n) delete.

(struct LazyHeap
  [deleted heap])

(define (make-lazyheap <=)
  (LazyHeap (make-hash) (make-heap <=)))

(define (lazyheap-add! lh x)
  (heap-add! (LazyHeap-heap lh) x))

(define (lazyheap-delete! lh x)
  (counter-add! (LazyHeap-deleted lh) x))

(define (lazyheap-min lh)
  (match-define (LazyHeap deleted heap) lh)
  (let loop ()
    (define minv (heap-min heap))
    (cond [(hash-has-key? deleted minv)
           (counter-remove! deleted minv)
           (heap-remove-min! heap)
           (loop)]
          [else minv])))

(define (lazyheap-remove-min! lh)
  (lazyheap-min lh)
  (heap-remove-min! (LazyHeap-heap lh)))

;; ** Skip List

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

;; ** Splay Tree

(define (splay-tree-update! sl key fn default)
  (splay-tree-set! sl key
                   (fn (splay-tree-ref sl key default))))

;; ** Counter

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

(define (counter-add! cter val)
  (hash-update! cter val add1 0))

(define (counter-remove! cter val)
  (hash-update! cter val sub1)
  (when (= 0 (hash-ref cter val))
    (hash-remove! cter val)))

;; ** Trie

;; only for lowercase characters

(define (make-trie)
  (make-vector 26 #f))

(define (trie-add! alphabet str)
  (for/fold ([ab alphabet])
            ([c str])
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

;; ** Char Table

(define (make-char-table)
  (make-fxvector 256 0))

(define (char-table-ref abt c)
  (fxvector-ref abt (char->integer c)))

(define (char-table-add! abt c)
  (define i (char->integer c))
  (fxvector-set! abt i (add1 (fxvector-ref abt i))))

(define (char-table-remove! abt c)
  (define i (char->integer c))
  (fxvector-set! abt i (sub1 (fxvector-ref abt i))))

(define (char-table-update! abt c updater)
  (define i (char->integer c))
  (fxvector-set! abt i (updater (fxvector-ref abt i))))

;; * Algorithm

;; ** Range Sum

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
                        ([v lst])
                (ft-add! fenwick-tree v 1)
                (+ res (ft-sum fenwick-tree (add1 v) n)))])
    (for ([v lst])
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

;; ** Graph

(define (make-graph)
  (make-hash))

(define (graph-add-dir-edge! g from to)
  (hash-update! g from (λ (old) (cons to old)) '()))

(define (graph-add-undir-edge! g u v)
  (graph-add-dir-edge! g u v)
  (graph-add-dir-edge! g v u))

;; build graph

(define (undir-edges->graph edges)
  (define g (make-graph))
  (for ([e edges])
    (match e
      [(list u v) (graph-add-undir-edge! g u v)]))
  g)

(define (dir-edges->graph edges)
  (define g (make-hash))
  (for ([e edges])
    (match e
      [(list u v) (graph-add-dir-edge! g u v)]))
  g)

(define (undir-edges->tree edges root from)
  (define g (undir-edges->graph edges))
  (define tree-edges '())

  (define (go root from)
    (for ([c (hash-ref g root '())]
          #:when (not (equal? c from)))
      (set! tree-edges (cons (list root c) tree-edges))
      (go c root)))

  (go root from)
  (dir-edges->graph tree-edges))

;; dijkstra algorithm
;; solve single source shortest path problem
;; return the shortest distance hash table and
;; the previous node hash table
; graph/dijkstra : (node, edgeof) -> (list dist prev)
; edgeof : node -> (listof (cons node cost))
; node : any
; cost : non-negative number
; dist : (hash node cost)
; prev : (hash node node)
(define (graph/dijkstra s edgeof)
  (define dist (make-hash))
  (define prev (make-hash))

  (define (rec h)
    (cond [(heap-empty? h)
           (list dist prev)]
          [else
           (match-define (cons d closest) (heap-min h))
           (heap-remove-min! h)
           (for ([edge (edgeof closest)])
             (match-define (cons to cost) edge)
             (define d1 (+ d cost))
             (when (or (not (hash-has-key? dist to))
                       (< d1 (hash-ref dist to)))
               (hash-set! dist to d1)
               (hash-set! prev to closest)
               (heap-add! h (cons d1 to))))

           (rec h)]))

  (define h (make-heap (λ (a b) (<= (car a) (car b)))))
  (heap-add! h (cons 0 s))
  (hash-set! dist s 0)
  (rec h))

;; find the shortest path from `s` to `t` and cost
; graph/shortest : (node, node, edgeof) -> (list path cost)
; edgeof : node -> (listof (cons node cost))
; node : any
; cost : non-negative number
; path : (and (listof node) (= s (first path)) (= t (last path)))
(define (graph/shortest s t edgeof)
  (match-define (list dist prev) (graph/dijkstra s edgeof))

  (define (build-path path)
    (define node (first path))
    (cond [(= node s) path]
          [else (build-path (cons (hash-ref prev node) path))]))

  (list (build-path (list t)) (hash-ref dist t)))

(define (bfs starts edgeof)
  (define dist (make-hash))

  (define (loop nodes steps)
    (define new-nodes
      (for*/list ([node nodes]
                  [nei (edgeof node)]
                  #:when (not (hash-has-key? dist nei)))
        (hash-set! dist nei (add1 steps))
        nei))

    (when (not (null? new-nodes))
      (loop new-nodes (add1 steps))))

  (loop starts 0)
  dist)

;; * Functional

;; ** Bitwise

;; all the arguments should be a non-negative fixnum integer

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

;; ** Range

(define in-reverse-range
  (case-lambda
    [(from to) (in-range (sub1 to) (sub1 from) -1)]
    [(from to delta) (in-range (- to delta) (- from delta) (- delta))]))

(define in-inclusive-reverse-range
  (case-lambda
    [(from to) (in-reverse-range from (add1 to))]
    [(from to delta) (in-reverse-range from (+ to delta) delta)]))

;; ** Points

(define Point cons)

(define (list->point lst)
  (Point (first lst) (second lst)))

(define point-x car)
(define point-y cdr)

(define (point-map fn p1 p2)
  (Point (fn (car p1) (car p2))
         (fn (cdr p1) (cdr p2))))

;; convert a list of points (2 elements list) into
;; a list of pairs
(define (points->pairs lst)
  (map list->point lst))

;; ** Others

;; convert (vectorof (vectorof x)) to (listof (listof x))
(define (vector2d->list2d mat)
  (map vector->list (vector->list mat)))

;; reverse function of `vector2d->list2d`
(define (list2d->vector2d lst)
  (list->vector (map list->vector lst)))

(define (transpose lstlst)
  (apply map list lstlst))

;; list->hash : (listof pair) -> hash
(define (list->hash lst)
  (for/fold ([h (hash)])
            ([pair lst])
    (hash-set h (car pair) (cdr pair))))

(define (compare x y)
  (cond [(= x y) '=]
        [(< x y) '<]
        [else '>]))

;; make a alphabet list from lowercase a to z
(define (alphabet)
  (map integer->char
       (inclusive-range (char->integer #\a) (char->integer #\z))))

(define-syntax-rule (cons! lst element)
  (set! lst (cons element lst)))

(define (sum lst)
  (foldl + 0 lst))

(define (product lst)
  (foldl * 1 lst))

(define (maximum lst)
  (foldl max (car lst) lst))

(define (minimum lst)
  (foldl min (car lst) lst))

(define (digit-char->integer c)
  (- (char->integer c) (char->integer #\0)))

(define (lower-char->integer c)
  (- (char->integer c) (char->integer #\a)))

(define (integer->lower-char i)
  (integer->char (+ i (char->integer #\a))))

(define (uppercase-char->integer c)
  (- (char->integer c) (char->integer #\A)))

(define (scanl proc init lst)
  (cons init
        (for/list ([v lst])
          (set! init (proc v init))
          init)))

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
             (for/list ([i n]
                        [val lst]
                        #:when (bitwise-bit-set? bits i))
               val))
           (set! bits (add1 bits))
           res]))
    (in-producer gen stop)))

(define (set->immutable s)
  (list->set (set->list s)))

(define (list2d-dims lstlst)
  (match lstlst
    ['()
     (values 0 0)]
    [(cons fst _rems)
     (values (length lstlst) (length fst))]))

(define (vector2d-dims vecvec)
  (define m (vector-length vecvec))
  (define n (if (= 0 m) 0 (vector-length (vector-ref vecvec 0))))
  (values m n))

;; faster group-by for sorted list (increasing/decreasing)
(define (group-by-consecutive key lst [same? equal?])
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

;; Return O(n^2) pairs of a list
(define (pairs lst)
  (define vec (list->vector lst))
  (define n (vector-length vec))
  (for*/list ([j n]
              [i j])
    (cons (vector-ref vec i) (vector-ref vec j))))

;; Return O(n^2) sublists of list `lst`
(define (sublists lst)
  (define (sublists-head lst)
    (match lst
      ['() '()]
      [(cons x xs)
       (cons (list x)
             (map (λ (rem) (cons x rem)) (sublists-head xs)))]))

  (match lst
    ['() '()]
    [(cons _ xs) (append (sublists-head lst) (sublists xs))]))

(define (string-reverse str)
  (list->string (reverse (string->list str))))

(define (generate-prime-table limit)
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
  (define ans (make-vector (vlen lst) -1))

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
      (cond [(char=? (sref str i) (sref str j))
             (aset! prefix i (add1 j))]
            [(= j 0)
             (void)]
            [else
             (loop (aref prefix (sub1 j)))])))
  (λ (i) (aref prefix i)))

(define (identity-matrix n)
  (for/vector ([i n])
    (for/vector ([j n])
      (if (= i j) 1 0))))

(define (matrix/* mat1 mat2)
  (define m (vlen mat1))
  (define n (vlen mat2))
  (for/vector ([i (in-range 0 m)])
    (for/vector ([j (in-range 0 n)])
      (for/sum ([k (in-range 0 n)])
        (* (aref mat1 i k) (aref mat2 k j))))))

;; O(log n) matrix exponent operation
;; unsually used in some algorithms like
;; O(log n) fibonacci function.
(define (matrix-expmod mat p modfn)
  (cond [(= p 0)
         (identity-matrix (vlen (aref mat 0)))]
        [else
         (define mat/2 (matrix-expmod mat (quotient p 2) modfn))
         (define ans (if (odd? p)
                         (matrix/* mat (matrix/* mat/2 mat/2))
                         (matrix/* mat/2 mat/2)))
         (for/vector ([row ans])
           (for/vector ([v row])
             (modfn v)))]))

;; * Syntax

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


;; cache the procedure using a hash table
;; usage: just replace (define something ...) with (define/cache something ...)
(define-syntax-parser define/cache
  [(_ (fname:id args:id ...)
      body ...)
   #'(define fname
       (letrec ([cache (make-hash)]
                [fn
                 (λ (args ...)
                   body ...)]
                [fname
                 (λ (args ...)
                   (define key (list args ...))
                   (cond [(hash-has-key? cache key)
                          (hash-ref cache key)]
                         [else
                          (define val (fn args ...))
                          (hash-set! cache key val)
                          val]))])
         fname))])

;; cache the procedure using vectors
(define-syntax-parser define/cache-vec
  [(_ (fname:id args:id ...) (dims ... init)
      transformer
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(args ...))])
     #'(define fname
         (letrec ([cache (make-array dims ... init)]
                  [to-index transformer]
                  [fn
                   (λ (args ...)
                     body ...)]
                  [fname
                   (λ (args ...)
                     (define-values (inames ...) (to-index args ...))
                     (when (= init (aref cache inames ...))
                       (aset! cache inames ... (fn args ...)))
                     (aref cache inames ...))])
           fname)))])

;; cache the procedure using fixnum vectors
(define-syntax-parser define/cache-fxvec
  [(_ (fname:id args:id ...) (dims ... init)
      transformer
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(args ...))])
     #'(define fname
         (letrec ([cache (make-fxvector (* dims ...) init)]
                  [to-index transformer]
                  [fn
                   (λ (args ...)
                     body ...)]
                  [hs (list dims ...)]
                  [real-dims (cdr (reverse (scanl * 1 (reverse hs))))]
                  [args->index
                   (λ ps
                     (for/sum ([p (in-list ps)]
                               [d (in-list real-dims)])
                       (* p d)))]
                  [fname
                   (λ (args ...)
                     (define-values (inames ...) (to-index args ...))
                     (define index (args->index inames ...))
                     (when (= init (fxvector-ref cache index))
                       (fxvector-set! cache index (fn args ...)))
                     (fxvector-ref cache index))])
           fname)))])


(define-syntax-rule (run-once! fn)
  (set! fn (run-once fn)))

(define (run-once fn)
  (let ([has (mutable-set)])
    (lambda args
      (when (not (set-member? has args))
        (set-add! has args)
        (apply fn args)))))

(define-syntax-parse-rule (run-once-vec! fn:id hints:expr ...)
  (set! fn (run-once-vec fn hints ...)))

(define-syntax-parser run-once-vec
  [(_ fn:id hints:expr ...)
   (with-syntax ([(args ...) (generate-temporaries #'(hints ...))])
     #'(let* ([cache (make-array hints ... #f)]
              [ori-fn fn])
         (lambda (args ...)
           (when (eq? #f (aref cache args ...))
             (aset! cache args ... #t)
             (ori-fn args ...)))))])

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
  (set! fn (log-call-times (quote fn) fn)))

;; return a new function that same with `fn`,
;; but record the number of calls, and can obtain
;; it by running `(fn 'query)` or log by `(fn 'log)`.
(define (log-call-times name fn)
  (let ([cnt 0])
    (define (call . args)
      (set! cnt (add1 cnt))
      (apply fn args))

    (define (dispatch . args)
      (match args
        ['(query) cnt]
        ['(log) (displayln (format "~a: called ~a times" name cnt))]
        [_ (apply call args)]))
    dispatch))

;; statistic function `fn`
;; use `(fn 'log)` to print the results
(define-syntax-rule (statistic! fn)
  (set! fn (statistic (quote fn) fn)))

(define (statistic name fn)
  (let ([cnt 0]
        [arg-set (mutable-set)]
        [res-set (mutable-set)]
        [cpu-time 0]
        [real-time 0]
        [gc-time 0]
        [max-rec-depth 0]
        [rec-depth 0])
    (define (call args)
      (set-add! arg-set args)
      (set! cnt (add1 cnt))

      (set! rec-depth (add1 rec-depth))
      (set! max-rec-depth (max max-rec-depth rec-depth))
      (define-values (results cput realt gct)
        (time-apply fn args))
      (set! rec-depth (sub1 rec-depth))

      (when (zero? rec-depth)
        (set! cpu-time (+ cpu-time cput))
        (set! real-time (+ real-time realt))
        (set! gc-time (+ gc-time gct)))
      (set-add! res-set results)
      (apply values results))

    (define (dispatch . args)
      (match args
        ['(log)
         (displayln (format "'~a' statistic:" name))
         (displayln (format "    ~a distinct arguments" (set-count arg-set)))
         (displayln (format "    ~a distinct results" (set-count res-set)))
         (displayln (format "    ~a calls" cnt))
         (displayln (format "    ~a max recursion depth" max-rec-depth))
         (displayln (format "    ~a ms cpu time" cpu-time))
         (displayln (format "    ~a ms real time" real-time))
         (displayln (format "    ~a ms gc time" gc-time))]
        [_ (call args)]))
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

;; as function

;; make a function proxy for a vector or a hash table

(define-syntax-parser as-function1!
  [(_ (var:id args ...))
   #'(set! var
           (let ([old-var var])
             (cond [(vector? old-var)
                    (λ (args ...) (aref old-var args ...))]
                   [(hash? old-var)
                    (λ (x) (hash-ref old-var x))])))])

(define-syntax-parse-rule (as-function! spec ...)
  (let ()
    (as-function1! spec) ...))

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

(provide (all-defined-out))

