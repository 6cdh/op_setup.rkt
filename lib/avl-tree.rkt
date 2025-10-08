#lang racket

(provide make-avl-tree
         avl-tree?
         avl-tree-ref
         avl-tree-has-key?
         avl-tree-update!
         avl-tree-set!
         avl-tree-remove!
         avl-tree-count
         avl-tree->list
         avl-tree-iter?
         avl-tree-iterate-key
         avl-tree-iterate-value
         avl-tree-iterate-least/>?
         avl-tree-iterate-least/>=?
         avl-tree-iterate-least
         avl-tree-iterate-greatest/<?
         avl-tree-iterate-greatest/<=?
         avl-tree-iterate-greatest
         avl-tree-iterate-next)

(require "utils.rkt")
(require racket/generator)

;; AVL Tree
;; alternative to data/skip-list or data/splay-tree but faster
;; provides similar interface as data/skip-list, but does not
;; support dictionary interface.
;; Only support number as key.

(struct AVLNode
  (value height left right))

(define (AVL-balance-factor tree)
  (match tree
    [#f 0]
    [(AVLNode _ _ left right)
     (- (AVL-height right) (AVL-height left))]))

(define (AVL-height tree)
  (match tree
    [#f 0]
    [_ (AVLNode-height tree)]))

(define (AVL val left right)
  (AVLNode val (add1 (max (AVL-height left) (AVL-height right))) left right))

(define (AVL-rotate-left tree)
  (match tree
    [(AVLNode a _ b (AVLNode c _ d e))
     (AVL c (AVL a b d) e)]))

(define (AVL-rotate-right tree)
  (match tree
    [(AVLNode a _ (AVLNode b _ c d) e)
     (AVL b c (AVL a d e))]))

(define (AVL-rotate-right-left tree)
  (match tree
    [(AVLNode a _ b (AVLNode c _ (AVLNode d _ e f) g))
     (AVL d (AVL a b e) (AVL c f g))]))

(define (AVL-rotate-left-right tree)
  (match tree
    [(AVLNode a _ (AVLNode b _ c (AVLNode d _ e f)) g)
     (AVL d (AVL b c e) (AVL a f g))]))

(define (AVL-balance tree)
  (cond [(and (= -2 (AVL-balance-factor tree))
              (= 1 (AVL-balance-factor (AVLNode-left tree))))
         (AVL-rotate-left-right tree)]
        [(= -2 (AVL-balance-factor tree))
         (AVL-rotate-right tree)]
        [(and (= 2 (AVL-balance-factor tree))
              (= -1 (AVL-balance-factor (AVLNode-right tree))))
         (AVL-rotate-right-left tree)]
        [(= 2 (AVL-balance-factor tree))
         (AVL-rotate-left tree)]
        [else tree]))

(define (AVL-update tree key updater default root)
  (match tree
    [#f
     (set-AVLRoot-size! root (add1 (AVLRoot-size root)))
     (AVL (cons key (updater default)) #f #f)]
    [(AVLNode pair _ left right)
     (match (compare key (car pair))
       ['= (AVL (cons key (updater (cdr pair))) left right)]
       ['< (AVL-balance (AVL pair (AVL-update left key updater default root) right))]
       ['> (AVL-balance (AVL pair left (AVL-update right key updater default root)))])]))

(define (AVL-ref tree key default)
  (match tree
    [#f default]
    [(AVLNode pair _ left right)
     (match (compare key (car pair))
       ['= (cdr pair)]
       ['< (AVL-ref left key default)]
       ['> (AVL-ref right key default)])]))

(define (AVL-remove tree key root)
  (match tree
    [#f #f]
    [(AVLNode pair _ left right)
     (match (compare key (car pair))
       ['= (set-AVLRoot-size! root (sub1 (AVLRoot-size root)))
           (AVL-merge left right)]
       ['< (AVL-balance (AVL pair (AVL-remove left key root) right))]
       ['> (AVL-balance (AVL pair left (AVL-remove right key root)))])]))

(define (AVL-merge left right)
  (match* (left right)
    [(#f right) right]
    [(left #f) left]
    [(left right)
     (define-values (min-pair new-right) (AVL-extract-min right))
     (AVL-balance (AVL min-pair left new-right))]))

(define (AVL-extract-min tree)
  (match tree
    [(AVLNode p _ #f right)
     (values p right)]
    [(AVLNode p _ left right)
     (define-values (min-pair new-left) (AVL-extract-min left))
     (values min-pair (AVL-balance (AVL p new-left right)))]))

(struct AVLRoot
  (size node)
  #:mutable)

(define (make-avl-tree)
  (AVLRoot 0 #f))

(define avl-tree? AVLRoot?)

(define *none* (gensym 'none))

(define (avl-tree-ref avl key [default *none*])
  (define val (AVL-ref (AVLRoot-node avl) key default))
  (if (eq? val *none*)
      (error 'avl-tree-ref "no value found for key ~v" key)
      val))

(define (avl-tree-has-key? avl key)
  (define notfound (gensym 'notfound))
  (not (eq? notfound (avl-tree-ref avl key notfound))))

(define (avl-tree-update! avl key updater [default *none*])
  (set-AVLRoot-node! avl (AVL-update (AVLRoot-node avl) key updater default avl))
  (void))

(define (avl-tree-set! avl key val)
  (avl-tree-update! avl key (λ (_) val) val))

(define (avl-tree-remove! avl key)
  (set-AVLRoot-node! avl (AVL-remove (AVLRoot-node avl) key avl))
  (void))

(define (avl-tree-count avl)
  (AVLRoot-size avl))

(define (avl-tree->list avl)
  (define gen
    (generator ()
      (let rec ([node (AVLRoot-node avl)])
        (match node
          [#f (void)]
          [(AVLNode kv _ left right)
           (rec left)
           (yield kv)
           (rec right)]))))

  (for/list ([v (in-producer gen (void))])
    v))

(struct AVL-Iter
  (stack))

(define (make-avl-iter)
  (AVL-Iter '()))

(define (AVL-iter-push iter node)
  (AVL-Iter (cons node (AVL-Iter-stack iter))))

(define avl-tree-iter? AVL-Iter?)

(define (avl-tree-iterate-next avl iter)
  (define (up node parents)
    (match parents
      ['() #f]
      [(cons p rest)
       (if (eq? node (AVLNode-left p))
           (AVL-Iter parents)
           (up p rest))]))

  (define (down p parents)
    (define left (AVLNode-left p))
    (if (false? left)
        (AVL-Iter (cons p parents))
        (down left (cons p parents))))

  (match (AVL-Iter-stack iter)
    ['() #f]
    [(and stack (cons node parents))
     (define right (AVLNode-right node))
     (if (false? right)
         (up node parents)
         (down right stack))]))

(define (avl-tree-iterate-key avl iter)
  (car (AVLNode-value (car (AVL-Iter-stack iter)))))

(define (avl-tree-iterate-value avl iter)
  (cdr (AVLNode-value (car (AVL-Iter-stack iter)))))

(define (avl-tree-iterate-least-ok avl ok?)
  (define (leftmost node iter)
    (match node
      [#f #f]
      [(AVLNode (cons key _) _ left right)
       (define iter2 (AVL-iter-push iter node))
       (if (ok? key)
           (let ([lm (leftmost left iter2)])
             (if (false? lm)
                 iter2
                 lm))
           (leftmost right iter2))]))

  (leftmost (AVLRoot-node avl) (make-avl-iter)))

(define (avl-tree-iterate-greatest-ok avl ok?)
  (define (rightmost node iter)
    (match node
      [#f #f]
      [(AVLNode (cons key _) _ left right)
       (define iter2 (AVL-iter-push iter node))
       (if (ok? key)
           (let ([rm (rightmost right iter2)])
             (if (false? rm)
                 iter2
                 rm))
           (rightmost left iter2))]))

  (rightmost (AVLRoot-node avl) (make-avl-iter)))

(define (avl-tree-iterate-least/>? avl key)
  (avl-tree-iterate-least-ok avl (λ (k) (> k key))))

(define (avl-tree-iterate-least/>=? avl key)
  (avl-tree-iterate-least-ok avl (λ (k) (>= k key))))

(define (avl-tree-iterate-least avl)
  (avl-tree-iterate-least-ok avl (λ (_) #t)))

(define (avl-tree-iterate-greatest/<? avl key)
  (avl-tree-iterate-greatest-ok avl (λ (k) (< k key))))

(define (avl-tree-iterate-greatest/<=? avl key)
  (avl-tree-iterate-greatest-ok avl (λ (k) (<= k key))))

(define (avl-tree-iterate-greatest avl)
  (avl-tree-iterate-greatest-ok avl (λ (_) #t)))

