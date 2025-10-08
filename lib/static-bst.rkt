#lang racket

(provide (all-defined-out))

;; Static BST ;;

;; Binary Search Tree on a predefined sorted vector
;; The only usage is that it's much faster than
;; data/skip-list or data/splay-tree

(struct SBST
  (keys vals none))

;; make-sbst
;; Make a static binary search tree.
;; sorted-lst : sorted list
;; nothing : a value represents value absent in the tree
(define (make-sbst sorted-lst nothing)
  (define keys (list->vector sorted-lst))
  (SBST keys (make-vector (vector-length keys) nothing) nothing))

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

