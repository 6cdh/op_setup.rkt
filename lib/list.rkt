#lang racket

(provide (all-defined-out))

;; Faster versions of first, second, third, ...
(define list-first car)
(define list-second cadr)
(define list-third caddr)

(define (list-scanl proc init lst)
  (cons init
        (for/list ([v (in-list lst)])
          (set! init (proc v init))
          init)))

(define (list-sum lst)
  (foldl + 0 lst))

(define (list-product lst)
  (foldl * 1 lst))

(define (list-maximum lst)
  (foldl max (car lst) lst))

(define (list-minimum lst)
  (foldl min (car lst) lst))

(define (take-atmost lst k)
  (cond [(= k 0) '()]
        [(null? lst) '()]
        [else (cons (car lst) (take-atmost (cdr lst) (sub1 k)))]))

(define (list-scanr proc init lst)
  (reverse
    (for/list ([v (in-list (reverse lst))])
      (set! init (proc v init))
      init)))

(define (sublist lst from to)
  (drop (take lst to) from))

(define (transpose lstlst)
  (apply map list lstlst))

;; list->hash : (listof pair) -> hash
(define (list->hash lst)
  (for/fold ([h (hash)])
            ([pair (in-list lst)])
    (hash-set h (car pair) (cdr pair))))

(define (list-compare lst1 lst2 [less? <])
  (match* (lst1 lst2)
    [('() '()) '=]
    [('() _) '<]
    [(_ '()) '>]
    [((cons x1 r1) (cons x2 r2))
     (cond [(less? x1 x2) '<]
           [(less? x2 x1) '>]
           [else (list-compare r1 r2 less?)])]))

(define (pair-compare p1 p2 [less? <])
  (match* (p1 p2)
    [((cons x1 y1) (cons x2 y2))
     (cond [(less? x1 x2) '<]
           [(less? x2 x1) '>]
           [(less? y1 y2) '<]
           [(less? y2 y1) '>]
           [else '=])]))

(define (list=? l1 l2 [less? <])
  (eq? '= (list-compare l1 l2 less?)))

(define (list<? l1 l2 [less? <])
  (eq? '< (list-compare l1 l2 less?)))

(define (list>? l1 l2 [less? <])
  (eq? '> (list-compare l1 l2 less?)))

(define (pair=? p1 p2 [less? <])
  (eq? '= (pair-compare p1 p2 less?)))

(define (pair<? p1 p2 [less? <])
  (eq? '< (pair-compare p1 p2 less?)))

(define (pair>? p1 p2 [less? <])
  (eq? '> (pair-compare p1 p2 less?)))

(define (list2d-dims lstlst)
  (match lstlst
    ['()
     (values 0 0)]
    [(cons fst _rems)
     (values (length lstlst) (length fst))]))

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
