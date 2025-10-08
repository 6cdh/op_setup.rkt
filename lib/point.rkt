#lang racket

(provide (all-defined-out))

;; Points ;;

(define Point cons)

(define (list->point lst)
  (Point (first lst) (second lst)))

(define Point-x car)
(define Point-y cdr)

(define (point-map fn p1 p2)
  (Point (fn (car p1) (car p2))
         (fn (cdr p1) (cdr p2))))

;; convert a list of points (2 elements list) into
;; a list of pairs
(define (points->pairs lst)
  (map list->point lst))
