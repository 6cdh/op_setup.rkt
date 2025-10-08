#lang racket

(provide (all-defined-out))

(require racket/fixnum)

;; ASCII Char Table ;;

(define (make-char-table init)
  (make-fxvector 256 init))

(define (char-table-ref abt c)
  (fxvector-ref abt (char->integer c)))

(define (char-table-set! abt c val)
  (fxvector-set! abt (char->integer c) val))

(define (char-table-update! abt c updater)
  (define i (char->integer c))
  (fxvector-set! abt i (updater (fxvector-ref abt i))))

