#lang racket/base

(require "check-syntax.rkt"
         data/skip-list
         syntax/modread
         racket/class
         racket/file
         racket/set
         racket/match
         racket/port
         racket/string
         racket/cmdline)

(define *lib* "lib.rkt")

(define info-collector%
  (class (annotations-mixin object%)
    (init-field src)
    (super-new)

    (define cont '())

    (define/override (syncheck:find-source-object stx)
      (if (and (equal? (syntax-source stx) src)
               (syntax-original? stx))
          src
          #f))

    (define/override (syncheck:add-mouse-over-status obj start end str)
      (define obj (list 'syncheck:add-mouse-over-status start end str))
      (set! cont (cons obj cont)))

    (define/override (syncheck:add-definition-target obj start _finish id _mods)
      (define obj (list 'syncheck:add-definition-target start id))
      (set! cont (cons obj cont)))

    (define/override (syncheck:add-arrow _obj1
                                         def-left _def-right
                                         _obj2
                                         ref-left _ref-right
                                         _actual?
                                         _phase-level)
      (define obj (list 'syncheck:add-arrow def-left ref-left))
      (set! cont (cons obj cont)))

    (define/public (get-cont)
      cont)))

(define (analyze text)
  (define base-ns (make-base-namespace))
  (define-values (add-syntax done)
    (make-traversal base-ns #f))
  (define src 'current-file)
  (define info-collector (new info-collector% [src src]))
  (define in (open-input-string text))
  (port-count-lines! in)
  (parameterize ([current-annotations info-collector]
                 [current-namespace base-ns])
    (define expanded (expand
                      (with-module-reading-parameterization
                        (lambda () (read-syntax src in)))))
    (add-syntax expanded)
    (done))

  (send info-collector get-cont))

(define (find-used-syms filename)
  (define code (file->string filename))

  (define need-copy-syms (mutable-set))
  (define cont (analyze code))

  (for ([c cont])
    (match c
      [(list 'syncheck:add-mouse-over-status start end str)
       (when (string=? str (format "imported from ~v" *lib*))
         (set-add! need-copy-syms
                   (string->symbol (substring code start end))))]
      [_ (void)]))
  need-copy-syms)

(define (copy-used need-copy-syms lib)
  (define (read-top-level-defs code)
    (define port (open-input-string code))
    ;; make syntax-position counts in string
    (port-count-lines! port)
    (parameterize ([current-input-port port])
      (read-language)
      (port->list read-syntax)))

  (define code (file->string lib))

  (define stxes (read-top-level-defs code))
  (define cont (analyze code))

  (define marked-set (mutable-set))
  (define sorted-top-level-poses (make-skip-list))

  (for ([stx stxes])
    (skip-list-set! sorted-top-level-poses
                    (sub1 (syntax-position stx))
                    #t))

  (define (top-level-start-pos pos)
    (define it (skip-list-iterate-greatest/<=? sorted-top-level-poses pos))
    (skip-list-iterate-key sorted-top-level-poses it))

  (define (mark-copy! pos)
    (set-add! marked-set (top-level-start-pos pos)))

  (define (marked? pos)
    (set-member? marked-set (top-level-start-pos pos)))

  (define (same-top-level? pos1 pos2)
    (= (top-level-start-pos pos1)
       (top-level-start-pos pos2)))

  (define (in-this-module? pos)
    (skip-list-iterate-greatest/<=? sorted-top-level-poses pos))

  (define (mark-rec! pos)
    (when (not (marked? pos))
      (mark-copy! pos)
      (for ([c cont])
        (match c
          [(list 'syncheck:add-arrow def-start ref-start)
           (when (and (in-this-module? def-start)
                      (same-top-level? pos ref-start)
                      (not (same-top-level? pos def-start)))
             (mark-rec! def-start))]
          [_ (void)]))))

  (for ([c cont])
    (match c
      [(list 'syncheck:add-definition-target start id)
       (when (set-member? need-copy-syms id)
         (mark-rec! start))]
      [_ (void)]))

  (string-join
   (for*/list ([stx stxes]
               [pos (in-value (sub1 (syntax-position stx)))]
               #:when (marked? pos))
     (substring code pos (+ pos (syntax-span stx))))
   "\n\n"))

(let* ([lang-line (make-parameter #f)]
       [filename (command-line #:once-any
                               [("--langline") ("copy `#lang racket` line"
                                                "default: no")
                                               (lang-line #t)]
                               #:args (filename)
                               filename)]
       [code (file->string filename)]
       [used-syms (find-used-syms filename)]
       [copied-code (copy-used used-syms *lib*)]
       [removed (list (format "(require ~v)\n" *lib*)
                      (if (lang-line)
                          ""
                          "#lang racket\n"))])
  (displayln
   (string-append
    (string-trim
     (for/fold ([replaced (string-append code "\n" copied-code)])
               ([rep removed])
       (string-replace replaced rep "")))
    "\n")))

