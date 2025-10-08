#lang racket

(provide (all-defined-out))

(require syntax/parse/define)
(require "array.rkt")

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

;; using dynamic growable vector to cache the procedure
(define-syntax-parser define/cache-dvec
  [(_ (fname:id args:id ...) (init)
      (transformers ...)
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(transformers ...))])
     #'(define fname
         (letrec ([cache #()]
                  [to-index (λ (args ...) (values transformers ...))]
                  [fn
                   (λ (args ...)
                     body ...)]
                  [fname
                   (λ (args ...)
                     (define-values (inames ...) (to-index args ...))
                     (define can-ref (can-ref? cache inames ...))
                     (define cached-val (if can-ref (aref cache inames ...) init))
                     (cond [(or (not can-ref) (equal? init cached-val))
                            (when (not can-ref)
                              (set! cache (aexpand! cache inames ... init)))
                            (define val (fn args ...))
                            (aset! cache inames ... val)
                            val]
                           [else cached-val]))])
           fname)))])

;; cache the procedure using vectors
(define-syntax-parser define/cache-vec
  [(_ (fname:id args:id ...) (dims ... init)
      transformer
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(dims ...))])
     #'(define fname
         (letrec ([cache (make-array dims ... init)]
                  [to-index (λ (args ...) transformer)]
                  [fn
                   (λ (args ...)
                     body ...)]
                  [fname
                   (λ (args ...)
                     (define-values (inames ...) (to-index args ...))
                     (when (equal? init (aref cache inames ...))
                       (aset! cache inames ... (fn args ...)))
                     (aref cache inames ...))])
           fname)))])


;; cache the procedure using vectors but call the original function
;; if the arguments can't fit dims...
(define-syntax-parser define/cache-vec-guard
  [(_ (fname:id args:id ...) (dims ... init)
      transformer
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(dims ...))])
     #'(define fname
         (letrec ([cache (make-array dims ... init)]
                  [to-index (λ (args ...) transformer)]
                  [fn
                   (λ (args ...)
                     body ...)]
                  [fname
                   (λ (args ...)
                     (cond [(or (< args 0) ...
                                (>= args dims) ...)
                            (fn args ...)]
                           [else
                            (define-values (inames ...) (to-index args ...))
                            (when (equal? init (aref cache inames ...))
                              (aset! cache inames ... (fn args ...)))
                            (aref cache inames ...)]))])
           fname)))])

(define-syntax-parser define/cache-vec1
  [(_ (fname:id args:id ...) (dim init)
      transformer
      body ...)
   #'(define fname
       (letrec ([cache (make-fxvector dim init)]
                [to-index (λ (args ...) transformer)]
                [fn
                 (λ (args ...)
                   body ...)]
                [fname
                 (λ (args ...)
                   (define iname (to-index args ...))
                   (when (= init (fxvector-ref cache iname))
                     (fxvector-set! cache iname (fn args ...)))
                   (fxvector-ref cache iname))])
         fname))])

;; cache the procedure using fixnum vectors
(define-syntax-parser define/cache-fxvec
  [(_ (fname:id args:id ...) (dims ... init)
      transformer
      body ...)
   (with-syntax ([(inames ...) (generate-temporaries #'(dims ...))])
     #'(define fname
         (letrec ([cache (make-fxvector (* dims ...) init)]
                  [to-index (λ (args ...) transformer)]
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
   #'(let ([arr2 (vector-ref arr (C idx ...))])
       (C1 arr2 then ...))]
  [(_ a op b then ...)
   #'(C1 (op a (C b)) then ...)])

