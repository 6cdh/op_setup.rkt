#lang racket/base

(require drracket/check-syntax
         data/skip-list
         syntax/modread
         racket/list
         racket/class
         racket/file
         racket/set
         racket/match
         racket/port
         racket/string
         racket/cmdline)

(define info-collector%
  (class (annotations-mixin object%)
    (init-field src)
    (super-new)

    (define records '())

    (define/override (syncheck:find-source-object stx)
      (if (and (equal? (syntax-source stx) src)
               (syntax-original? stx))
          src
          #f))

    (define/override (syncheck:add-mouse-over-status obj start end str)
      (define obj (list 'syncheck:add-mouse-over-status start end str))
      (set! records (cons obj records)))

    (define/override (syncheck:add-definition-target obj start _finish id _mods)
      (define obj (list 'syncheck:add-definition-target start id))
      (set! records (cons obj records)))

    (define/override (syncheck:add-arrow _obj1
                                         def-left _def-right
                                         _obj2
                                         ref-left _ref-right
                                         _actual?
                                         _phase-level)
      (define obj (list 'syncheck:add-arrow def-left ref-left))
      (set! records (cons obj records)))

    (define/public (get-records)
      records)))

;; A import item means import `name` from `mod`.
(struct Import
  [name mod]
  #:transparent)

;; Top Level Form Data
(struct TLF
  [start
   end
   used-tlfs
   imports
   used?]
  #:mutable)

(struct FileData
  [code
   symbol->tlf
   tlfs
   deps])

;; files
(define *file->filedata* (make-hash))
(define *file->external-symbols* (make-hash))

(define (read-syntaxes code)
  (define port (open-input-string code))
  ;; make syntax-position counts in string
  (port-count-lines! port)
  (parameterize ([current-input-port port])
    (read-language)
    (port->list read-syntax)))

(define *base-ns* (make-base-namespace))

(define (read-check-syntax-records file code)
  (match-define-values (src-dir _ #f) (split-path file))
  (define-values (add-syntax done)
    (make-traversal *base-ns* #f))
  (define src 'current-file)
  (define info-collector (new info-collector% [src src]))
  (define in (open-input-string code))
  (port-count-lines! in)
  (parameterize ([current-annotations info-collector]
                 [current-namespace *base-ns*]
                 [current-load-relative-directory src-dir])
    (define expanded (expand
                       (with-module-reading-parameterization
                         (lambda () (read-syntax src in)))))
    (add-syntax expanded)
    (done))

  (send info-collector get-records))

(define (analyze-file file)
  (define code (file->string file))
  (match-define-values (file-dir _ #f) (split-path file))

  (define records (read-check-syntax-records file code))
  (define stxes (read-syntaxes code))
  (define position->tlf (make-adjustable-skip-list))

  (define tlfs
    (for/list ([stx stxes])
      (define start (sub1 (syntax-position stx)))
      (define end (+ start (syntax-span stx)))
      (define tlf (TLF start end (mutable-set) (mutable-set) #f))
      (skip-list-set! position->tlf start tlf)
      tlf))

  (define (locate-tlf pos)
    (define it (skip-list-iterate-greatest/<=? position->tlf pos))
    (skip-list-iterate-value position->tlf it))

  (define (locate-tlf-position pos)
    (define it (skip-list-iterate-greatest/<=? position->tlf pos))
    (skip-list-iterate-key position->tlf it))

  (define (in-same-tlf? pos1 pos2)
    (= (locate-tlf-position pos1) (locate-tlf-position pos2)))

  (define (in-this-module? pos)
    (skip-list-iterate-greatest/<=? position->tlf pos))

  (define symbol->tlf (make-hash))
  (for ([r records])
    (match r
      [(list 'syncheck:add-mouse-over-status start end msg)
       (define m (regexp-match #px"imported from \"(.*)\"" msg))
       ;; add a import item
       (when m
         (define mod-path (second m))
         (define sym (string->symbol (substring code start end)))
         (define imp (Import sym (build-path file-dir mod-path)))
         (define tlf (locate-tlf start))
         (define imports (TLF-imports tlf))
         (set-add! imports imp))]
      [(list 'syncheck:add-arrow to-pos from-pos)
       #:when (in-this-module? to-pos)
       ;; add a reference from a tlf to another tlf
       (define pos (locate-tlf-position from-pos))
       (unless (in-same-tlf? pos to-pos)
         (define from-tlf (locate-tlf from-pos))
         (define to-tlf (locate-tlf to-pos))
         (define used (TLF-used-tlfs from-tlf))
         (set-add! used to-tlf))]
      [(list 'syncheck:add-definition-target start sym)
       ;; add a symbol definition
       (hash-set! symbol->tlf sym (locate-tlf start))]
      [_ (void)]))

  (FileData code (λ (sym) (hash-ref symbol->tlf sym)) tlfs (mutable-set)))

(define (analyze-main-file filepath)
  (define filedata (analyze-file filepath))
  (hash-set! *file->filedata* filepath filedata)
  (define tlfs (FileData-tlfs filedata))
  (define deps (FileData-deps filedata))
  (define imports (mutable-set))
  (for ([tlf tlfs])
    (set-union! imports (TLF-imports tlf))
    (for ([imp (TLF-imports tlf)])
      (set-add! deps (Import-mod imp))))
  imports)

;; For the used symbols those are defined in `file`.
;; add their dependency functions and dependency files.
;; And update the dependency files recursively.
(define (update-dependency file)
  (when (not (hash-has-key? *file->filedata* file))
    (hash-set! *file->filedata* file (analyze-file file)))
  (define filedata (hash-ref *file->filedata* file))
  (define deps (FileData-deps filedata))
  (define pending-mods (mutable-set))

  (define (add-to-copy tlf)
    (unless (TLF-used? tlf)
      (set-TLF-used?! tlf #t)

      (for ([imp (TLF-imports tlf)])
        (define name (Import-name imp))
        (define mod (Import-mod imp))
        (set-add! deps mod)
        (define mod-used-syms (hash-ref! *file->external-symbols* mod (mutable-set)))
        (when (not (set-member? mod-used-syms name))
          (set-add! mod-used-syms name)
          (set-add! pending-mods mod)))

      (for ([next (TLF-used-tlfs tlf)])
        (add-to-copy next))))

  (define syms (hash-ref *file->external-symbols* file))
  (define symbol->tlf (FileData-symbol->tlf filedata))
  (for ([sym syms])
    (add-to-copy (symbol->tlf sym)))

  (for ([mod pending-mods])
    (update-dependency mod)))

(define skip-list-update!
  (case-lambda
    [(sl key fn)
     (skip-list-set! sl key
                     (fn (skip-list-ref sl key)))]
    [(sl key fn default)
     (skip-list-set! sl key
                     (fn (skip-list-ref sl key default)))]))

;; topological sort files
(define (sort-files)
  (define ins (make-hash))
  (define outs (make-hash))
  (for* ([(f filedata) *file->filedata*])
    (define deps (FileData-deps filedata))
    (hash-set! ins f (set->list deps))
    (for ([dep deps])
      (hash-update! outs dep (λ (old) (set-add! old f) old) (mutable-set))))

  (define file->degree (make-hash))
  (define degree->files (make-adjustable-skip-list))
  (for ([(file ref-files) ins])
    (define degree (length ref-files))
    (hash-set! file->degree file degree)
    (skip-list-update! degree->files degree
                       (λ (old) (set-add! old file) old)
                       (mutable-set)))

  (define (remove-file! key file)
    (define val (skip-list-ref degree->files key))
    (set-remove! val file)
    (when (set-empty? val)
      (skip-list-remove! degree->files key)))

  (for/list ([_ (hash-count ins)])
    (define mini-it (skip-list-iterate-least degree->files))
    (define mini-degree (skip-list-iterate-key degree->files mini-it))
    (unless (= 0 mini-degree)
      (error "cyclic dependency in file dependencies"))

    (define f (set-first (skip-list-ref degree->files mini-degree)))
    (remove-file! mini-degree f)

    (for ([ref-file (hash-ref outs f '())])
      (define degree (hash-ref file->degree ref-file))
      (hash-update! file->degree ref-file sub1)
      (remove-file! degree ref-file)

      (skip-list-update! degree->files (sub1 degree)
                         (λ (old) (set-add! old ref-file) old)
                         (mutable-set)))
    f))

(define (copy-symbols filedata)
  (for/list ([tlf (FileData-tlfs filedata)]
             #:when (TLF-used? tlf))
    (substring (FileData-code filedata) (TLF-start tlf) (TLF-end tlf))))

(define (clear-original-code code)
  (define no-local-require (regexp-replace* #px"\\(\\s*require\\s+\".*?\n" code ""))
  (define lang-line (first (regexp-match #px"#lang .*?\n" no-local-require)))
  (define no-langline (regexp-replace #px"#lang .*?\n" no-local-require ""))
  (values lang-line (string-trim no-langline)))

(define (remove-requires code deps)
  (define-values (lang-line rawcode) (clear-original-code code))
  (define full-code
    (cond [(andmap char-whitespace? (string->list deps))
           rawcode]
          [(lib-sep?)
           (string-append
             ";; === library START ===\n\n"
             deps "\n\n"
             ";; === library END ===\n\n"
             rawcode)]
          [else
           (string-append deps "\n\n" rawcode)]))
  (if (lang-line?)
      (string-append lang-line "\n" full-code)
      full-code))

(define (main filename)
  ;; Build a directed graph of files that each node is a file containing its required symbols
  ;; that need to copy later.
  ;; Then topological sort the graph to get the order of files to copy.
  ;; Then copy the files in order.

  (define filepath (path->complete-path filename))
  (define imports (analyze-main-file filepath))
  (for ([imp imports])
    (hash-update! *file->external-symbols*
                  (Import-mod imp)
                  (λ (old) (set-add! old (Import-name imp)) old)
                  (mutable-set))
    (update-dependency (Import-mod imp)))

  (define sorted-files (sort-files))
  (define copied
    (for/list ([file sorted-files])
      (copy-symbols (hash-ref *file->filedata* file))))

  (define copied-no-require
    (for*/list ([codes copied]
                [tlf-str codes]
                #:when (not (regexp-match? #px"^\\s*\\(\\s*require\\s+\"" tlf-str)))
      tlf-str))

  (define final-code
    (string-append
      (string-trim
        (remove-requires (FileData-code (hash-ref *file->filedata* filepath))
                         (string-join copied-no-require "\n\n")))
      "\n"))

  (display final-code))

(define lang-line? (make-parameter #f))
(define lib-sep? (make-parameter #f))
(define filename
  (command-line
    #:once-each
    [("--langline")
     ("copy `#lang racket` line"
      "default: no")
     (lang-line? #t)]
    [("--separator")
     ("insert library separator comment"
      "default: no")
     (lib-sep? #t)]

    #:args (filename)
    filename))

(main filename)

