Here is a setup for competitive/online programming for Racket that I use mainly for Leetcode or CodeWars.

It aims to provide a workflow, not a lot of common used algorithms or data structures library though there are some common functions I prefer in `lib.rkt`.

# Workflows

1. You have your own style library `lib.rkt`.
2. Import `lib.rkt` in `run.rkt`, write code and test as usual.
3. Run `copy.sh` to copy your code from `run.rkt` and only necessary code from `lib.rkt` to the clipboard.
4. Paste your code into the browser.
5. Remove test code from the copied code if there are some.

In this way, you can write code without manually write or copy code from your library or share code with a lot of boilerplate code.

# Library

`lib.rkt` contains functions that some of them may attract you use Racket (or a lisp) on online programming platform:

* shorter and convenient multi-dimension vector utilities that are compatible with existing vector functions: `make-array`, `aset!`, `aref`, `aupd!`, ...
* debug macros that print expression and its value: `debugv`
* debug macros that hijack a function then print input/output/recursive calls: `debugf!`
* cache macros that hijack and automatically cache a recursive function use hash table, or a given multi-dimension vector for premature optimization: `cachef!`, `cache-hash`, `cache-vec1`, `cache-vec2`, ...
* assert macro so you can place it somewhere to make sure your code are correct: `assert`
* counter macro that hijack a function, and record the number of calls and return it when you need: `log-call-times!`
* threading macro with placeholder `%`: `~>`
* modulo macro that can modulo after any given operation: `modop`
* `C` macro that provide part of C like language experience, support nested infix expression, convenient bitwise operation operator, shorter assignment, send value to function chain in infix syntax.

# Note

* Your code should be correct to be copied otherwise the script will complain when analyze the dependency of your code.
* `copier.rkt` copies a file whose name is given from the command line and print code to stdout.
* By default, `#lang racket` is not copied. Use the `--langline` flag with `copier.rkt` to include it.
* By default, `copy.sh` copy code to clipboard under Wayland, write your own code if you are under X11 or other platform.
* modify or add your own functions to `lib.rkt`.

