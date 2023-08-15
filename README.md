Here is a setup for competitive/online programming for Racket that I use mainly for Leetcode or CodeWars.

It aims to provide a workflow, not a lot of common used algorithms or data structures library though there are some common functions I prefer in `lib.rkt`.

## Workflow

1. You have your own style library in `lib.rkt`.
2. In `run.rkt`, require `lib.rkt`. Then write code and test your code as usual.
3. Run `copy.sh` to copy your code from `run.rkt` and only the necessary code from `lib.rkt` to `output.rkt`. Then it will be copied to your clipboard.
4. Paste your code into the browser.
5. If there is any test code in the copied code, remove it.

In this way, you can write code without manually write or copy code from your library or share code with a lot of boilerplate code.

## Requirements

* Racket
* A tool for copying to the clipboard
  * wl-clipboard on Wayland
  * xclip on X11

Other platforms are not supported because I don't use them and can't test it. Feel free to open a issue if you have suggestion for other platforms.

## Note

* Your code must be correct in order to be copied otherwise the script will complain when analyze the dependency of your code.
* By default, `#lang racket` is not copied. Use the `--langline` flag with `copier.rkt` to include it.
* the current copy time is ~2s, you can run `raco make check-syntax.rkt` to reduce it to 1.4s.

## Library

`lib.rkt` contains functions that some of them may attract you use Racket (or a lisp) on online programming platform:

* shorter and convenient multi-dimension vector utilities that are compatible with existing vector functions: `make-array`, `aset!`, `aref`, `aupd!`, ...
* debug macros that print expression and its value: `debugv`
* debug macros that hijack a function then print input/output/recursive calls: `debugf!`
* cache macros that hijack and automatically cache a recursive function use hash table, or a vector for premature optimization if you provide enough hints: `cachef!`
* assert macro so you can place it somewhere to make sure your code are correct: `assert`
* counter macro that hijack a function, and record the number of calls and return it when you need: `log-call-times!`
* threading macro: `~>`
* modulo macro that modulo nested expression: `lc-mod`
* `C` macro that provide part of C like language experience, support nested infix expression, convenient bitwise operation operator, C style assignment.

## License

The `check-syntax.rkt` and files under `private/` are belong to [drracket](https://github.com/racket/drracket). It's under Apache v2 and MIT license.

