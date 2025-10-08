Here is a setup for share code for Racket that I use mainly for Leetcode or CodeWars.

## What is it

When You need to share or submit a piece of code, but your code are distributed across multiple files. You want to bundle your code and necessary dependency into one file and copy it. Then this setup is for you.

## How to use

1. Put your main code in `run.rkt` that executes directly.
2. Require your library through `(require "path/to/file.rkt")` in `run.rkt`.
3. Run `copy.sh`. It will analyze your code in `run.rkt`, and copy necessary dependency from your other local files, then write them into `output.rkt` and copy it to your clipboard.
4. You can share it now!

## Requirements

- Racket
- A tool for copying to the clipboard
  - wl-clipboard on Wayland
  - xclip on X11

For Windows, only WSL is supported. You need to install Racket in WSL and run `copy.sh` there.

Other platforms are not supported because I don't use them and can't test it. Feel free to open a issue if you have suggestion for other platforms.

## Note

- Your code must be correct in order to be copied otherwise the script will complain when analyze the dependency of your code.
- By default, `#lang racket` is not copied. Use the `--langline` flag with `bundler.rkt` to include it.

## Bundler

`bundler.rkt` is a bundler that actually does the job.

```shell
# analyze file.rkt and print the bundled code to stdout.
racket bundler.rkt file.rkt
```

`bundler.rkt` can accept two flags, use `racket bundler.rkt -h` for more information.

## Library

`lib` contains functions that some of them may attract you use Racket (or a lisp) on online judge platform:

- shorter and convenient multi-dimension vector utilities that are compatible with existing vector functions: `make-array`, `aset!`, `aref`, `aupd!`, ...
- debug macros that print expression and its value: `P`.
- debug macros that hijack a function then print input/output/recursive calls: `debugf!`.
- cache macros that defines a recursive function use hash table for cache, or a vector for premature optimization if you provide enough hints: `define/cache` and `define/cache-vec`.
- assert macro so you can place it somewhere to make sure your code are correct: `assert`.
- counter macro that hijack a function, and record the number of calls and return it when you need: `log-call-times!`.
- threading macro: `~>`.
- modulo macro that modulo nested expression: `lc-mod`.
- `C` macro that provide part of C like language experience, support nested infix expression, convenient bitwise operation operator, C style assignment.
- hijack macro that wraps a function, record the number of calls, max recursion depth, the number of distinct arguments, cpu time and gc time of this function: `statistic!`.
