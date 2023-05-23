clipcopy () {
	# xclip -in -selection clipboard < "${1:-/dev/stdin}"
    wl-copy < $1
}

racket copier.rkt run.rkt > output.rkt
clipcopy output.rkt
