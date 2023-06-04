clipcopy () {
	# xclip -in -selection clipboard < "${1:-/dev/stdin}"
    text=$(cat $1)
    wl-copy "$text"
}

racket copier.rkt run.rkt > output.rkt
clipcopy output.rkt
