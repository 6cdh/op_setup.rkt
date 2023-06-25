clipcopy () {
    if [ "$XDG_SESSION_TYPE" = "wayland" ]; then
        text=$(cat $1)
        wl-copy "$text"
    elif [ "$XDG_SESSION_TYPE" = "x11" ]; then
        xclip -in -selection clipboard < "${1:-/dev/stdin}"
    else
        echo "unknown session type: \$XDG_SESSION_TYPE = $XDG_SESSION_TYPE"
    fi
}

racket copier.rkt run.rkt > output.rkt
clipcopy output.rkt
