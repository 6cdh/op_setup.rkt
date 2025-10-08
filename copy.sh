clipcopy () {
    if [ "$XDG_SESSION_TYPE" = "wayland" ]; then
        text=$(cat $1)
        wl-copy "$text"
    elif [ "$XDG_SESSION_TYPE" = "x11" ]; then
        xclip -in -selection clipboard < "${1:-/dev/stdin}"
    elif [ -x "$(command -v clip.exe)" ]; then
        iconv -f UTF-8 -t UTF-16LE "$1" | clip.exe
    else
        echo "no proper clipboard support for this platform"
    fi
}

racket bundler.rkt --separator run.rkt > output.rkt
clipcopy output.rkt
