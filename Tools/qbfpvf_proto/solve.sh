#!/bin/bash
DIMACS="$1"
DEPQBF=~/devel/depqbf_mod/depqbf
DEPQBF_OPTIONS="--dep-man=simple --no-lazy-qpup --no-trivial-falsity --no-trivial-truth --no-dynamic-nenofex --no-qbce-dynamic"
TRACEDIR=~/opt/qbf/ctraces

TRACEFMT="compact"
TRACESFX="ctrace"


function error() {
  echo "Error: $1"
  exit 1
}



if test $# -eq 2; then

  case "$2" in
    compact) TRACEFMT="compact"; TRACESFX="ctrace" ;;
    qrp) TRACEFMT="qrp"; TRACESFX="trace" ;;
    bqrp) TRACEFMT="bqrp"; TRACESFX="btrace" ;;
    *) error "Unknown trace format $2" ;;
  esac

fi

DEPQBF_OPTIONS="$DEPQBF_OPTIONS --trace=$TRACEFMT"


mkdir -p $TRACEDIR


test -f "$DIMACS" || error "No such file: $DIMACS"

BASENAME="$(basename -s .qdimacs "$DIMACS")"

TRACE="$TRACEDIR/$BASENAME.$TRACESFX"
LOGFILE="$TRACE.log"

rm -rf "$LOGFILE"

COMMAND="$DEPQBF $DEPQBF_OPTIONS $DIMACS"

echo "Date $(date)" >>"$LOGFILE"
echo "Machine $(uname -a)" >>"$LOGFILE"
echo "Command $COMMAND" >>"$LOGFILE"

echo "Log: $LOGFILE"

/usr/bin/time -a -o "$LOGFILE" -v $COMMAND > "$TRACE" 2> >(tee -a "$LOGFILE" >&2)
RESULT=$?

echo "Return code: $RESULT">>"$LOGFILE"

if test $RESULT -eq 0; then echo "s UNSPEC"
elif test $RESULT -eq 10; then echo "s SAT"
elif test $RESULT -eq 20; then echo "s UNSAT"
else echo "Strange return code: $RESULT"
fi


