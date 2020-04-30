#!/bin/bash

DIMACS=$1
TRACEDIR=~/opt/qbf/ctraces

function error() {
  echo "Error: $1"
  exit 1
}

test $# -eq 1 || error "Usage verify.sh qdimacs-file"

test -f "$DIMACS" || error "No such file: $DIMACS"

BASENAME="$(basename -s .qdimacs "$DIMACS")"

PROOF="$TRACEDIR/$BASENAME.cqrp"
LOGFILE="$TRACEDIR/$BASENAME.verify.log"

test -f "$PROOF" || error "No such file: $PROOF"

rm -rf "$LOGFILE"

COMMAND="./verify $DIMACS $PROOF"

echo "Date $(date)" >>"$LOGFILE"
echo "Machine $(uname -a)" >>"$LOGFILE"
echo "Command $COMMAND" >>"$LOGFILE"
echo "Log: $LOGFILE"


/usr/bin/time -a -o "$LOGFILE" -v $COMMAND >>"$LOGFILE" 2>&1
RESULT=$?

echo "Return code: $RESULT">>"$LOGFILE"

if test $RESULT -eq 0; then echo "VERIFIED"
else echo "Error return code: $RESULT"
fi

