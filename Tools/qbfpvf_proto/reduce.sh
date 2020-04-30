#!/bin/bash

function error() {
  echo "Error: $1"
  exit 1
}

test $# -eq 1 || error "Usage reduce.sh ctrace-file"

TRACE=$1

test -f "$TRACE" || error "No such file $TRACE"

BASENAME="${TRACE%.ctrace}"

LOGFILE="$BASENAME.cqrp.log"
PROOF="$BASENAME.cqrp"

rm -rf "$LOGFILE"

COMMAND="./reduce $TRACE $PROOF"

echo "Date $(date)" >>"$LOGFILE"
echo "Machine $(uname -a)" >>"$LOGFILE"
echo "Command $COMMAND" >>"$LOGFILE"
echo "Log: $LOGFILE"


/usr/bin/time -a -o "$LOGFILE" -v $COMMAND 2>&1 | tee -a "$LOGFILE"
RESULT=$?

echo "Return code: $RESULT">>"$LOGFILE"

if test $RESULT -eq 0; then echo "REDUCED"
else echo "Error return code: $RESULT"
fi



