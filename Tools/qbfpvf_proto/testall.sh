#!/bin/bash

INSTDIR="$HOME/opt/qbf/CheckedInstances-Eval10"
PROOFDIR="$HOME/opt/qbf/Proofs-Eval10"
LOGDIR="/tmp"
CHECK="./qbfpvf_proto"

function check() {
  INST="$1"
  BN="$(basename $INST)"
  BN="${BN%.*}"
  PROOF="$PROOFDIR/$BN.qrp"
  LOG="$LOGDIR/$BN.log"

  if test -f "$PROOF"; then
    echo -n "Checking $INST"
    if /usr/bin/time -f 'c TIMING %e s, %M kiB' $CHECK "$INST" "$PROOF" >"$LOG" 2>&1; then
      echo -ne "\033[1K\r"
      RES=$(grep '^s' $LOG)
      TIME=$(grep '^c TIMING' $LOG | sed -re 's/c TIMING//')
      echo "OK ($RES) [$TIME]: $INST"
    else
      echo -ne "\033[1K\r"
      echo "ERROR: $INST ($LOG)"
    fi
  else
    echo "NO PROOF: $INST"
  fi
}


for f in $INSTDIR/*.qdimacs; do check $f; done




