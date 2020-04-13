#!/bin/bash

INSTDIR="testdb/instances"
PROOFDIR="$HOME/opt/qbf/proofs"
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
    if $CHECK "$INST" "$PROOF" >"$LOG" 2>&1; then
      echo -ne "\033[1K\r"
      RES=$(grep '^s' $LOG)
      echo "OK ($RES): $INST"
    else
      echo -ne "\033[1K\r"
      echo "ERROR: $INST ($LOG)"
    fi
  else
    echo "NO PROOF: $INST"
  fi
}


for f in $INSTDIR/*.qdimacs; do check $f; done




