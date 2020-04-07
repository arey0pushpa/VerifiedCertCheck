error() {
  echo $1
  exit 1
}


check() {
  f=$1

  stem=${f%.trace}
  fname=${stem##*/}
  dname=${stem%/*/*}

  fml="$dname/instances/$fname.qdimacs"
  prf="$dname/proofs/$fname.qrp"

  if test ! -f "$fml"; then
    echo "formula not found: $fml";
    return
  fi


  lastline=$(tail -n1 $f)

  if ( echo $lastline | grep -q "^r SAT" ); then
    echo "checking (SAT): $f"
    ./qrpcheck -f $fml $f >$prf
    echo Done
  elif ( echo $lastline | grep -q "^r UNSAT" ); then
    echo "checking (UNSAT): $f"
    ./qrpcheck $f >$prf
    echo Done
  else
    echo "No valid r line at end of file: $f"
  fi
}


for f in testdb/utraces/*.trace; do
  check "$f"

#   echo $stem
#   echo
#   echo

done
