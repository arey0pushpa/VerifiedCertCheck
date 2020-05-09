
function error() {
  echo -n "Error: $1"

  if test "$BASENAME"; then echo " in $BASENAME"; else echo; fi

  exit 1
}

function check_file() {
  test -f "$1" || error "No such file: $1"
}

function check_for_executable() {
  test -x $1 || error "$1 not found"
}

BASENAME=

check_for_executable reduce
check_for_executable verify

# DO NOT CHANGE DEFAULT OPTIONS HERE! CHANGE THEM IN GENERATED .scripting_config FILE!
if test ! -f ".scripting_config"; then
  echo "Creating config file with default settings: .scripting_config"
cat >".scripting_config" <<HERE
# Configuration for test scripts
TRACEDIR=~/opt/qbf/ctraces
DEPQBF=~/devel/depqbf_mod5/depqbf
# DEPQBF_OPTIONS="--dep-man=simple --no-lazy-qpup --no-trivial-falsity --no-trivial-truth --no-dynamic-nenofex --no-qbce-dynamic"
# DEPQBF_OPTIONS="--dep-man=simple --traditional-qcdcl --no-trivial-falsity --no-trivial-truth --no-dynamic-nenofex --no-qbce-dynamic"
DEPQBF_OPTIONS="--dep-man=simple --trace=compact --no-lazy-qpup --no-qbce-dynamic --max-secs=2700"
HERE
fi

. .scripting_config

function set_names_from_basename() {
  BASENAME=$1

  TRACE_BASENAME="$TRACEDIR/$BASENAME"

  PROOF="$TRACE_BASENAME.cqrp"
  TRACE="$TRACE_BASENAME.ctrace"
}


function set_names_from_qdimacs() {
  check_file "$1"
  DIMACS="$1"
  set_names_from_basename "$(basename -s .qdimacs "$1")"
}

function set_names_from_ctrace() {
  check_file "$1"
  set_names_from_basename "$(basename -s .ctrace "$1")"
}


function init_logging() {
  PHASE="$1"
  test -n "$TRACE_BASENAME" -a -n "$PHASE" || error "Internal: TRACE_BASENAME and PHASE must be set"

  LOGFILE_BASENAME="$TRACE_BASENAME.$PHASE"
  LOGFILE="$LOGFILE_BASENAME.log"


  if test -f "$LOGFILE"; then
    mv $LOGFILE $(mktemp "$LOGFILE_BASENAME.old.XXXXXXXX.log")
  fi

  echo "Date $(date)" >>"$LOGFILE"
  echo "Machine $(uname -a)" >>"$LOGFILE"
#   echo "Log: $LOGFILE"
}

function std_init_qdimacs() {
  set_names_from_qdimacs "$1"
  init_logging "$2"
}

function std_init_ctrace() {
  set_names_from_basename "$1"
  init_logging "$2"
}


function run_command() {
  check_file "$LOGFILE"

  local COMMAND="$1"
  echo "Command $COMMAND" >>"$LOGFILE"

  /usr/bin/time -a -o "$LOGFILE" -v $COMMAND >"$LOGFILE" 2>&1
  local RESULT=$?

  echo "Return code: $RESULT">>"$LOGFILE"

  return $RESULT
}


function run_command_tr() {
  check_file "$LOGFILE"

  local COMMAND="$1"
  local TRACE="$2"
  echo "Command $COMMAND" >>"$LOGFILE"

  /usr/bin/time -a -o "$LOGFILE" -v $COMMAND > "$TRACE" 2> >(tee -a "$LOGFILE" >&2)
  local RESULT=$?

  echo "Return code: $RESULT">>"$LOGFILE"

  return $RESULT
}


function solve() {
  check_for_executable "$DEPQBF"
  check_file "$DIMACS"
  COMMAND="$DEPQBF $DEPQBF_OPTIONS $DIMACS"

  init_logging "solve"

  run_command_tr "$COMMAND" "$TRACE"
  local RESULT=$?

  stat -c 'Trace size: %s' "$TRACE" >>"$LOGFILE"

  if test $RESULT -eq 0; then error "UNSPEC solver result"
  elif test $RESULT -eq 10; then echo "SAT $BASENAME"
  elif test $RESULT -eq 20; then echo "UNSAT $BASENAME"
  else error "Strange return code: $RESULT"
  fi

  return 0
}

function reduce() {
  init_logging "reduce"
  check_file "$TRACE"
  COMMAND="./reduce $TRACE $PROOF"

  run_command "$COMMAND"
  local RESULT=$?

  stat -c 'Trace size: %s' "$TRACE" >>"$LOGFILE"
  stat -c 'Proof size: %s' "$PROOF" >>"$LOGFILE"

  test $RESULT -eq 0 || error "reduce: error return code: $RESULT"

  echo "REDUCED $BASENAME"

  return 0
}

function verify() {
  init_logging "verify"

  check_file "$DIMACS"
  check_file "$PROOF"

  COMMAND="./verify $DIMACS $PROOF"

  run_command "$COMMAND"
  local RESULT=$?


  test $RESULT -eq 0 || error "verify: error return code: $RESULT"

  echo "VERIFIED $BASENAME"

#   if test $RESULT -eq 0; then echo "VERIFIED"
#   else error "Error return code: $RESULT"
#   fi

  return 0
}



OPTIND=1         # Reset in case getopts has been used previously in the shell.

SOLVE=false
REDUCE=false
VERIFY=false

while getopts "srv" opt; do
    case "$opt" in
    h|\?)
        error "Invalid options"
        ;;
    s)  SOLVE=true
        ;;
    r)  REDUCE=true
        ;;
    v)  VERIFY=true
        ;;
    esac
done

shift $((OPTIND-1))

[ "${1:-}" = "--" ] && shift


test $# -eq 1 || error "Expected qdimacs filename"

set_names_from_qdimacs "$1"
shift

if $SOLVE && $VERIFY; then REDUCE=true; fi

if $SOLVE; then solve; fi
if $REDUCE; then reduce; rm -rf "$TRACE"; fi
if $VERIFY; then verify; rm -rf "$PROOF"; fi



