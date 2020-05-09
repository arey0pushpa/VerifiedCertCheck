#!/bin/bash

function error() {
  echo "Error: $1"
  exit 1
}


test $# -eq 1 || error "Usage: eval-logs log-dir"

LOGDIR=$1



egrep "User time|Trace size|Proof size|^s" "$LOGDIR"/*.log\
  | sed -re 's/:/ /;s/Trace size:/trace-size/;s/Proof size:/proof-size/;s/User time.*:/user-time/;
             s|^.*/||; s/\.log / /; s/\.(solve|reduce|verify)/ \1/
            '\
  | gawk -f <(cat <<'HERE'
      {
        problem=$1
        cat=$2 "-" $3
        value=$4
        data[problem][cat] = value
      }

      END {
        n = split("solve-user-time solve-trace-size reduce-user-time reduce-proof-size verify-user-time verify-s",cats)

        printf "problem, "
        for (i=1;i<n;i++) printf "%s, ", cats[i];
        print cats[n]

        PROCINFO["sorted_in"] = "@ind_str_asc"

        for (p in data) {
          printf "%s, ", p

          for (i=1;i<n;i++) printf "%s, ", data[p][cats[i]];
          print data[p][cats[i]]


        }
      }

HERE
)
