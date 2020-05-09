#!/bin/sh


test $# -eq 1 || exit 1


sed -re 's/^#.*//;s/K *$/ 1024/;s/M *$/ 1048576/;s/G *$/ 1073741824/' $1 \
  | gawk '
      BEGIN { print "problem, orig-solve-time, orig-trace-size"  }
      $4 { print $1 ", " $2 ", " int($3*$4) }
    '
