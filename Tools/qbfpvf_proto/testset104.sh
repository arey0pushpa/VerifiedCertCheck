#!/bin/bash

gawk '{print "../benchmarks/instances/" $0}' testset104.txt | parallel -n1 -j4 ./do_test.sh -srv

