#!/bin/bash

set -ex

coq_makefile -f _CoqProject -o Makefile

make

\time -v -a -o make0_$(date -I).time make dryrun -k 2>&1 | tee -a make0_$(date -I).log

# TODO Uncomment
# make benchs, or
#\time -v -a -o make_$(date -I).time make benchs -k 2>&1 | tee -a make_$(date -I).log

# make tex
