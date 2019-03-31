#!/bin/bash

set -ex

coq_makefile -f _CoqProject -o Makefile

make

# make benchs -k # or better:
\time -v -a -o make_$(date -I).time make benchs -k 2>&1 | tee -a make_$(date -I).log

make tex
