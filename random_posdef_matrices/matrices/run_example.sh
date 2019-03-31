#!/bin/bash

set -ex

coq_makefile -f _CoqProject -o Makefile

make mat0100.vo

\time -v -a -o make_ex_$(date -I).time make example -k 2>&1 | tee -a make_ex_$(date -I).log
