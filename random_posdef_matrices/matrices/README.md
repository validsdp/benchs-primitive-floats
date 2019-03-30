# Benchmarks

To run the benchs for individual operations add, mul, sqrt, div, opp:
	
    ( cd .. && make run )
    coq_makefile -f _CoqProject -o Makefile
    make
    make benchs  # or to save time/log info:
    # \time -v -a -o make_$(date -I).time make benchs -k 2>&1 | tee -a make_$(date -I).log
    make benchs.tex
    pdflatex benchs.tex
    make benchs_native.tex
    pdflatex benchs_native.tex
