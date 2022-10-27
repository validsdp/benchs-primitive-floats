all::
	$(info Pos. def. matrices of size 50 upto 500 have already be generated and committed.)
	$(info If you want to regenerate them, type 'make run'.)

compile:: random_posdef_matrices

run:: compile
	./random_posdef_matrices

random_posdef_matrices: main.ml
	ocamlopt -o $@ $^

clean::
	rm -f *~ *.cm* *.o
