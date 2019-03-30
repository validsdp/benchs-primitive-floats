all:: run

compile:: random_posdef_matrices

run:: compile
	./random_posdef_matrices

random_posdef_matrices: main.ml
	ocamlopt -o $@ $^

clean::
	rm -f *~ *.cm* *.o
