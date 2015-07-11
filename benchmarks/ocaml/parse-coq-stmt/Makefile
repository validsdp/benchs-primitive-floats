###############################################################################
OCAMLMAKEFILE = ../OCamlMakefile
###############################################################################

# Donner la liste des librairies utilisées, et dé-commmenter si non vide
LIBS = nums # numerix unix num str graphics
# INCDIRS = ~/lib
# OCAMLLDFLAGS = -dllpath ~/lib

# Donner les fichers souces de votre programme
SOURCES = syntax.ml parser.mly lexer.mll print.ml main.ml
RESULT = parse-coq-stmt

### Custom Variables
COQC = /home/emartin/src/coq-8.4pl4/bin/coqc
TEST = testsuite/test_main.v
# PRE_TARGETS = ...
YFLAGS = -v
TRASH = parser.output
# Dé-commenter pour une application utilisant les threads
# THREADS=yes

###############################################################################
-include $(OCAMLMAKEFILE)
###############################################################################

### Custom Rules
.PHONY: all
all: byte-code

.PHONY: check
check: all
	$(COQC) $(TEST) | ./$(RESULT) --tex
	$(COQC) $(TEST) | ./$(RESULT) --pvs
	$(COQC) $(TEST) | ./$(RESULT) --hl-alex -k || test $$? -eq 2
	$(COQC) $(TEST) | ./$(RESULT) --hl-sos -k || test $$? -eq 2
