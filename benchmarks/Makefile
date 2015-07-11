# -*- compile-command: "make -k -s"; -*-

# Makefile to automate benchmarks for the Coq.Interval tactic and related tools
# Author: Erik Martin-Dorel, 2014

# USAGE:
# $ make -s # to make all benchmarks (-s = --silent)
# $ make -s coq # for CoqInterval
# $ make -s metit # for PVS-6.0 (+) MetiTarski
# $ make -s interval # for PVS-6.0 (+) Interval
# $ make -s bern # for PVS-5.0 (+) Bernstein
# $ make -s sos # for HOL Light (+) REAL_SOS
# $ make -s alex # for HOL Light (+) Alexey.Solovyev's lib
# $ FORCEPVS=1 make -s pvs # for rerunning all PVS proofs, including TCCs
# $ make -s nlc-nocoq # for NLCertify, without using Coq
# $ make -s nlc-coq # for NLCertify, using Coq

include Makefile.common

# Delete the default suffixes
.SUFFIXES:

# For testing verify_ineq (by Alexey.Solovyev) we use a checkpointed
# version of HOL Light (based on DMTCP), but it is not really possible
# to run multiple instances of HOL Light in parallel.
# Hence:
.NOTPARALLEL:

### Rules
.SECONDARY: $(TMP_KEEP)
.PHONY: all clean dist-clean \
  subdirs $(SUBDIRS) clean-subdirs $(CLEAN_SUBDIRS) \
  coq-parser \
  coq pvs metit interval bern hl sos alex \
  nlc-nocoq nlc-coq \
  tar dist-tar
all: subdirs $(FINAL)
subdirs: $(SUBDIRS)
$(SUBDIRS):
	@echo Building subdir $@ ...
	$(MAKE) -C $@
coq-parser: $(DIR_PARSE_COQ)
$(PARSE_COQ): coq-parser
coq: $(CSV_COQ)
pvs: metit interval bern
metit: $(CSV_METIT)
interval: $(CSV_INTERVAL)
bern: $(CSV_BERN)
hl: sos alex
sos: $(CSV_SOS)
alex: $(CSV_ALEX)
nlc-nocoq: $(CSV_NLC_NOCOQ)
nlc-nocoq: $(CSV_NLC_COQ)
clean-subdirs: $(CLEAN_SUBDIRS)
$(CLEAN_SUBDIRS):
	@echo Cleaning subdir $(@:clean-%=%) ...
	$(MAKE) -C $(@:clean-%=%) clean
clean:
	$(RM) $(TMP_RM) $(TMP_KEEP)
dist-clean: clean clean-subdirs
	$(RM) $(FINAL) $(FINAL_AUX)
	$(RM) -r $(DIR_OUT)/pvsbin
	$(RM) .pvscontext $(DIR_OUT)/.pvscontext $(FILES_PVS:.pvs=.prf)
	$(RM) $(DIR_OUT)/orphaned-proofs.prf $(FILES_PVS:.pvs=.prf~)

# STEP 0: Make directory $(DIR_OUT)
$(DIR_OUT):
	@echo Step 0: Building $(DIR_OUT)
	mkdir -p -v $(DIR_OUT)
	@echo Step 0: Finished $(DIR_OUT)

# STEP 1: Add the Check vernacular command & Count occurrences of Time
# Warning: '$' are written '$$' in this Makefile context
$(DIR_OUT)/%.v: $(DIR_COQ)/%.v | $(DIR_OUT)
	@echo Step 1: Building $@
	cp $< $@
	./step1.perl $< >> $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 1: Finished $@

# STEP 2: COQC
%.v.out: %.v
	@echo Step 2: Building $@
	$(TIME) $(TIMEFLAGS) -o "$<.time" $(COQC) $(COQFLAGS) $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 2: Finished $@
#cat "$<.time" | sed -e"s/^/  /"
#RV=$$?; if test $$RV -eq 0; then cat "$<.time"; else cp $@ $@.bak; fi

# STEP 3: Parse Coq output
%.v.out.csv: %.v.out
	@echo Step 3: Building $@
	./step3_time.perl -f $*.v $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 3: Finished $@

%.v.out.stmt: %.v.out
	@echo Step 3: Building $@
	./step3_stmt.perl $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 3: Finished $@

# STEP(S) 4: Parse Coq formulas
%_metit.pvs: %.v.out.stmt $(PARSE_COQ)
	@echo Step 4: Building $@
	$(PARSE_COQ) --pvs < $< | ./step4_metit.perl -o $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 4: Finished $@

%_interval.pvs: %.v.out.stmt $(PARSE_COQ)
	@echo Step 4: Building $@
	$(PARSE_COQ) --pvs < $< | ./step4_interval.perl -o $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 4: Finished $@

%_bern.pvs: %.v.out.stmt $(PARSE_COQ)
	@echo Step 4: Building $@
	$(PARSE_COQ) --pvs < $< | ./step4_bern.perl -o $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 4: Finished $@

%_sos.hl: %.v.out.stmt $(PARSE_COQ)
	@echo Step 4: Building $@
	export HOLLIGHT_DIR=$(DIR_HL) && $(PARSE_COQ) --hl-sos --keep-going < $< | ./step4_sos.perl -o $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 4: Finished $@

%_alex.hl: %.v.out.stmt $(PARSE_COQ)
	@echo Step 4: Building $@
	$(PARSE_COQ) --hl-alex --keep-going < $< | ./step4_alex.perl -o $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 4: Finished $@

# STEP 4 for Sollya
$(DIR_OUT)/%.sollya: %.sollya
	@echo Step 4: Building $@
	cp $< $@
	@echo Step 4: Finished $@

# STEP(S) 5: Run the tools
%_nlc_nocoq.log %_nlc_nocoq.time: $(NLC_INEQ)
	@echo Step 5: Building $*_nlc_nocoq.log, $*_nlc_nocoq.time
	perl -w -p -e 's|$(NLC_PATT)|$(NLC_INEQ)|;' $(NLC_PARAM_NOCOQ) > $(NLC_PARAM)
	cd $(DIR_NLC) && $(TIME) $(TIMEFLAGS) -o $(abspath $*_nlc_nocoq.time) $(TIMEOUT_NLC_NOCOQ) $(NLC) $(notdir $*) 2> $(abspath $*_nlc_nocoq.log~) && mv -f $(abspath $*_nlc_nocoq.log~) $(abspath $*_nlc_nocoq.log) || echo > $(abspath $*_nlc_nocoq.log)
	@echo Step 5: Finished $*_nlc_nocoq.log, $*_nlc_nocoq.time

%_nlc_coq.log %_nlc_coq.time: $(NLC_INEQ)
	@echo Step 5: Building $*_nlc_coq.log, $*_nlc_coq.time
	perl -w -p -e 's|$(NLC_PATT)|$(NLC_INEQ)|;' $(NLC_PARAM_COQ) > $(NLC_PARAM)
	cd $(DIR_NLC) && $(TIME) $(TIMEFLAGS) -o $(abspath $*_nlc_coq.time) $(TIMEOUT_NLC_COQ) $(NLC) $(notdir $*) 2> $(abspath $*_nlc_coq.log~) && mv -f $(abspath $*_nlc_coq.log~) $(abspath $*_nlc_coq.log) || echo > $(abspath $*_nlc_coq.log)
	@echo Step 5: Finished $*_nlc_coq.log, $*_nlc_coq.time

%.sollya.out: %.sollya
	@echo Step 5: Building $@
	$(SOLLYA) $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 5: Finished $@

%_metit.pvs.out: %_metit.pvs
	@echo Step 5: Building $@
	$(PVS6) $(PROVEITFLAGS) -o $@ $< | sed -e"s/^/  /"
	@echo Step 5: Finished $@

%_interval.pvs.out: %_interval.pvs
	@echo Step 5: Building $@
	$(PVS6) $(PROVEITFLAGS) --disable-oracles -o $@ $< | sed -e"s/^/  /"
	@echo Step 5: Finished $@

%_bern.pvs.out: %_bern.pvs
	@echo Step 5: Building $@
	$(PVS5) $(PROVEITFLAGS) -o $@ $< | sed -e"s/^/  /" && mv $*_bern.log $*_bern.pvs.log
	@echo Step 5: Finished $@

%_sos.hl.out %_sos.hl.time: %_sos.hl
	@echo Step 5: Building $<.out, $<.err, $<.time
	export HOLLIGHT_DIR=$(DIR_HL) && $(TIME) $(TIMEFLAGS) -o $<.time $(TIMEOUT_SOS) $(OCAML) < $< > $<.out~ 2> $<.err && mv -f $<.out~ $<.out || echo > $<.out
	@echo Step 5: Finished $<.out, $<.err, $<.time

%_alex.hl.out: %_alex.hl
	@echo Step 5: Building $@
	$(HL_ALEX) < $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 5: Finished $@

# STEP(S) 6: Parse tools output/log
 ## cp $< $@ ## cp $*.pvs.log $@ ## What about TCCs ?
%_nlc_nocoq.csv: %_nlc_nocoq.log %_nlc_nocoq.time
	@echo Step 6: Building $@
	./step6_nlc_nocoq_1.perl --t1 $*_nlc_nocoq.time $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_nlc_coq.csv: %_nlc_coq.log %_nlc_coq.time
	@echo Step 6: Building $@
	./step6_nlc_coq_1.perl --t1 $*_nlc_coq.time $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%.sollya.csv: %.sollya.out
	@echo Step 6: Building $@
	./step6_sollya.perl --title=$(notdir $(@:.csv=)) $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_metit.pvs.csv: %_metit.pvs.out
	@echo Step 6: Building $@
	./step6_metit.perl --title=$(notdir $(@:.csv=)) $*_metit.pvs.log > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_interval.pvs.csv: %_interval.pvs.out
	@echo Step 6: Building $@
	./step6_interval.perl -f $*_interval.pvs.log $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_bern.pvs.csv: %_bern.pvs.out
	@echo Step 6: Building $@
	./step6_bern.perl -f $*_bern.pvs.log $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_sos.hl.csv: %_sos.hl.out %_sos.hl.time
	@echo Step 6: Building $@
	./step6_sos_1.perl --t1 $*_sos.hl.time -f $*.v $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

%_alex.hl.csv: %_alex.hl.out
	@echo Step 6: Building $@
	./step6_alex.perl --title=$(notdir $(@:.csv=)) $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 6: Finished $@

# STEP 7: Generate the LaTeX
$(FINAL): $(FILES_CSV) ./step7_tex.perl
	@echo Step 7: Building $@
	cat $(FILES_CSV) > $(FINAL_AUX)
	./step7_tex.perl $(addprefix --aux-coq=,$(FIL_COQ_FINAL)) $(addprefix --coq=,$(CSV_COQ_FINAL)) $(addprefix --metit=,$(CSV_METIT)) $(addprefix --interval=,$(CSV_INTERVAL)) $(addprefix --bern=,$(CSV_BERN)) $(addprefix --hl-sos=,$(CSV_SOS)) $(addprefix --hl-alex=,$(CSV_ALEX)) $(addprefix --sollya=,$(CSV_SOLLYA)) $(addprefix --nlc-nocoq=,$(CSV_NLC_NOCOQ)) $(addprefix --nlc-coq=,$(CSV_NLC_COQ)) > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 7: Finished $@

tar:
	@echo Building $(PACK).tar.gz
	$(RM) $(PACK).tar.gz
	$(RM) -r $(PACK)
	mkdir -p $(sort $(addprefix $(PACK)/,$(dir $(TAR_FILES))))
	for f in $(TAR_FILES); do cp -p $$f $(PACK)/$$f; done
	tar czf $(PACK).tar.gz $(PACK)/
	$(RM) -r $(PACK)
	@echo Finished $(PACK).tar.gz

dist-tar:
	@echo Building $(DIST_PACK).tar.gz
	$(RM) $(DIST_PACK).tar.gz
	$(RM) -r $(DIST_PACK)
	mkdir -p $(sort $(addprefix $(DIST_PACK)/,$(dir $(DIST_TAR_FILES))))
	-for f in $(DIST_TAR_FILES); do cp -p $$f $(DIST_PACK)/$$f; done
	tar czf $(DIST_PACK).tar.gz $(DIST_PACK)/
	$(RM) -r $(DIST_PACK)
	@echo Finished $(DIST_PACK).tar.gz
