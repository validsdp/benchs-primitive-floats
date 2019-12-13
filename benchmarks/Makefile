# -*- compile-command: "make -k -s"; -*-

# Makefile to automate benchmarks for the Coq.Interval tactic and related tools

# USAGE:
# $ make -s # to make all benchmarks (-s = --silent)
# $ make -s 341-bigz-int31
# $ make -s 341-bigz-int63
# $ make -s dev-bigz-int63
# $ make -s dev-primfloat

include Makefile.common

# Delete the default suffixes
.SUFFIXES:

# Run benchmarks sequentially
.NOTPARALLEL:

### Rules
.SECONDARY: $(TMP_KEEP)
.PHONY: all clean dist-clean \
  341-bigz-int31 341-bigz-int63 dev-bigz-int63 dev-primfloat \
  tar dist-tar

all:
	sudo docker run --rm -it -v "$(CURDIR):$(CURDIR)" -w "$(CURDIR)" --init $(COQ89_INTVL_STABLE) /bin/bash --login -c "$(OPAM_INFO_COMMAND); make 341-bigz-int31" | tee make.$$(date +'%Y%m%d_%H%M%S').COQ89_INTVL_STABLE.log
	sudo docker run --rm -it -v "$(CURDIR):$(CURDIR)" -w "$(CURDIR)" --init $(COQ810_INTVL_STABLE) /bin/bash --login -c "$(OPAM_INFO_COMMAND); make 341-bigz-int63" | tee make.$$(date +'%Y%m%d_%H%M%S').COQ810_INTVL_STABLE.log
	sudo docker run --rm -it -v "$(CURDIR):$(CURDIR)" -w "$(CURDIR)" --init $(COQ810_INTVL_DEV) /bin/bash --login -c "$(OPAM_INFO_COMMAND); $(OPAM_INTVL_DEV); make dev-bigz-int63-810" | tee make.$$(date +'%Y%m%d_%H%M%S').COQ810_INTVL_DEV.log
	sudo docker run --rm -it -v "$(CURDIR):$(CURDIR)" -w "$(CURDIR)" --init $(COQ811_INTVL_DEV) /bin/bash --login -c "$(OPAM_INFO_COMMAND); $(OPAM_INTVL_DEV); make dev-bigz-int63-811" | tee make.$$(date +'%Y%m%d_%H%M%S').COQ11_INTVL_DEV.log
	sudo docker run --rm -it -v "$(CURDIR):$(CURDIR)" -w "$(CURDIR)" --init $(COQ811_INTVL_DEV) /bin/bash --login -c "$(OPAM_INFO_COMMAND); $(OPAM_INTVL_DEV); make dev-primfloat" | tee make.$$(date +'%Y%m%d_%H%M%S').COQ811_INTVL_DEV.log
	$(MAKE) $(FINAL)

coq: $(CSV_COQ)
clean:
	$(RM) $(TMP_KEEP)
dist-clean: clean
	$(RM) $(FINAL) $(FINAL_AUX)

341-bigz-int31: $(FIL_COQ_1_31)
341-bigz-int63: $(FIL_COQ_1_63)
dev-bigz-int63-810: $(FIL_COQ_2_10)
dev-bigz-int63-811: $(FIL_COQ_2_11)
dev-primfloat: $(FIL_COQ_3)

# STEP 1: Make directory $(DIR_OUT)
$(DIR_OUT):
	@echo Step 0: Building $(DIR_OUT)
	mkdir -p -v $(DIR_OUT)
	@echo Step 0: Finished $(DIR_OUT)

# # STEP 1: Add the Check vernacular command & Count occurrences of Time
# # Warning: '$' are written '$$' in this Makefile context
# $(DIR_OUT)/%.v: $(DIR_COQ)/%.v | $(DIR_OUT)
# 	@echo Step 1: Building $@
# 	cp $< $@
# 	./step1.perl $< >> $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
# 	@echo Step 1: Finished $@

$(DIR_OUT)/%_stable_bigz_int31.v $(DIR_OUT)/%_stable_bigz_int63.v: $(DIR_COQ)/%_stable.v | $(DIR_OUT)
	@echo Step 1: Building $@
	cp $< $@
	@echo Step 1: Finished $@

$(DIR_OUT)/coqintvl_dev_%.v: $(DIR_COQ)/coqintvl_dev_%.v | $(DIR_OUT)
	@echo Step 1: Building $@
	cp $< $@
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
	./step3_time.perl $< > $@ || ( RV=$$?; rm -f "$@"; exit $${RV} )
	@echo Step 3: Finished $@

# STEP 4: Generate the LaTeX
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
