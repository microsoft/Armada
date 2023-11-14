################################################################################
# Customize these variables for your project
################################################################################
# The root files of your project, from which to begin scanning dependences
FSTAR_FILES=MyProgramProof.fst MyVarIntroProof.fst MyVarHidingProof.fst GlobalVarExampleInvariant.fst

FSTAR_EXEC?=$(shell which fstar.exe)
Z3_EXEC?=$(shell which z3)

################################################################################
FSTAR=$(FSTAR_EXEC) --cache_checked_modules --smt $(Z3_EXEC)

all: verify-all

# a.fst.checked is the binary, checked version of a.fst
%.checked: %
	$(FSTAR) $*
	touch $@

clean:
	rm -rf *~ *.checked .depend

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --extract '* -FStar -Prims' > .depend

depend: .depend

include .depend

verify-all: $(addsuffix .checked, $(ALL_FST_FILES))
