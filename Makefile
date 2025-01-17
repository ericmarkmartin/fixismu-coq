# Comment out the below line if you want to be quiet by default.
V=1

# Specify a concrete number of jobs if necessary
JOBS=-j

ifeq ($(V),1)
E=@true
Q=
MFLAGS=$(JOBS)
else
E=@echo
Q=@
MFLAGS=$(JOBS) -s
endif

SRCS := $(shell egrep "^.*\.v$$" _CoqProject)
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: coq clean install validate

coq: Makefile.coq
	$(E) "  MAKE Makefile.coq"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(E) "  COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

install: Makefile.coq
	$(E) "  MAKE -f Makefile.coq install"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq install

validate: Makefile.coq
	$(E) "  MAKE -f Makefile.coq validate"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq validate
