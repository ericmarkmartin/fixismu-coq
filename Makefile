# Comment out the below line if you want to be quiet by default.
V=1

# Set a concrete value such as -j4 if nested make jobserver inheritance is unavailable.
JOBS ?=

ROCQ ?= rocq

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

.PHONY: all rocq coq clean

all: rocq

rocq: Makefile.rocq
	$(E) "  MAKE Makefile.rocq"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.rocq

coq: rocq

Makefile.rocq: Makefile _CoqProject
	$(E) "  ROCQ MAKEFILE Makefile.rocq"
	$(Q)$(ROCQ) makefile -f _CoqProject -o Makefile.rocq

clean: Makefile.rocq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.rocq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.rocq Makefile.rocq.conf Makefile.coq Makefile.coq.conf
	$(Q)rm -f *.bak *.d *.glob *~ result*
