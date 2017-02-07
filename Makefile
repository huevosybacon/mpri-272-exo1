# Based on example given by Adam Chlipala, in “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

# Usage examples:
#     make
#     make all
#     make html
#     make all TIMED=yes
#     make clean

# Modules to be included in the main build:
MODULES-MAIN := FormalSystem Translation Classical
MODULES-OTHER := 

# Files that are largely broken for now and will not be built. \
  (WARNING: this typically will have the effect that they become more\
  broken, since they won’t stay up-to-date with their dependencies.)
MODULES-BROKEN :=  


VS      := $(MODULES-MAIN:%=%.v)
VS-OTHER := $(MODULES-OTHER:%=%.v)
VS-ALL := $(VS) $(VS-OTHER)

# The HoTT coq binaries (“hoqc” etc.) are used by default.  These can
# be overridden by explicitly passing a different value of COQC, e.g.
#     make COQC=coqc
# COQDEP and COQDOC are set automatically based on COQC, but we are not
# very clever about this, so if it doesn’t work, these can be explicitly
# specified too.
#
# NOTE: currently, the “timed” options are hardwired to use “hoqc” etc.

COQC ?= coqc

ifeq ($(COQC),hoqc)
	COQDEP ?= hoqdep
else
	COQDEP ?= coqdep
endif

COQDOC ?= coqdoc

export COQC COQDEP COQDOC

# Optionally: report compilation times
ifeq ($(TIMED),yes)
	COMPSHELL := scripts/report_time.sh
else
	COMPSHELL := $(SHELL)
endif

.PHONY: coq all install clean html

coq: Makefile.coq
	$(MAKE) -f Makefile.coq SHELL=$(COMPSHELL)

Makefile.coq: Makefile $(VS)
	coq_makefile -R . "" $(VS) -o Makefile.coq

Makefile_all.coq: Makefile $(VS-ALL)
	coq_makefile -R . "" $(VS-ALL) -o Makefile_all.coq

all: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq SHELL=$(COMPSHELL) 

install: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq install SHELL=$(COMPSHELL) 

clean:: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq clean
	rm -f Makefile*.coq
	rm -f html

html: all
	mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d html $(VS-CORE) $(VS-EXTRA)
