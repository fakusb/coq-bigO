##############################################################################
# To specify the location of the Coq binaries, create a file called
# settings.sh and define the variable COQBIN (with trailing slash),
# e.g.
#   COQBIN=/var/tmp/coq/bin/
# If this file is absent, then COQBIN is empty and "coqc" is used.

-include settings.sh

##############################################################################
# We assume that TLC and CFML have been installed via [make install].
# If desired, these variables can be overridden in settings.sh.

ifndef TLC
  TLC  := $(shell $(COQBIN)coqc -where)/user-contrib/TLC
endif

ifndef CFML
  CFML := $(shell $(COQBIN)coqc -where)/user-contrib/CFML
endif

##############################################################################
# Check that TLC and CFML can be found.

ifeq ($(wildcard $(TLC)),)
  $(error $(TLC) does not exist. \
          Please install TLC first)
endif

ifeq ($(wildcard $(CFML)),)
  $(error $(CFML) does not exist. \
          Please install CFML first)
endif

##############################################################################
# Define SRC.
# This must be an absolute path.

SRC := $(shell cd ../src && pwd)

##############################################################################
# Define COQINCLUDE.

PWD := $(shell pwd)
BIGO := $(shell cd ../../src && pwd)

COQINCLUDE := \
  -R $(TLC) TLC                \
  -R $(CFML)/lib/coq CFML      \
  -R $(CFML)/lib/stdlib STDLIB \
  -R $(PWD) EXAMPLES           \
	-R $(BIGO) BigO              \

##############################################################################
# Instrument the produced CF to enable reasoning about time credits

CFML_FLAGS := -credits

##############################################################################
# Define ML.
# This variable specifies which .ml files should be processed by CFML.
# We copy these source files to $(CF), and process them with CFML there.

SOURCES := \
  max_subsequence_sum.ml \
  simple.ml

CF := $(PWD)/_cf

ML := $(patsubst %,$(CF)/%,$(SOURCES))

OCAML_INCLUDE := \
  -I $(CFML)/lib/stdlib \
  -I $(CF) \

##############################################################################
# Define V and VD.

# The variable V specifies which files should be (ultimately) processed by Coq.
# It is computed late, after CFML has produced the files %_ml.v in $(CF). Note
# that V is assigned using = instead of :=.

# The variable V_AUX specifies which extra dependencies Coq should see.
# We leave it empty unless ARTHUR is defined.

# These variables are used by Makefile.coq.

V = $(shell find $(PWD) -name "*.v" | grep -vw _output)

##############################################################################

# Export every variable to every sub-make.
export

##############################################################################
# Compilation.

.PHONY: all prepare finish clean

# The target all is split as a sequence (prepare; finish). The only reason why
# this is done is so that the variable V is evaluated *after* CFML has run. I
# have tried various other ways, but failed miserably; $(shell) is evaluated
# too early, and my attempts to use `...` ran into problems with spaces and
# quoting.

all: finish

prepare:
	@ $(MAKE) --no-print-directory -C ../src all
	@ echo "------------------------------------------------------------------------------"
	@ mkdir -p $(CF)
	@ cd $(SRC) && cp -fa $(SOURCES) $(CF)
	@ chmod a-w $(ML)
	@ $(MAKE) --no-print-directory -f $(CFML)/lib/make/Makefile.cfml all

finish: prepare
	@ echo "------------------------------------------------------------------------------"
	@ $(MAKE) --no-print-directory -f $(TLC)/Makefile.coq _CoqProject all

clean:
	@ rm -rf $(CF)
	@ $(MAKE) --no-print-directory -f $(TLC)/Makefile.coq $@
