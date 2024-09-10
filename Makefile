################################################
#            Check makefile version            #
# (https://github.com/mit-plv/koika/issues/18) #
################################################

ifeq ($(filter output-sync,$(value .FEATURES)),)
$(info You have Make version $(MAKE_VERSION).)
$(error Unsupported version of Make. Please use GNU Make >= 4.0)
endif

####################
# Global variables #
####################

OBJ_DIR := _obj
BUILD_DIR := _build/default
COQ_BUILD_DIR := $(BUILD_DIR)/coq
OCAML_BUILD_DIR := $(BUILD_DIR)/ocaml

V ?=
verbose := $(if $(V),,@)

default: all

#######
# Coq #
#######

coq:
	@printf "\n== Building Coq library ==\n"
	dune build @@coq/all

coq-all:
	@printf "\n== Building Coq library and proofs ==\n"
	dune build @coq/all

CHECKED_MODULES ?= OneRuleAtATime CompilerCorrectness/Correctness
checked_paths := $(patsubst %,$(COQ_BUILD_DIR)/%.vo,$(CHECKED_MODULES))

coq-check: coq-all
	coqchk --output-context -R $(COQ_BUILD_DIR) Koika $(checked_paths)

.PHONY: coq coq-all coq-check

#########
# OCaml #
#########

ocaml:
	@printf "\n== Building OCaml library and executables ==\n"
	dune build ocaml/cuttlec.exe @install

.PHONY: ocaml

####################
# Examples & tests #
####################

# The setup below generates one Makefile rule per target.  It uses canned rules
# and eval because patterns like ‘%1/_objects/%2.v/: %1/%2.v’ aren't supported.
# https://www.gnu.org/software/make/manual/html_node/Canned-Recipes.html
# https://www.gnu.org/software/make/manual/html_node/Eval-Function.html
#
# This code is not very useful anymore, because everything, including selecting
# which examples/tests are to be built, is done in examples/dune and tests/dune,
# now.  The code is left here, because the dune code does not support .etc
# supplements, yet, and to give make the right™ targets for examples/tests.
# This means that the assignments to TESTS and EXAMPLES must be kept in sync
# with their respective dune files!

target_directory = $(1).d
target_directories = $(foreach fname,$(1),$(call target_directory,$(fname)))

# Execute follow-ups if any
define cuttlec_recipe_coda =
	$(verbose)if [ -d $<.etc ]; then cp -rf $<.etc/. "$(BUILD_DIR)$@"; fi
	$(verbose)if [ -d $(dir $<)etc ]; then cp -rf $(dir $<)etc/. "$(BUILD_DIR)$@"; fi
	$(verbose)if [ -f "$(BUILD_DIR)$@/Makefile" ]; then $(MAKE) -C "$(BUILD_DIR)$@"; fi
endef

define cuttlec_recipe =
	@printf "\n-- Compiling %s --\n" "$<"
	dune build "@$@/runtest"
endef

define cuttlec_template =
$(eval dirpath := $(call target_directory,$(1)))
$(dirpath) $(dirpath)/: $(1)
	$(value cuttlec_recipe)
	$(value cuttlec_recipe_coda)
endef

TESTS := $(wildcard tests/*.lv) $(wildcard tests/*.v)
EXAMPLES := $(wildcard examples/*.lv) $(wildcard examples/*.v) examples/rv/rv32i.v examples/rv/rv32e.v

$(foreach fname,$(EXAMPLES) $(TESTS),\
	$(eval $(call cuttlec_template,$(fname))))

examples: coq.kernel
	dune build @examples/runtest

clean-examples:
	find examples/ -type d \( -name '*.d' \) -exec rm -rf {} +
	rm -rf $(BUILD_DIR)/examples

tests:
	dune build @tests/runtest

clean-tests:
	find tests/ -type d  \( -name '*.d' \) -exec rm -rf {} +
	rm -rf $(BUILD_DIR)/tests

# HACK: Part One of a two-part hack. When using nix, dune does not provide the
# OCaml libs of Coq to its targets. Thus, link the libs to a well-known location
# and add specific "-nI" include flags in e.g. examples/rv/dune.
coq.kernel:
	@./coq.kernel.hack.sh

.PHONY: configure examples clean-examples tests clean-tests

#################
# Whole project #
#################

readme:
	./etc/readme/update.py README.rst

package:
	etc/package.sh

dune-all: coq ocaml
	@printf "\n== Completing full build ==\n"
	dune build @all

all: coq ocaml examples tests readme;

clean: clean-tests clean-examples
	dune clean
	rm -f koika-*.tar.gz coq.kernel

.PHONY: readme package dune-all all clean

.SUFFIXES:

# Running two copies of dune in parallel isn't safe, and dune is already
# handling most of the parallelism for us
.NOTPARALLEL:

# Disable built-in rules
MAKEFLAGS += --no-builtin-rules
.SUFFIXES:
