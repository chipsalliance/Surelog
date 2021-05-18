export TOP_DIR :=$(shell git rev-parse --show-toplevel)

# Explicitly use bash so we can use the pipefail feature
SHELL :=/bin/bash

#===============================================================================
# CAD TOOL SETUP
#
# You can either include a makefile that has the environment setup or you can
# set the variables below to the correct values. The LM_LICENSE_FILE should be
# set to a valid synopsys licenese server and DC_SHELL should point to the
# Synopsys DesignCompiler dc_shell bin.
#===============================================================================

# If the machine you are working on is bsg_cadenv complient, then you do not
# need to setup the cad tools, simply put bsg_cadenv in the same root dir.
-include $(TOP_DIR)/../bsg_cadenv/cadenv.mk

# License file
export LM_LICENSE_FILE ?=

# DesignCompiler dc_shell binary
export DC_SHELL ?=

#===============================================================================
# DESIGN SETUP
#
# The DESIGN_NAME variable is used to set the name of the top-level module
# you would like to elaborate in DesignCompiler.
#
# The DESIGN_FILELIST is the path to the filelist object for this design. The
# filelist is responsible for linking all files, include directories, macros
# and top-level parameters for the design. The filelist is a VCS style filelist
# that can contain 5 things:
#   1. Comments        -- begging in the # character
#   2. +incdir+<path>  -- adding a search directory for includes
#   3. +define+<macro> -- adding a macro definition at compile time
#   4. -pvalue+<param> -- top-level parametes
#   5. <file>          -- verilog files
#
# The DESIGN_DIRECTORIES_MK is an optional file that is a makefile that gets
# included right before the major steps in the sv2v conversion process. This
# makefile can specify envrionment variables that your DESIGN_FILELIST needs to
# find and link all of the files.
#===============================================================================

export DESIGN_NAME ?=gcd

export DESIGN_FILELIST ?=$(TOP_DIR)/examples/gcd/gcd.flist

export DESIGN_DIRECTORIES_MK ?=

export DESIGN_CONSTRAINTS_FILE ?=

export DESIGN_ELAB_NAME ?=$(DESIGN_NAME)

#===============================================================================
# ADDITIONAL TOOL SETUP
#
# These are additonal tools that we will need to use this flow. Run 'make
# tools' to download and build these. The additional tools are pretty small
# and should not take to long to build.
#===============================================================================

# Additional Tool directories
PYPY3_BUILD_DIR      :=$(TOP_DIR)/tools/pypy3
VIRTUALENV_BUILD_DIR :=$(TOP_DIR)/tools/virtual_env
PYVERILOG_BUILD_DIR  :=$(TOP_DIR)/tools/pyverilog
IVERILOG_BUILD_DIR   :=$(TOP_DIR)/tools/iverilog

# Use these in place for your normal python and pip commands. This will use the
# virtualenv python and pip which has the installed dependancies.
PYTHON :=source $(VIRTUALENV_BUILD_DIR)/bin/activate; python
PIP    :=source $(VIRTUALENV_BUILD_DIR)/bin/activate; python -m pip

# Update path variable as needed
export PATH:=$(PATH):$(IVERILOG_BUILD_DIR)/install/bin

#===============================================================================
# MAIN TARGET
#===============================================================================

.DEFAULT_GOAL=convert_sv2v

export OUTPUT_DIR       ?=$(CURDIR)/results
export OUTPUT_ELAB_FILE ?=$(OUTPUT_DIR)/$(DESIGN_NAME).elab.v
export OUTPUT_SV2V_FILE ?=$(OUTPUT_DIR)/$(DESIGN_NAME).sv2v.v

#LOGLVL?=debug
LOGLVL?=info
#LOGLVL?=warning
#LOGLVL?=error
#LOGLVL?=critical

SV2V_OPTIONS ?= -loglvl $(LOGLVL)
#SV2V_OPTIONS += -no_wire_reg_decl_opt
#SV2V_OPTIONS += -no_always_at_redux_opt
#SV2V_OPTIONS += -no_concat_redux_opt
#SV2V_OPTIONS += -wrapper bsg_top

convert_sv2v: synth elab_to_rtl

synth:
	mkdir -p $(OUTPUT_DIR)
	$(eval -include $(DESIGN_DIRECTORIES_MK))
	set -o pipefail; $(DC_SHELL) -64bit -f $(TOP_DIR)/scripts/tcl/run_dc.tcl 2>&1 | tee -i $(OUTPUT_DIR)/$(DESIGN_NAME).synth.log
	touch $(OUTPUT_DIR)/$(DESIGN_NAME).elab.v.sdc

elab_to_rtl:
	mkdir -p $(OUTPUT_DIR)
	$(eval -include $(DESIGN_DIRECTORIES_MK))
	$(PYTHON) $(TOP_DIR)/scripts/py/bsg_elab_to_rtl.py -i $(OUTPUT_ELAB_FILE) -o $(OUTPUT_SV2V_FILE) $(SV2V_OPTIONS) 2>&1 | tee -i $(OUTPUT_DIR)/$(DESIGN_NAME).elab_to_rtl.log
	cp $(OUTPUT_DIR)/$(DESIGN_NAME).elab.v.sdc $(OUTPUT_DIR)/$(DESIGN_NAME).sv2v.v.sdc
	sed -i -e 's/^#.*$$//g' $(OUTPUT_DIR)/$(DESIGN_NAME).sv2v.v.sdc
	sed -i -e '/^$$/d' $(OUTPUT_DIR)/$(DESIGN_NAME).sv2v.v.sdc

help:
	$(PYTHON) $(TOP_DIR)/scripts/py/bsg_elab_to_rtl.py -h

#===============================================================================
# TOOLS
#===============================================================================

tools: $(IVERILOG_BUILD_DIR) $(PYPY3_BUILD_DIR) $(VIRTUALENV_BUILD_DIR) $(PYVERILOG_BUILD_DIR)

$(IVERILOG_BUILD_DIR):
	mkdir -p $(@D)
	git clone git://github.com/steveicarus/iverilog.git $@
	cd $@; git checkout v10_3
	cd $@; sh autoconf.sh
	cd $@; ./configure --prefix=$@/install
	cd $@; make -j4
	cd $@; make install

$(PYPY3_BUILD_DIR):
	mkdir -p $@/download
	#cd $@/download; wget https://downloads.python.org/pypy/pypy3.7-v7.3.2-linux64.tar.bz2
	cd $@/download; wget https://downloads.python.org/pypy/pypy3.6-v7.3.2-linux64.tar.bz2
	cd $@; tar xvf download/pypy3.6-v7.3.2-linux64.tar.bz2
	cd $@; mv pypy3.6-v7.3.2-linux64/* .
	cd $@; rmdir pypy3.6-v7.3.2-linux64/

$(VIRTUALENV_BUILD_DIR): $(PYPY3_BUILD_DIR)
	mkdir -p $(@D)
	virtualenv -p $(PYPY3_BUILD_DIR)/bin/pypy3 $@
	$(PIP) install jinja2 pytest pytest-pythonpath

$(PYVERILOG_BUILD_DIR): $(VIRTUALENV_BUILD_DIR) $(IVERILOG_BUILD_DIR)
	mkdir -p $(@D)
	git clone https://github.com/PyHDI/Pyverilog.git $@
	cd $@; git checkout 1.1.3
	cd $@; git apply $(TOP_DIR)/patches/pyverilog_add_wirelist_reglist.patch
	cd $@; git apply $(TOP_DIR)/patches/pyverilog_sensitivity_comp.patch
	cd $@; $(PYTHON) setup.py install

clean_tools:
	rm -rf $(PYPY3_BUILD_DIR)
	rm -rf $(VIRTUALENV_BUILD_DIR)
	rm -rf $(PYVERILOG_BUILD_DIR)
	rm -rf $(IVERILOG_BUILD_DIR)

#===============================================================================
# CLEAN UP
#===============================================================================

deep_clean: clean_tools clean

clean:
	rm -rf $(OUTPUT_DIR)
	rm -rf __pycache__
	rm -f  parser.out parsetab.py

