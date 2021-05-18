export BP_HDK_DIR ?= $(shell git rev-parse --show-toplevel)

.PHONY: bsg_cadenv bleach_all
.DEFAULT: hdk

include $(BP_HDK_DIR)/Makefile.common

hdk:
	echo "HDK coming soon!"

bsg_cadenv:
	-cd $(BP_HDK_DIR); git clone git@github.com:bespoke-silicon-group/bsg_cadenv.git bsg_cadenv

tidy:
	echo "HDK is tidy already"

## This target just wipes the whole repo clean.
#  Use with caution.
bleach_all:
	cd $(BP_HDK_DIR); git clean -fdx; git submodule deinit -f .

