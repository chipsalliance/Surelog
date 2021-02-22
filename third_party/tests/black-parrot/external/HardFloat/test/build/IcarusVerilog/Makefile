
#=============================================================================
#
# This Makefile is part of the Berkeley HardFloat IEEE Floating-Point
# Arithmetic Package, Release 1, by John R. Hauser.
#
# Copyright 2019 The Regents of the University of California.  All rights
# reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#  1. Redistributions of source code must retain the above copyright notice,
#     this list of conditions, and the following disclaimer.
#
#  2. Redistributions in binary form must reproduce the above copyright
#     notice, this list of conditions, and the following disclaimer in the
#     documentation and/or other materials provided with the distribution.
#
#  3. Neither the name of the University nor the names of its contributors
#     may be used to endorse or promote products derived from this software
#     without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS", AND ANY
# EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE
# DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
# THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#=============================================================================

include config.make
ifndef SPECIALIZE_TYPE
$(error Macro 'SPECIALIZE_TYPE' not defined)
endif

SOURCE_DIR ?= ../../../source
TEST_SOURCE_DIR ?= ../../source

COMPILE_V = \
  iverilog -gstrict-expr-width -I$(SOURCE_DIR)/$(SPECIALIZE_TYPE) \
    -I$(SOURCE_DIR)
TESTFLOAT_GEN = testfloat_gen
SIMULATE_VVP = vvp -N

DELETE = rm -f

.PHONY: \
  default \
  test-level1-recFNToFN \
  test-level1-iNToRecFN \
  test-level1-recFNToIN \
  test-level1-recFNToRecFN \
  test-level1-addRecFN_add \
  test-level1-addRecFN_sub \
  test-level1-addRecFN \
  test-level1-mulRecFN \
  test-level1-mulAddRecFN_add \
  test-level1-mulAddRecFN_mul \
  test-level1-mulAddRecFN \
  test-level1-divSqrtRecFN_small_div \
  test-level1-divSqrtRecFN_small_sqrt \
  test-level1-all1 \
  test-level1-all2 \
  test-level1 \
  test-level2-recFNToFN \
  test-level2-iNToRecFN \
  test-level2-recFNToIN \
  test-level2-recFNToRecFN \
  test-level2-addRecFN_add \
  test-level2-addRecFN_sub \
  test-level2-addRecFN \
  test-level2-mulRecFN \
  test-level2-mulAddRecFN_add \
  test-level2-mulAddRecFN_mul \
  test-level2-mulAddRecFN \
  test-level2-divSqrtRecFN_small_div \
  test-level2-divSqrtRecFN_small_sqrt \
  test-level2-all1 \
  test-level2-all2 \
  test-level2 \
  clean \

default:
	@echo "Invalid Makefile target."
	@echo "(Valid targets include 'test-level1' and 'test-level2'.)"

vpath %.vi \
  $(TEST_SOURCE_DIR) \
  $(SOURCE_DIR)/$(SPECIALIZE_TYPE) \
  $(SOURCE_DIR) \

vpath %.v \
  $(TEST_SOURCE_DIR) \
  $(SOURCE_DIR)/$(SPECIALIZE_TYPE) \
  $(SOURCE_DIR) \

INCLUDES = \
  HardFloat_consts.vi \
  HardFloat_specialize.vi \
  HardFloat_localFuncs.vi \

SRC_COMMON = \
  finish_fail-IcarusVerilog.vi \
  HardFloat_primitives.v \
  HardFloat_specialize.v \
  fNToRecFN.v \
  isSigNaNRecFN.v \
  HardFloat_rawFN.v \
  sameRecFN.v \

$(SRC_COMMON): $(INCLUDES)

.SUFFIXES:

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_recFNToFN_template

test_recF$(1)ToF$(1).vvp: $(SRC_COMMON) recFNToFN.v test_recFNToFN.v
	$(COMPILE_V) -s test_recF$(1)ToF$(1) -o $$@ $$^

.PHONY: test-level1-recF$(1)ToF$(1)
test-level1-recF$(1)ToF$(1): test_recF$(1)ToF$(1).vvp
	$(TESTFLOAT_GEN) f$(1) | $(SIMULATE_VVP) test_recF$(1)ToF$(1).vvp

test-level1-recFNToFN: test-level1-recF$(1)ToF$(1)

.PHONY: test-level2-recF$(1)ToF$(1)
test-level2-recF$(1)ToF$(1): test_recF$(1)ToF$(1).vvp
	$(TESTFLOAT_GEN) f$(1) -level 2 | $(SIMULATE_VVP) test_recF$(1)ToF$(1).vvp

test-level2-recFNToFN: test-level2-recF$(1)ToF$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_iNToRecFN_template

test_i$(1)ToRecF$(2).vvp: $(SRC_COMMON) iNToRecFN.v test_iNToRecFN.v
	$(COMPILE_V) -s test_i$(1)ToRecF$(2) -o $$@ $$^

.PHONY: test-level1-i$(1)ToRecF$(2)
test-level1-i$(1)ToRecF$(2): test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 0" ui$(1)_to_f$(2) -rnear_even | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 1" ui$(1)_to_f$(2) -rminMag | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 2" ui$(1)_to_f$(2) -rmin | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 3" ui$(1)_to_f$(2) -rmax | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 4" ui$(1)_to_f$(2) -rnear_maxMag | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 6" ui$(1)_to_f$(2) -rodd | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 0" i$(1)_to_f$(2) -rnear_even | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 1" i$(1)_to_f$(2) -rminMag | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 2" i$(1)_to_f$(2) -rmin | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 3" i$(1)_to_f$(2) -rmax | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 4" i$(1)_to_f$(2) -rnear_maxMag | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 6" i$(1)_to_f$(2) -rodd | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp

test-level1-iNToRecFN: test-level1-i$(1)ToRecF$(2)

.PHONY: test-level2-i$(1)ToRecF$(2)
test-level2-i$(1)ToRecF$(2): test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 0" ui$(1)_to_f$(2) -rnear_even -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 1" ui$(1)_to_f$(2) -rminMag -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 2" ui$(1)_to_f$(2) -rmin -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 3" ui$(1)_to_f$(2) -rmax -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 4" ui$(1)_to_f$(2) -rnear_maxMag -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 6" ui$(1)_to_f$(2) -rodd -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 0" i$(1)_to_f$(2) -rnear_even -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 1" i$(1)_to_f$(2) -rminMag -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 2" i$(1)_to_f$(2) -rmin -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 3" i$(1)_to_f$(2) -rmax -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 4" i$(1)_to_f$(2) -rnear_maxMag -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 6" i$(1)_to_f$(2) -rodd -level 2 | $(SIMULATE_VVP) test_i$(1)ToRecF$(2).vvp

test-level2-iNToRecFN: test-level2-i$(1)ToRecF$(2)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_recFNToIN_template

test_recF$(1)ToI$(2).vvp: $(SRC_COMMON) recFNToIN.v test_recFNToIN.v
	$(COMPILE_V) -s test_recF$(1)ToI$(2) -o $$@ $$^

.PHONY: test-level1-recF$(1)ToI$(2)
test-level1-recF$(1)ToI$(2): test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 0" f$(1)_to_ui$(2) -rnear_even -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 1" f$(1)_to_ui$(2) -rminMag -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 2" f$(1)_to_ui$(2) -rmin -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 3" f$(1)_to_ui$(2) -rmax -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 4" f$(1)_to_ui$(2) -rnear_maxMag -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 6" f$(1)_to_ui$(2) -rodd -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 0" f$(1)_to_i$(2) -rnear_even -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 1" f$(1)_to_i$(2) -rminMag -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 2" f$(1)_to_i$(2) -rmin -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 3" f$(1)_to_i$(2) -rmax -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 4" f$(1)_to_i$(2) -rnear_maxMag -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 6" f$(1)_to_i$(2) -rodd -exact | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp

test-level1-recFNToIN: test-level1-recF$(1)ToI$(2)

.PHONY: test-level2-recF$(1)ToI$(2)
test-level2-recF$(1)ToI$(2): test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 0" f$(1)_to_ui$(2) -rnear_even -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 1" f$(1)_to_ui$(2) -rminMag -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 2" f$(1)_to_ui$(2) -rmin -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 3" f$(1)_to_ui$(2) -rmax -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 4" f$(1)_to_ui$(2) -rnear_maxMag -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 0 6" f$(1)_to_ui$(2) -rodd -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 0" f$(1)_to_i$(2) -rnear_even -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 1" f$(1)_to_i$(2) -rminMag -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 2" f$(1)_to_i$(2) -rmin -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 3" f$(1)_to_i$(2) -rmax -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 4" f$(1)_to_i$(2) -rnear_maxMag -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp
	$(TESTFLOAT_GEN) -prefix "0 1 6" f$(1)_to_i$(2) -rodd -exact -level 2 | $(SIMULATE_VVP) test_recF$(1)ToI$(2).vvp

test-level2-recFNToIN: test-level2-recF$(1)ToI$(2)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_compareRecFN_template

test_compareRecF$(1).vvp: $(SRC_COMMON) compareRecFN.v test_compareRecFN.v
	$(COMPILE_V) -s test_compareRecF$(1) -o $$@ $$^

.PHONY: test-level1-compareRecF$(1)
test-level1-compareRecF$(1): test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 0" f$(1)_lt_quiet | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 1" f$(1)_le_quiet | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 2" f$(1)_eq | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 0" f$(1)_lt | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 1" f$(1)_le | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 2" f$(1)_eq_signaling | $(SIMULATE_VVP) test_compareRecF$(1).vvp

test-level1-compareRecFN: test-level1-compareRecF$(1)

.PHONY: test-level2-compareRecF$(1)
test-level2-compareRecF$(1): test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 0" f$(1)_lt_quiet -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 1" f$(1)_le_quiet -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "0 2" f$(1)_eq -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 0" f$(1)_lt -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 1" f$(1)_le -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp
	$(TESTFLOAT_GEN) -prefix "1 2" f$(1)_eq_signaling -level 2 | $(SIMULATE_VVP) test_compareRecF$(1).vvp

test-level2-compareRecFN: test-level2-compareRecF$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define otherTest_template

test_$(3).vvp: $(SRC_COMMON) $(2)
	$(COMPILE_V) -s test_$(3) -o $$@ $$^

.PHONY: test-level1-$(3)
test-level1-$(3): test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 0" $(4) -tininessbefore -rnear_even | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 1" $(4) -tininessbefore -rminMag | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 2" $(4) -tininessbefore -rmin | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 3" $(4) -tininessbefore -rmax | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 4" $(4) -tininessbefore -rnear_maxMag | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 6" $(4) -tininessbefore -rodd | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 0" $(4) -rnear_even | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 1" $(4) -rminMag | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 2" $(4) -rmin | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 3" $(4) -rmax | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 4" $(4) -rnear_maxMag | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 6" $(4) -rodd | $(SIMULATE_VVP) test_$(3).vvp

test-level1-$(1): test-level1-$(3)

.PHONY: test-level2-$(3)
test-level2-$(3): test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 0" $(4) -tininessbefore -rnear_even -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 1" $(4) -tininessbefore -rminMag -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 2" $(4) -tininessbefore -rmin -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 3" $(4) -tininessbefore -rmax -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 4" $(4) -tininessbefore -rnear_maxMag -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "0 6" $(4) -tininessbefore -rodd -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 0" $(4) -rnear_even -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 1" $(4) -rminMag -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 2" $(4) -rmin -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 3" $(4) -rmax -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 4" $(4) -rnear_maxMag -level 2 | $(SIMULATE_VVP) test_$(3).vvp
	$(TESTFLOAT_GEN) -prefix "1 6" $(4) -rodd -level 2 | $(SIMULATE_VVP) test_$(3).vvp

test-level2-$(1): test-level2-$(3)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

$(eval $(call test_recFNToFN_template,16))
$(eval $(call test_recFNToFN_template,32))
$(eval $(call test_recFNToFN_template,64))
$(eval $(call test_recFNToFN_template,128))

$(eval $(call test_iNToRecFN_template,32,16))
$(eval $(call test_iNToRecFN_template,32,32))
$(eval $(call test_iNToRecFN_template,32,64))
$(eval $(call test_iNToRecFN_template,32,128))
$(eval $(call test_iNToRecFN_template,64,16))
$(eval $(call test_iNToRecFN_template,64,32))
$(eval $(call test_iNToRecFN_template,64,64))
$(eval $(call test_iNToRecFN_template,64,128))

$(eval $(call test_recFNToIN_template,16,32))
$(eval $(call test_recFNToIN_template,16,64))
$(eval $(call test_recFNToIN_template,32,32))
$(eval $(call test_recFNToIN_template,32,64))
$(eval $(call test_recFNToIN_template,64,32))
$(eval $(call test_recFNToIN_template,64,64))
$(eval $(call test_recFNToIN_template,128,32))
$(eval $(call test_recFNToIN_template,128,64))

SRC_TEST_RECFNTORECFN = \
  recFNToRecFN.v \
  test_recFNToRecFN.v \

$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF16ToRecF32,f16_to_f32))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF16ToRecF64,f16_to_f64))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF16ToRecF128,f16_to_f128))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF32ToRecF16,f32_to_f16))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF32ToRecF64,f32_to_f64))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF32ToRecF128,f32_to_f128))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF64ToRecF16,f64_to_f16))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF64ToRecF32,f64_to_f32))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF64ToRecF128,f64_to_f128))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF128ToRecF16,f128_to_f16))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF128ToRecF32,f128_to_f32))
$(eval $(call otherTest_template,recFNToRecFN,$(SRC_TEST_RECFNTORECFN),recF128ToRecF64,f128_to_f64))

SRC_TEST_ADDRECFN_ADD = \
  addRecFN.v \
  test_addRecFN_add.v \

$(eval $(call otherTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN_ADD),addRecF16_add,f16_add))
$(eval $(call otherTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN_ADD),addRecF32_add,f32_add))
$(eval $(call otherTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN_ADD),addRecF64_add,f64_add))
$(eval $(call otherTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN_ADD),addRecF128_add,f128_add))

SRC_TEST_ADDRECFN_SUB = \
  addRecFN.v \
  test_addRecFN_sub.v \

$(eval $(call otherTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN_SUB),addRecF16_sub,f16_sub))
$(eval $(call otherTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN_SUB),addRecF32_sub,f32_sub))
$(eval $(call otherTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN_SUB),addRecF64_sub,f64_sub))
$(eval $(call otherTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN_SUB),addRecF128_sub,f128_sub))

SRC_TEST_MULRECFN = \
  mulRecFN.v \
  test_mulRecFN.v \

$(eval $(call otherTest_template,mulRecFN,$(SRC_TEST_MULRECFN),mulRecF16,f16_mul))
$(eval $(call otherTest_template,mulRecFN,$(SRC_TEST_MULRECFN),mulRecF32,f32_mul))
$(eval $(call otherTest_template,mulRecFN,$(SRC_TEST_MULRECFN),mulRecF64,f64_mul))
$(eval $(call otherTest_template,mulRecFN,$(SRC_TEST_MULRECFN),mulRecF128,f128_mul))

SRC_TEST_MULADDRECFN_ADD = \
  mulAddRecFN.v \
  test_mulAddRecFN_add.v \

$(eval $(call otherTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN_ADD),mulAddRecF16_add,f16_add))
$(eval $(call otherTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN_ADD),mulAddRecF32_add,f32_add))
$(eval $(call otherTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN_ADD),mulAddRecF64_add,f64_add))
$(eval $(call otherTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN_ADD),mulAddRecF128_add,f128_add))

SRC_TEST_MULADDRECFN_MUL = \
  mulAddRecFN.v \
  test_mulAddRecFN_mul.v \

$(eval $(call otherTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN_MUL),mulAddRecF16_mul,f16_mul))
$(eval $(call otherTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN_MUL),mulAddRecF32_mul,f32_mul))
$(eval $(call otherTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN_MUL),mulAddRecF64_mul,f64_mul))
$(eval $(call otherTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN_MUL),mulAddRecF128_mul,f128_mul))

SRC_TEST_MULADDRECFN = \
  mulAddRecFN.v \
  test_mulAddRecFN.v \

$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF16,f16_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF32,f32_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF64,f64_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF128,f128_mulAdd))

SRC_TEST_DIVSQRTRECFN_SMALL_DIV = \
  divSqrtRecFN_small.v \
  test_divSqrtRecFN_small_div.v \

$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL_DIV),divSqrtRecF16_small_div,f16_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL_DIV),divSqrtRecF32_small_div,f32_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL_DIV),divSqrtRecF64_small_div,f64_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL_DIV),divSqrtRecF128_small_div,f128_div))

SRC_TEST_DIVSQRTRECFN_SMALL_SQRT = \
  divSqrtRecFN_small.v \
  test_divSqrtRecFN_small_sqrt.v \

$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL_SQRT),divSqrtRecF16_small_sqrt,f16_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL_SQRT),divSqrtRecF32_small_sqrt,f32_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL_SQRT),divSqrtRecF64_small_sqrt,f64_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL_SQRT),divSqrtRecF128_small_sqrt,f128_sqrt))

$(eval $(call test_compareRecFN_template,16))
$(eval $(call test_compareRecFN_template,32))
$(eval $(call test_compareRecFN_template,64))
$(eval $(call test_compareRecFN_template,128))

test-level1-addRecF16: test-level1-addRecF16_add test-level1-addRecF16_sub
test-level1-addRecF32: test-level1-addRecF32_add test-level1-addRecF32_sub
test-level1-addRecF64: test-level1-addRecF64_add test-level1-addRecF64_sub
test-level1-addRecF128: test-level1-addRecF128_add test-level1-addRecF128_sub
test-level1-addRecFN: \
  test-level1-addRecF16 \
  test-level1-addRecF32 \
  test-level1-addRecF64 \
  test-level1-addRecF128 \

test-level1-all1: \
  test-level1-recFNToFN \
  test-level1-iNToRecFN \
  test-level1-recFNToIN \
  test-level1-recFNToRecFN \
  test-level1-divSqrtRecFN_small_sqrt \

test-level1-all2: \
  test-level1-addRecFN \
  test-level1-mulRecFN \
  test-level1-mulAddRecFN_add \
  test-level1-mulAddRecFN_mul \
  test-level1-divSqrtRecFN_small_div \
  test-level1-compareRecFN \

test-level1: test-level1-all1 test-level1-all2 test-level1-mulAddRecFN

test-level2-addRecF16: test-level2-addRecF16_add test-level2-addRecF16_sub
test-level2-addRecF32: test-level2-addRecF32_add test-level2-addRecF32_sub
test-level2-addRecF64: test-level2-addRecF64_add test-level2-addRecF64_sub
test-level2-addRecF128: test-level2-addRecF128_add test-level2-addRecF128_sub
test-level2-addRecFN: \
  test-level2-addRecF16 \
  test-level2-addRecF32 \
  test-level2-addRecF64 \
  test-level2-addRecF128 \

test-level2-all1: \
  test-level2-recFNToFN \
  test-level2-iNToRecFN \
  test-level2-recFNToIN \
  test-level2-recFNToRecFN \
  test-level2-divSqrtRecFN_small_sqrt \

test-level2-all2: \
  test-level2-addRecFN \
  test-level2-mulRecFN \
  test-level2-mulAddRecFN_add \
  test-level2-mulAddRecFN_mul \
  test-level2-divSqrtRecFN_small_div \
  test-level2-compareRecFN \

test-level2: test-level2-all1 test-level2-all2 test-level2-mulAddRecFN

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

clean:
	$(DELETE) *.vvp

