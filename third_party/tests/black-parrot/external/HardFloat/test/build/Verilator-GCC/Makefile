
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
CFLAGS ?= -O2

EXE =

TRANSLATE_V_C_MK = \
  verilator -Wno-WIDTH -I$(SOURCE_DIR)/$(SPECIALIZE_TYPE) -I$(SOURCE_DIR) \
    --cc --exe --compiler gcc -CFLAGS "-I.. $(CFLAGS)"
OBJ_DIR = obj_dir
TESTFLOAT_GEN = testfloat_gen

MKDIR = mkdir -p
COPY = cp -p
DELETE = rm -f
DELETE_DIR = rm -rf

.PHONY: \
  default \
  test-level1-fNToRecFN \
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
  test-level1-compareRecFN \
  test-level1-all1 \
  test-level1-all2 \
  test-level1 \
  test-level2-fNToRecFN \
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
  test-level2-compareRecFN \
  test-level2-all1 \
  test-level2-all2 \
  test-level2 \
  clean \

default:
	@echo "Invalid Makefile target."
	@echo "(Valid targets include 'test-level1' and 'test-level2'.)"

vpath %.vi \
  $(SOURCE_DIR)/$(SPECIALIZE_TYPE) \
  $(SOURCE_DIR) \

vpath %.v \
  $(TEST_SOURCE_DIR)/Verilator \
  $(TEST_SOURCE_DIR) \
  $(SOURCE_DIR)/$(SPECIALIZE_TYPE) \
  $(SOURCE_DIR) \

vpath %.h $(TEST_SOURCE_DIR)/Verilator
vpath %.c $(TEST_SOURCE_DIR)/Verilator
vpath %.cpp $(TEST_SOURCE_DIR)/Verilator

INCLUDES = \
  HardFloat_consts.vi \
  HardFloat_specialize.vi \
  HardFloat_localFuncs.vi \
  testCommon.h \

SRC_COMMON = \
  HardFloat_primitives.v \
  HardFloat_specialize.v \
  isSigNaNRecFN.v \
  HardFloat_rawFN.v \
  testCommon.c \

$(SRC_COMMON): $(INCLUDES)

.SUFFIXES:

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define genericTest_template

$(OBJ_DIR)/test_$(3)-$(4).cpp: test_$(3).cpp
	$(MKDIR) $(OBJ_DIR)
	$(COPY) $$< $$@

test_$(4)$(EXE): $(SRC_COMMON) $(2) $(OBJ_DIR)/test_$(3)-$(4).cpp
	$(TRANSLATE_V_C_MK) --top-module $(4) -CFLAGS "-DunitName=$(4) -DunitVHeader=\\\"V$(4).h\\\" -DCHECKNANS=$(6) -I../../../source/Verilator" $$^
	make -C $(OBJ_DIR) -f V$(4).mk
	$(COPY) $(OBJ_DIR)/V$(4)$(EXE) test_$(4)$(EXE)

.PHONY: test-level1-$(4)
test-level1-$(4): test_$(4)$(EXE)
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rnear_even | ./test_$(4)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rminMag | ./test_$(4)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rmin | ./test_$(4)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rmax | ./test_$(4)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rnear_maxMag | ./test_$(4)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rodd | ./test_$(4)$(EXE) 0 6
	$(TESTFLOAT_GEN) $(5) -rnear_even | ./test_$(4)$(EXE) 1 0
	$(TESTFLOAT_GEN) $(5) -rminMag | ./test_$(4)$(EXE) 1 1
	$(TESTFLOAT_GEN) $(5) -rmin | ./test_$(4)$(EXE) 1 2
	$(TESTFLOAT_GEN) $(5) -rmax | ./test_$(4)$(EXE) 1 3
	$(TESTFLOAT_GEN) $(5) -rnear_maxMag | ./test_$(4)$(EXE) 1 4
	$(TESTFLOAT_GEN) $(5) -rodd | ./test_$(4)$(EXE) 1 6

test-level1-$(1): test-level1-$(4)

.PHONY: test-level2-$(4)
test-level2-$(4): test_$(4)$(EXE)
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rnear_even -level 2 | ./test_$(4)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rminMag -level 2 | ./test_$(4)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rmin -level 2 | ./test_$(4)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rmax -level 2 | ./test_$(4)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rnear_maxMag -level 2 | ./test_$(4)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(5) -tininessbefore -rodd -level 2 | ./test_$(4)$(EXE) 0 6
	$(TESTFLOAT_GEN) $(5) -rnear_even -level 2 | ./test_$(4)$(EXE) 1 0
	$(TESTFLOAT_GEN) $(5) -rminMag -level 2 | ./test_$(4)$(EXE) 1 1
	$(TESTFLOAT_GEN) $(5) -rmin -level 2 | ./test_$(4)$(EXE) 1 2
	$(TESTFLOAT_GEN) $(5) -rmax -level 2 | ./test_$(4)$(EXE) 1 3
	$(TESTFLOAT_GEN) $(5) -rnear_maxMag -level 2 | ./test_$(4)$(EXE) 1 4
	$(TESTFLOAT_GEN) $(5) -rodd -level 2 | ./test_$(4)$(EXE) 1 6

test-level2-$(1): test-level2-$(4)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_fNtoRecFN_template

test_f$(1)ToRecF$(1)$(EXE): $(SRC_COMMON) fNToRecFN.v fNToRecFN_spec.v test_f$(1)ToRecF$(1).cpp
	$(TRANSLATE_V_C_MK) --top-module f$(1)ToRecF$(1) $$^
	make -C $(OBJ_DIR) -f Vf$(1)ToRecF$(1).mk
	$(COPY) $(OBJ_DIR)/Vf$(1)ToRecF$(1)$(EXE) test_f$(1)ToRecF$(1)$(EXE)

.PHONY: test-level1-f$(1)ToRecF$(1)
test-level1-f$(1)ToRecF$(1): test_f$(1)ToRecF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1) | ./test_f$(1)ToRecF$(1)$(EXE)

test-level1-fNToRecFN: test-level1-f$(1)ToRecF$(1)

.PHONY: test-level2-f$(1)ToRecF$(1)
test-level2-f$(1)ToRecF$(1): test_f$(1)ToRecF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1) -level 2 | ./test_f$(1)ToRecF$(1)$(EXE)

test-level2-fNToRecFN: test-level2-f$(1)ToRecF$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_recFNtoFN_template

test_recF$(1)ToF$(1)$(EXE): $(SRC_COMMON) recFNToFN.v recFNToFN_spec.v test_recF$(1)ToF$(1).cpp
	$(TRANSLATE_V_C_MK) --top-module recF$(1)ToF$(1) $$^
	make -C $(OBJ_DIR) -f VrecF$(1)ToF$(1).mk
	$(COPY) $(OBJ_DIR)/VrecF$(1)ToF$(1)$(EXE) test_recF$(1)ToF$(1)$(EXE)

.PHONY: test-level1-recF$(1)ToF$(1)
test-level1-recF$(1)ToF$(1): test_recF$(1)ToF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1) | ./test_recF$(1)ToF$(1)$(EXE)

test-level1-recFNToFN: test-level1-recF$(1)ToF$(1)

.PHONY: test-level2-recF$(1)ToF$(1)
test-level2-recF$(1)ToF$(1): test_recF$(1)ToF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1) -level 2 | ./test_recF$(1)ToF$(1)$(EXE)

test-level2-recFNToFN: test-level2-recF$(1)ToF$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_recFNtoIN_template

test_$(1)$(EXE): $(SRC_COMMON) recFNToIN.v recFNToIN_spec.v test_$(1).cpp
	$(TRANSLATE_V_C_MK) --top-module $(1) $$^
	make -C $(OBJ_DIR) -f V$(1).mk
	$(COPY) $(OBJ_DIR)/V$(1)$(EXE) test_$(1)$(EXE)

.PHONY: test-level1-$(1)
test-level1-$(1): test_$(1)$(EXE)
	$(TESTFLOAT_GEN) $(2) -rnear_even -exact | ./test_$(1)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(2) -rminMag -exact | ./test_$(1)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(2) -rmin -exact | ./test_$(1)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(2) -rmax -exact | ./test_$(1)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(2) -rnear_maxMag -exact | ./test_$(1)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(2) -rodd -exact | ./test_$(1)$(EXE) 0 6

test-level1-recFNToIN: test-level1-$(1)

.PHONY: test-level2-$(1)
test-level2-$(1): test_$(1)$(EXE)
	$(TESTFLOAT_GEN) $(2) -rnear_even -exact -level 2 | ./test_$(1)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(2) -rminMag -exact -level 2 | ./test_$(1)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(2) -rmin -exact -level 2 | ./test_$(1)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(2) -rmax -exact -level 2 | ./test_$(1)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(2) -rnear_maxMag -exact -level 2 | ./test_$(1)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(2) -rodd -exact -level 2 | ./test_$(1)$(EXE) 0 6

test-level2-recFNToIN: test-level2-$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define test_compareRecFN_template

test_compareRecF$(1)$(EXE): $(SRC_COMMON) compareRecFN.v compareRecFN_spec.v test_compareRecF$(1).cpp
	$(TRANSLATE_V_C_MK) --top-module compareRecF$(1) $$^
	make -C $(OBJ_DIR) -f VcompareRecF$(1).mk
	$(COPY) $(OBJ_DIR)/VcompareRecF$(1)$(EXE) test_compareRecF$(1)$(EXE)

.PHONY: test-level1-compareRecF$(1)
test-level1-compareRecF$(1): test_compareRecF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1)_lt_quiet | ./test_compareRecF$(1)$(EXE) 0 0
	$(TESTFLOAT_GEN) f$(1)_le_quiet | ./test_compareRecF$(1)$(EXE) 0 1
	$(TESTFLOAT_GEN) f$(1)_eq | ./test_compareRecF$(1)$(EXE) 0 2
	$(TESTFLOAT_GEN) f$(1)_lt | ./test_compareRecF$(1)$(EXE) 1 0
	$(TESTFLOAT_GEN) f$(1)_le | ./test_compareRecF$(1)$(EXE) 1 1
	$(TESTFLOAT_GEN) f$(1)_eq_signaling | ./test_compareRecF$(1)$(EXE) 1 2

test-level1-compareRecFN: test-level1-compareRecF$(1)

.PHONY: test-level2-compareRecF$(1)
test-level2-compareRecF$(1): test_compareRecF$(1)$(EXE)
	$(TESTFLOAT_GEN) f$(1)_lt_quiet -level 2 | ./test_compareRecF$(1)$(EXE) 0 0
	$(TESTFLOAT_GEN) f$(1)_le_quiet -level 2 | ./test_compareRecF$(1)$(EXE) 0 1
	$(TESTFLOAT_GEN) f$(1)_eq -level 2 | ./test_compareRecF$(1)$(EXE) 0 2
	$(TESTFLOAT_GEN) f$(1)_lt -level 2 | ./test_compareRecF$(1)$(EXE) 1 0
	$(TESTFLOAT_GEN) f$(1)_le -level 2 | ./test_compareRecF$(1)$(EXE) 1 1
	$(TESTFLOAT_GEN) f$(1)_eq_signaling -level 2 | ./test_compareRecF$(1)$(EXE) 1 2

test-level2-compareRecFN: test-level2-compareRecF$(1)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

define otherTest_template

test_$(3)$(EXE): $(SRC_COMMON) $(2) test_$(3).cpp
	$(TRANSLATE_V_C_MK) --top-module $(3) $$^
	make -C $(OBJ_DIR) -f V$(3).mk
	$(COPY) $(OBJ_DIR)/V$(3)$(EXE) test_$(3)$(EXE)

.PHONY: test-level1-$(3)
test-level1-$(3): test_$(3)$(EXE)
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rnear_even | ./test_$(3)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rminMag | ./test_$(3)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rmin | ./test_$(3)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rmax | ./test_$(3)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rnear_maxMag | ./test_$(3)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rodd | ./test_$(3)$(EXE) 0 6
	$(TESTFLOAT_GEN) $(4) -rnear_even | ./test_$(3)$(EXE) 1 0
	$(TESTFLOAT_GEN) $(4) -rminMag | ./test_$(3)$(EXE) 1 1
	$(TESTFLOAT_GEN) $(4) -rmin | ./test_$(3)$(EXE) 1 2
	$(TESTFLOAT_GEN) $(4) -rmax | ./test_$(3)$(EXE) 1 3
	$(TESTFLOAT_GEN) $(4) -rnear_maxMag | ./test_$(3)$(EXE) 1 4
	$(TESTFLOAT_GEN) $(4) -rodd | ./test_$(3)$(EXE) 1 6

test-level1-$(1): test-level1-$(3)

.PHONY: test-level2-$(3)
test-level2-$(3): test_$(3)$(EXE)
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rnear_even -level 2 | ./test_$(3)$(EXE) 0 0
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rminMag -level 2 | ./test_$(3)$(EXE) 0 1
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rmin -level 2 | ./test_$(3)$(EXE) 0 2
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rmax -level 2 | ./test_$(3)$(EXE) 0 3
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rnear_maxMag -level 2 | ./test_$(3)$(EXE) 0 4
	$(TESTFLOAT_GEN) $(4) -tininessbefore -rodd -level 2 | ./test_$(3)$(EXE) 0 6
	$(TESTFLOAT_GEN) $(4) -rnear_even -level 2 | ./test_$(3)$(EXE) 1 0
	$(TESTFLOAT_GEN) $(4) -rminMag -level 2 | ./test_$(3)$(EXE) 1 1
	$(TESTFLOAT_GEN) $(4) -rmin -level 2 | ./test_$(3)$(EXE) 1 2
	$(TESTFLOAT_GEN) $(4) -rmax -level 2 | ./test_$(3)$(EXE) 1 3
	$(TESTFLOAT_GEN) $(4) -rnear_maxMag -level 2 | ./test_$(3)$(EXE) 1 4
	$(TESTFLOAT_GEN) $(4) -rodd -level 2 | ./test_$(3)$(EXE) 1 6

test-level2-$(1): test-level2-$(3)

endef

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------

$(eval $(call test_fNtoRecFN_template,16))
$(eval $(call test_fNtoRecFN_template,32))
$(eval $(call test_fNtoRecFN_template,64))
$(eval $(call test_fNtoRecFN_template,128))

$(eval $(call test_recFNtoFN_template,16))
$(eval $(call test_recFNtoFN_template,32))
$(eval $(call test_recFNtoFN_template,64))
$(eval $(call test_recFNtoFN_template,128))

SRC_TEST_INTORECFN = \
  iNToRecFN.v \
  iNToRecFN_spec.v \

$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui32ToRecF16,ui32_to_f16))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui32ToRecF32,ui32_to_f32))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui32ToRecF64,ui32_to_f64))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui32ToRecF128,ui32_to_f128))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui64ToRecF16,ui64_to_f16))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui64ToRecF32,ui64_to_f32))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui64ToRecF64,ui64_to_f64))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),ui64ToRecF128,ui64_to_f128))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i32ToRecF16,i32_to_f16))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i32ToRecF32,i32_to_f32))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i32ToRecF64,i32_to_f64))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i32ToRecF128,i32_to_f128))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i64ToRecF16,i64_to_f16))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i64ToRecF32,i64_to_f32))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i64ToRecF64,i64_to_f64))
$(eval $(call otherTest_template,iNToRecFN,$(SRC_TEST_INTORECFN),i64ToRecF128,i64_to_f128))

$(eval $(call test_recFNtoIN_template,recF16ToUi32,f16_to_ui32))
$(eval $(call test_recFNtoIN_template,recF16ToUi64,f16_to_ui64))
$(eval $(call test_recFNtoIN_template,recF16ToI32,f16_to_i32))
$(eval $(call test_recFNtoIN_template,recF16ToI64,f16_to_i64))
$(eval $(call test_recFNtoIN_template,recF32ToUi32,f32_to_ui32))
$(eval $(call test_recFNtoIN_template,recF32ToUi64,f32_to_ui64))
$(eval $(call test_recFNtoIN_template,recF32ToI32,f32_to_i32))
$(eval $(call test_recFNtoIN_template,recF32ToI64,f32_to_i64))
$(eval $(call test_recFNtoIN_template,recF64ToUi32,f64_to_ui32))
$(eval $(call test_recFNtoIN_template,recF64ToUi64,f64_to_ui64))
$(eval $(call test_recFNtoIN_template,recF64ToI32,f64_to_i32))
$(eval $(call test_recFNtoIN_template,recF64ToI64,f64_to_i64))
$(eval $(call test_recFNtoIN_template,recF128ToUi32,f128_to_ui32))
$(eval $(call test_recFNtoIN_template,recF128ToUi64,f128_to_ui64))
$(eval $(call test_recFNtoIN_template,recF128ToI32,f128_to_i32))
$(eval $(call test_recFNtoIN_template,recF128ToI64,f128_to_i64))

SRC_TEST_RECFNTORECFN = \
  recFNToRecFN.v \
  recFNToRecFN_spec.v \

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

SRC_TEST_ADDRECFN = \
  addRecFN.v \
  addRecFN_spec.v \

$(eval $(call genericTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN),abz_recF16,addRecF16_add,f16_add,true))
$(eval $(call genericTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN),abz_recF32,addRecF32_add,f32_add,true))
$(eval $(call genericTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN),abz_recF64,addRecF64_add,f64_add,true))
$(eval $(call genericTest_template,addRecFN_add,$(SRC_TEST_ADDRECFN),abz_recF128,addRecF128_add,f128_add,true))

$(eval $(call genericTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN),abz_recF16,addRecF16_sub,f16_sub,true))
$(eval $(call genericTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN),abz_recF32,addRecF32_sub,f32_sub,true))
$(eval $(call genericTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN),abz_recF64,addRecF64_sub,f64_sub,true))
$(eval $(call genericTest_template,addRecFN_sub,$(SRC_TEST_ADDRECFN),abz_recF128,addRecF128_sub,f128_sub,true))

SRC_TEST_MULRECFN = \
  mulRecFN.v \
  mulRecFN_spec.v \

$(eval $(call genericTest_template,mulRecFN,$(SRC_TEST_MULRECFN),abz_recF16,mulRecF16,f16_mul,true))
$(eval $(call genericTest_template,mulRecFN,$(SRC_TEST_MULRECFN),abz_recF32,mulRecF32,f32_mul,true))
$(eval $(call genericTest_template,mulRecFN,$(SRC_TEST_MULRECFN),abz_recF64,mulRecF64,f64_mul,true))
$(eval $(call genericTest_template,mulRecFN,$(SRC_TEST_MULRECFN),abz_recF128,mulRecF128,f128_mul,true))

SRC_TEST_MULADDRECFN = \
  mulAddRecFN.v \
  mulAddRecFN_spec.v \

$(eval $(call genericTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN),abz_recF16,mulAddRecF16_add,f16_add,false))
$(eval $(call genericTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN),abz_recF32,mulAddRecF32_add,f32_add,false))
$(eval $(call genericTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN),abz_recF64,mulAddRecF64_add,f64_add,false))
$(eval $(call genericTest_template,mulAddRecFN_add,$(SRC_TEST_MULADDRECFN),abz_recF128,mulAddRecF128_add,f128_add,false))

$(eval $(call genericTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN),abz_recF16,mulAddRecF16_mul,f16_mul,true))
$(eval $(call genericTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN),abz_recF32,mulAddRecF32_mul,f32_mul,true))
$(eval $(call genericTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN),abz_recF64,mulAddRecF64_mul,f64_mul,true))
$(eval $(call genericTest_template,mulAddRecFN_mul,$(SRC_TEST_MULADDRECFN),abz_recF128,mulAddRecF128_mul,f128_mul,true))

$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF16,f16_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF32,f32_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF64,f64_mulAdd))
$(eval $(call otherTest_template,mulAddRecFN,$(SRC_TEST_MULADDRECFN),mulAddRecF128,f128_mulAdd))

SRC_TEST_DIVSQRTRECFN_SMALL = \
  divSqrtRecFN_small.v \
  divSqrtRecFN_small_spec.v \

$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF16_small_div,f16_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF32_small_div,f32_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF64_small_div,f64_div))
$(eval $(call otherTest_template,divSqrtRecFN_small_div,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF128_small_div,f128_div))

$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF16_small_sqrt,f16_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF32_small_sqrt,f32_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF64_small_sqrt,f64_sqrt))
$(eval $(call otherTest_template,divSqrtRecFN_small_sqrt,$(SRC_TEST_DIVSQRTRECFN_SMALL),divSqrtRecF128_small_sqrt,f128_sqrt))

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
  test-level1-fNToRecFN \
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
  test-level2-fNToRecFN \
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
	$(DELETE_DIR) $(OBJ_DIR)
	$(DELETE) test_*

