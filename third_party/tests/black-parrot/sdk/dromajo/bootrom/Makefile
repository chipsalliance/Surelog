#******************************************************************************
# Copyright (C) 2018,2019,2020, Esperanto Technologies Inc.
# The copyright to the computer program(s) herein is the
# property of Esperanto Technologies, Inc. All Rights Reserved.
# The program(s) may be used and/or copied only with
# the written permission of Esperanto Technologies and
# in accordance with the terms and conditions stipulated in the
# agreement/contract under which the program(s) have been supplied.
#------------------------------------------------------------------------------

# RISCV environment variable must be set

MEMORY_START=0x8000000000
build_dir=.
CC=$(RISCV)/bin/riscv64-unknown-elf-gcc
OBJCOPY=$(RISCV)/bin/riscv64-unknown-elf-objcopy
CFLAGS=-march=rv64gc -mabi=lp64 -O2 -std=gnu11 -Wall -I. -nostartfiles -fno-common -g -DMEMORY_START=$(MEMORY_START)
LFLAGS=-static -nostdlib -Ttext=10000

elf := $(build_dir)/bootrom.elf
$(elf): bootrom.S
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $<

.PHONY: elf
elf: $(elf)

bin := $(build_dir)/bootrom.bin
$(bin): $(elf)
	$(OBJCOPY) -O binary $< $@

.PHONY: bin
bin: $(bin)

.PHONY: clean
clean::
	rm -rf $(hex) $(elf)
