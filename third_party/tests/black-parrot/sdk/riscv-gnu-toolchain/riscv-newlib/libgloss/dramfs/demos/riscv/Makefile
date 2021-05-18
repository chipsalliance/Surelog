TOOLS := ../bsg/rem_bsg_manycore/software/riscv-tools/riscv-install/bin
ISA := rv32im
OBJS := lfs_mem.o crt.o dramfs_intf.o fhello.o 
INS := hello.txt

run: fhello
	$(TOOLS)/spike -l --isa=$(ISA) fhello 2> spike.log

fhello: $(OBJS) link.ld
	$(TOOLS)/riscv32-unknown-elf-gcc -nostartfiles -T link.ld $(OBJS) -o $@

%.o : %.c
	$(TOOLS)/riscv32-unknown-elf-gcc -c $< -o $@

%.o : %.S
	$(TOOLS)/riscv32-unknown-elf-gcc -c $< -o $@

lfs_mem.c: $(INS)
	$(TOOLS)/../riscv32-unknown-elf/bin/dramfs_mklfs 128 256 $(INS) > $@

clean:
	-rm *.o lfs_mem.c *.log fhello

.PHONY: run clean
