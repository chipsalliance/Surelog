CROSS_COMPILE  ?= lm32-elf-

CC      = $(CROSS_COMPILE)gcc
AS      = $(CROSS_COMPILE)as
AS      = $(CC) -x assembler
SIZE    = $(CROSS_COMPILE)size
LD      = $(CC)
OBJCOPY = $(CROSS_COMPILE)objcopy

# in case make does not have this already defined
RM ?= rm -f

LDFLAGS = -Tlinker.ld -nostdlib -lgcc
ASFLAGS += -Wa,-I,.

CRT        = crt.o
TESTCASES += test_add.elf
TESTCASES += test_addi.elf
TESTCASES += test_and.elf
TESTCASES += test_andhi.elf
TESTCASES += test_andi.elf
TESTCASES += test_b.elf
TESTCASES += test_be.elf
TESTCASES += test_bg.elf
TESTCASES += test_bge.elf
TESTCASES += test_bgeu.elf
TESTCASES += test_bgu.elf
TESTCASES += test_bi.elf
TESTCASES += test_bne.elf
TESTCASES += test_break.elf
TESTCASES += test_bret.elf
TESTCASES += test_call.elf
TESTCASES += test_calli.elf
TESTCASES += test_cmpe.elf
TESTCASES += test_cmpei.elf
TESTCASES += test_cmpg.elf
TESTCASES += test_cmpgi.elf
TESTCASES += test_cmpge.elf
TESTCASES += test_cmpgei.elf
TESTCASES += test_cmpgeu.elf
TESTCASES += test_cmpgeui.elf
TESTCASES += test_cmpgu.elf
TESTCASES += test_cmpgui.elf
TESTCASES += test_cmpne.elf
TESTCASES += test_cmpnei.elf
TESTCASES += test_divu.elf
TESTCASES += test_eret.elf
TESTCASES += test_lb.elf
TESTCASES += test_lbu.elf
TESTCASES += test_lh.elf
TESTCASES += test_lhu.elf
TESTCASES += test_lw.elf
TESTCASES += test_mmu.elf
TESTCASES += test_modu.elf
TESTCASES += test_mul.elf
TESTCASES += test_muli.elf
TESTCASES += test_nor.elf
TESTCASES += test_nori.elf
TESTCASES += test_or.elf
TESTCASES += test_ori.elf
TESTCASES += test_orhi.elf
#TESTCASES += test_rcsr.elf
TESTCASES += test_ret.elf
TESTCASES += test_sb.elf
TESTCASES += test_scall.elf
TESTCASES += test_sextb.elf
TESTCASES += test_sexth.elf
TESTCASES += test_sh.elf
TESTCASES += test_sl.elf
TESTCASES += test_sli.elf
TESTCASES += test_sr.elf
TESTCASES += test_sri.elf
TESTCASES += test_sru.elf
TESTCASES += test_srui.elf
TESTCASES += test_sub.elf
TESTCASES += test_sw.elf
#TESTCASES += test_wcsr.elf
TESTCASES += test_xnor.elf
TESTCASES += test_xnori.elf
TESTCASES += test_xor.elf
TESTCASES += test_xori.elf

# auto generated  test_mmu with NOPs inserted
TESTCASES += test_mmu_nop1.elf
TESTCASES += test_mmu_nop2.elf
TESTCASES += test_mmu_nop3.elf

all: build

test_mmu_nop1.S: test_mmu.S
	@sed 's|##NOPS##|nop|' $<  > $@

test_mmu_nop2.S: test_mmu.S
	@sed 's|##NOPS##|nop;nop|' $<  > $@

test_mmu_nop3.S: test_mmu.S
	@sed 's|##NOPS##|nop;nop;nop|' $<  > $@

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) -c $< -o $@

%.elf: %.o macros.inc $(CRT)
	$(LD) $(LDFLAGS) $(NOSTDFLAGS) $(CRT) $< -o $@

%.vh: %.elf
	$(OBJCOPY) -O verilog $< $@

build: $(CRT) $(TESTCASES) $(TESTCASES:.elf=.vh)

check: $(TESTCASES:.elf=.vh)
	@$(MAKE) -C .. tb_lm32_system
	@for case in $(TESTCASES:.elf=.vh); do \
		echo -e "\nRunning test case $$case"; \
		vvp ../tb_lm32_system +prog=$$case; \
	done

check_%: test_%.vh
	@$(MAKE) -C .. tb_lm32_system
	vvp ../tb_lm32_system +prog=$<

clean:
	$(RM) $(TESTCASES) $(TESTCASES:.elf=.vh) $(CRT) *nop?.S tb_lm32.vcd
