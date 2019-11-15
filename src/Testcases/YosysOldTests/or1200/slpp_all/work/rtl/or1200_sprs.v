//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's interface to SPRs                                  ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Decoding of SPR addresses and access to SPRs                ////
////                                                              ////
////  To Do:                                                      ////
////   - make it smaller and faster                               ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// $Log: or1200_sprs.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Major update: 
// Structure reordered and bugs fixed. 

// synopsys translate_off
`timescale 1ps/1ps
// synopsys translate_on
//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's definitions                                        ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Defines for the OR1200 core                                 ////
////                                                              ////
////  To Do:                                                      ////
////   - add parameters that are missing                          ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// $Log: or1200_defines.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Defines added, bugs fixed. 

//
// Dump VCD
//
//`define OR1200_VCD_DUMP

//
// Generate debug messages during simulation
//
//`define OR1200_VERBOSE

////////////////////////////////////////////////////////
//
// Typical configuration for an ASIC
//

//
// Target ASIC memories
//
//`define OR1200_ARTISAN_SSP
//`define OR1200_ARTISAN_SDP
//`define OR1200_ARTISAN_STP
//`define OR1200_VIRTUALSILICON_SSP
//`define OR1200_VIRTUALSILICON_STP_T1
//`define OR1200_VIRTUALSILICON_STP_T2

//
// Do not implement Data cache
//

//
// Do not implement Insn cache
//

//
// Do not implement Data MMU
//
//`define OR1200_NO_DMMU

//
// Do not implement Insn MMU
//
//`define OR1200_NO_IMMU

//
// Select between ASIC optimized and generic multiplier
//
//`define OR1200_GENERIC_MULTP2_32X32

//
// Size/type of insn/data cache if implemented
//
// `define OR1200_IC_1W_4KB
// `define OR1200_IC_1W_8KB
// `define OR1200_DC_1W_8KB



//////////////////////////////////////////////////////////
//
// Do not change below unless you know what you are doing
//

//
// Reset active low
//
//`define OR1200_RST_ACT_LOW

//
// Enable RAM BIST
//
// At the moment this only works for Virtual Silicon
// single port RAMs. For other RAMs it has not effect.
// Special wrapper for VS RAMs needs to be provided
// with scan flops to facilitate bist scan.
//
//`define OR1200_BIST

//
// Register OR1200 WISHBONE outputs
// (must be defined/enabled)
//

//
// Register OR1200 WISHBONE inputs
//
// (must be undefined/disabled)
//
//`define OR1200_REGISTERED_INPUTS

//
// Disable bursts if they are not supported by the
// memory subsystem (only affect cache line fill)
//
//`define OR1200_NO_BURSTS
//

//
// WISHBONE retry counter range
//
// 2^value range for retry counter. Retry counter
// is activated whenever *wb_rty_i is asserted and
// until retry counter expires, corresponding
// WISHBONE interface is deactivated.
//
// To disable retry counters and *wb_rty_i all together,
// undefine this macro.
//
//`define OR1200_WB_RETRY 7

//
// WISHBONE Consecutive Address Burst
//
// This was used prior to WISHBONE B3 specification
// to identify bursts. It is no longer needed but
// remains enabled for compatibility with old designs.
//
// To remove *wb_cab_o ports undefine this macro.
//
//`define OR1200_WB_CAB

//
// WISHBONE B3 compatible interface
//
// This follows the WISHBONE B3 specification.
// It is not enabled by default because most
// designs still don't use WB b3.
//
// To enable *wb_cti_o/*wb_bte_o ports,
// define this macro.
//

//
// LOG all WISHBONE accesses
//

//
// Enable additional synthesis directives if using
// _Synopsys_ synthesis tool
//
//`define OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES

//
// Enables default statement in some case blocks
// and disables Synopsys synthesis directive full_case
//
// By default it is enabled. When disabled it
// can increase clock frequency.
//

//
// Operand width / register file address width
//
// (DO NOT CHANGE)
//

//
// l.add/l.addi/l.and and optional l.addc/l.addic
// also set (compare) flag when result of their
// operation equals zero
//
// At the time of writing this, default or32
// C/C++ compiler doesn't generate code that
// would benefit from this optimization.
//
// By default this optimization is disabled to
// save area.
//
//`define OR1200_ADDITIONAL_FLAG_MODIFIERS

//
// Implement l.addc/l.addic instructions
//
// By default implementation of l.addc/l.addic
// instructions is enabled in case you need them.
// If you don't use them, then disable implementation
// to save area.
//

//
// Implement l.sub instruction
//
// By default implementation of l.sub instructions
// is enabled to be compliant with the simulator.
// If you don't use carry bit, then disable
// implementation to save area.
//

//
// Implement carry bit SR[CY]
//
//
// By default implementation of SR[CY] is enabled
// to be compliant with the simulator. However SR[CY]
// is explicitly only used by l.addc/l.addic/l.sub
// instructions and if these three insns are not
// implemented there is not much point having SR[CY].
//

//
// Implement carry bit SR[OV]
//
// Compiler doesn't use this, but other code may like
// to.
//

//
// Implement carry bit SR[OVE]
//
// Overflow interrupt indicator. When enabled, SR[OV] flag
// does not remain asserted after exception.
//


//
// Implement rotate in the ALU
//
// At the time of writing this, or32
// C/C++ compiler doesn't generate rotate
// instructions. However or32 assembler
// can assemble code that uses rotate insn.
// This means that rotate instructions
// must be used manually inserted.
//
// By default implementation of rotate
// is disabled to save area and increase
// clock frequency.
//
//`define OR1200_IMPL_ALU_ROTATE

//
// Type of ALU compare to implement
//
// Try to find which synthesizes with
// most efficient logic use or highest speed.
//
//`define OR1200_IMPL_ALU_COMP1
//`define OR1200_IMPL_ALU_COMP2

//
// Implement Find First/Last '1'
//

//
// Implement l.cust5 ALU instruction
//
//`define OR1200_IMPL_ALU_CUST5

//
// Implement l.extXs and l.extXz instructions
//

//
// Implement multiplier
//
// By default multiplier is implemented
//

//
// Implement multiply-and-accumulate
//
// By default MAC is implemented. To
// implement MAC, multiplier (non-serial) needs to be
// implemented.
//
//`define OR1200_MAC_IMPLEMENTED

//
// Implement optional l.div/l.divu instructions
//
// By default divide instructions are not implemented
// to save area.
//
//

//
// Serial multiplier.
//
//`define OR1200_MULT_SERIAL

//
// Serial divider.
// Uncomment to use a serial divider, otherwise will
// be a generic parallel implementation.
//

//
// Implement HW Single Precision FPU
//
//`define OR1200_FPU_IMPLEMENTED

//
// Clock ratio RISC clock versus WB clock
//
// If you plan to run WB:RISC clock fixed to 1:1, disable
// both defines
//
// For WB:RISC 1:2 or 1:1, enable OR1200_CLKDIV_2_SUPPORTED
// and use clmode to set ratio
//
// For WB:RISC 1:4, 1:2 or 1:1, enable both defines and use
// clmode to set ratio
//
//`define OR1200_CLKDIV_2_SUPPORTED
//`define OR1200_CLKDIV_4_SUPPORTED

//
// Type of register file RAM
//
// Memory macro w/ two ports (see or1200_tpram_32x32.v)
//`define OR1200_RFRAM_TWOPORT
//
// Memory macro dual port (see or1200_dpram.v)

//
// Generic (flip-flop based) register file (see or1200_rfram_generic.v)
//`define OR1200_RFRAM_GENERIC
//  Generic register file supports - 16 registers 

//
// Type of mem2reg aligner to implement.
//
// Once OR1200_IMPL_MEM2REG2 yielded faster
// circuit, however with today tools it will
// most probably give you slower circuit.
//
//`define OR1200_IMPL_MEM2REG2

//
// Reset value and event
//
    
//
// ALUOPs
//
/* LS-nibble encodings correspond to bits [3:0] of instruction */

/* Values sent to ALU from decode unit - not defined by ISA */

// ALU instructions second opcode field

//
// MACOPs
//

//
// Shift/rotate ops
//

//
// Zero/Sign Extend ops
//

// Execution cycles per instruction

// Execution control which will "wait on" a module to finish


// Operand MUX selects

//
// BRANCHOPs
//

//
// LSUOPs
//
// Bit 0: sign extend
// Bits 1-2: 00 doubleword, 01 byte, 10 halfword, 11 singleword
// Bit 3: 0 load, 1 store

// Number of bits of load/store EA precalculated in ID stage
// for balancing ID and EX stages.
//
// Valid range: 2,3,...,30,31

// FETCHOPs

//
// Register File Write-Back OPs
//
// Bit 0: register file write enable
// Bits 3-1: write-back mux selects
//

// Compare instructions

//
// FP OPs
//
// MSbit indicates FPU operation valid
//
// FPU unit from Usselman takes 5 cycles from decode, so 4 ex. cycles
// FP instruction is double precision if bit 4 is set. We're a 32-bit 
// implementation thus do not support double precision FP 
// FP Compare instructions

//
// TAGs for instruction bus
//

//
// TAGs for data bus
//


//////////////////////////////////////////////
//
// ORBIS32 ISA specifics
//

// SHROT_OP position in machine word

//
// Instruction opcode groups (basic)
//
/* */
/* */
/* */
/* */

/////////////////////////////////////////////////////
//
// Exceptions
//

//
// Exception vectors per OR1K architecture:
// 0xPPPPP100 - reset
// 0xPPPPP200 - bus error
// ... etc
// where P represents exception prefix.
//
// Exception vectors can be customized as per
// the following formula:
// 0xPPPPPNVV - exception N
//
// P represents exception prefix
// N represents exception N
// VV represents length of the individual vector space,
//   usually it is 8 bits wide and starts with all bits zero
//

//
// PPPPP and VV parts
//
// Sum of these two defines needs to be 28
//

//
// N part width
//

//
// Definition of exception vectors
//
// To avoid implementation of a certain exception,
// simply comment out corresponding line
//


/////////////////////////////////////////////////////
//
// SPR groups
//

// Bits that define the group

// Width of the group bits

// Bits that define offset inside the group

// List of groups

/////////////////////////////////////////////////////
//
// System group
//

//
// System registers
//

//
// SR bits
//

//
// Bits that define offset inside the group
//

//
// Default Exception Prefix
//
// 1'b0 - OR1200_EXCEPT_EPH0_P (0x0000_0000)
// 1'b1 - OR1200_EXCEPT_EPH1_P (0xF000_0000)
//


//
// FPCSR bits
//

/////////////////////////////////////////////////////
//
// Power Management (PM)
//

// Define it if you want PM implemented
//`define OR1200_PM_IMPLEMENTED

// Bit positions inside PMR (don't change)

// PMR offset inside PM group of registers

// PM group

// Define if PMR can be read/written at any address inside PM group

// Define if reading PMR is allowed

// Define if unused PMR bits should be zero


/////////////////////////////////////////////////////
//
// Debug Unit (DU)
//

// Define it if you want DU implemented

//
// Define if you want HW Breakpoints
// (if HW breakpoints are not implemented
// only default software trapping is
// possible with l.trap insn - this is
// however already enough for use
// with or32 gdb)
//
//`define OR1200_DU_HWBKPTS

// Number of DVR/DCR pairs if HW breakpoints enabled
//	Comment / uncomment DU_DVRn / DU_DCRn pairs bellow according to this number ! 
//	DU_DVR0..DU_DVR7 should be uncommented for 8 DU_DVRDCR_PAIRS 

// Define if you want trace buffer
//	(for now only available for Xilinx Virtex FPGAs)
//`define OR1200_DU_TB_IMPLEMENTED


//
// Address offsets of DU registers inside DU group
//
// To not implement a register, doq not define its address
//

// Position of offset bits inside SPR address

// DCR bits

// DMR1 bits

// DMR2 bits

// DWCR bits

// DSR bits

// DRR bits

// Define if reading DU regs is allowed

// Define if unused DU registers bits should be zero

// Define if IF/LSU status is not needed by devel i/f

/////////////////////////////////////////////////////
//
// Programmable Interrupt Controller (PIC)
//

// Define it if you want PIC implemented

// Define number of interrupt inputs (2-31)

// Address offsets of PIC registers inside PIC group

// Position of offset bits inside SPR address

// Define if you want these PIC registers to be implemented

// Define if reading PIC registers is allowed

// Define if unused PIC register bits should be zero


/////////////////////////////////////////////////////
//
// Tick Timer (TT)
//

// Define it if you want TT implemented

// Address offsets of TT registers inside TT group

// Position of offset bits inside SPR group

// Define if you want these TT registers to be implemented

// TTMR bits

// Define if reading TT registers is allowed


//////////////////////////////////////////////
//
// MAC
//

//
// Shift {MACHI,MACLO} into destination register when executing l.macrc
//
// According to architecture manual there is no shift, so default value is 0.
// However the implementation has deviated in this from the arch manual and had
// hard coded shift by 28 bits which is a useful optimization for MP3 decoding 
// (if using libmad fixed point library). Shifts are no longer default setup, 
// but if you need to remain backward compatible, define your shift bits, which
// were normally
// dest_GPR = {MACHI,MACLO}[59:28]


//////////////////////////////////////////////
//
// Data MMU (DMMU)
//

//
// Address that selects between TLB TR and MR
//

//
// DTLBMR fields
//

//
// DTLBTR fields
//

//
// DTLB configuration
//

//
// Cache inhibit while DMMU is not enabled/implemented
//
// cache inhibited 0GB-4GB		1'b1
// cache inhibited 0GB-2GB		!dcpu_adr_i[31]
// cache inhibited 0GB-1GB 2GB-3GB	!dcpu_adr_i[30]
// cache inhibited 1GB-2GB 3GB-4GB	dcpu_adr_i[30]
// cache inhibited 2GB-4GB (default)	dcpu_adr_i[31]
// cached 0GB-4GB			1'b0
//


//////////////////////////////////////////////
//
// Insn MMU (IMMU)
//

//
// Address that selects between TLB TR and MR
//

//
// ITLBMR fields
//

//
// ITLBTR fields
//

//
// ITLB configuration
//

//
// Cache inhibit while IMMU is not enabled/implemented
// Note: all combinations that use icpu_adr_i cause async loop
//
// cache inhibited 0GB-4GB		1'b1
// cache inhibited 0GB-2GB		!icpu_adr_i[31]
// cache inhibited 0GB-1GB 2GB-3GB	!icpu_adr_i[30]
// cache inhibited 1GB-2GB 3GB-4GB	icpu_adr_i[30]
// cache inhibited 2GB-4GB (default)	icpu_adr_i[31]
// cached 0GB-4GB			1'b0
//


/////////////////////////////////////////////////
//
// Insn cache (IC)
//

// 4 for 16 byte line, 5 for 32 byte lines.
 
//
// IC configurations
//


/////////////////////////////////////////////////
//
// Data cache (DC)
//

// 4 for 16 bytes, 5 for 32 bytes
 
// Define to enable default behavior of cache as write through
// Turning this off enabled write back statergy
//

// Define to enable stores from the stack not doing writethrough.
// EXPERIMENTAL
//`define OR1200_DC_NOSTACKWRITETHROUGH

// Data cache SPR definitions
// Data cache group SPR addresses

//
// DC configurations
//


/////////////////////////////////////////////////
//
// Store buffer (SB)
//

//
// Store buffer
//
// It will improve performance by "caching" CPU stores
// using store buffer. This is most important for function
// prologues because DC can only work in write though mode
// and all stores would have to complete external WB writes
// to memory.
// Store buffer is between DC and data BIU.
// All stores will be stored into store buffer and immediately
// completed by the CPU, even though actual external writes
// will be performed later. As a consequence store buffer masks
// all data bus errors related to stores (data bus errors
// related to loads are delivered normally).
// All pending CPU loads will wait until store buffer is empty to
// ensure strict memory model. Right now this is necessary because
// we don't make destinction between cached and cache inhibited
// address space, so we simply empty store buffer until loads
// can begin.
//
// It makes design a bit bigger, depending what is the number of
// entries in SB FIFO. Number of entries can be changed further
// down.
//
//`define OR1200_SB_IMPLEMENTED

//
// Number of store buffer entries
//
// Verified number of entries are 4 and 8 entries
// (2 and 3 for OR1200_SB_LOG). OR1200_SB_ENTRIES must
// always match 2**OR1200_SB_LOG.
// To disable store buffer, undefine
// OR1200_SB_IMPLEMENTED.
//


/////////////////////////////////////////////////
//
// Quick Embedded Memory (QMEM)
//

//
// Quick Embedded Memory
//
// Instantiation of dedicated insn/data memory (RAM or ROM).
// Insn fetch has effective throughput 1insn / clock cycle.
// Data load takes two clock cycles / access, data store
// takes 1 clock cycle / access (if there is no insn fetch)).
// Memory instantiation is shared between insn and data,
// meaning if insn fetch are performed, data load/store
// performance will be lower.
//
// Main reason for QMEM is to put some time critical functions
// into this memory and to have predictable and fast access
// to these functions. (soft fpu, context switch, exception
// handlers, stack, etc)
//
// It makes design a bit bigger and slower. QMEM sits behind
// IMMU/DMMU so all addresses are physical (so the MMUs can be
// used with QMEM and QMEM is seen by the CPU just like any other
// memory in the system). IC/DC are sitting behind QMEM so the
// whole design timing might be worse with QMEM implemented.
//
//`define OR1200_QMEM_IMPLEMENTED

//
// Base address and mask of QMEM
//
// Base address defines first address of QMEM. Mask defines
// QMEM range in address space. Actual size of QMEM is however
// determined with instantiated RAM/ROM. However bigger
// mask will reserve more address space for QMEM, but also
// make design faster, while more tight mask will take
// less address space but also make design slower. If
// instantiated RAM/ROM is smaller than space reserved with
// the mask, instatiated RAM/ROM will also be shadowed
// at higher addresses in reserved space.
//

//
// QMEM interface byte-select capability
//
// To enable qmem_sel* ports, define this macro.
//
//`define OR1200_QMEM_BSEL

//
// QMEM interface acknowledge
//
// To enable qmem_ack port, define this macro.
//
//`define OR1200_QMEM_ACK

/////////////////////////////////////////////////////
//
// VR, UPR and Configuration Registers
//
//
// VR, UPR and configuration registers are optional. If 
// implemented, operating system can automatically figure
// out how to use the processor because it knows 
// what units are available in the processor and how they
// are configured.
//
// This section must be last in or1200_defines.v file so
// that all units are already configured and thus
// configuration registers are properly set.
// 

// Define if you want configuration registers implemented

// Define if you want full address decode inside SYS group

// Offsets of VR, UPR and CFGR registers

// VR fields

// VR values

// UPR fields

// UPR values

// CPUCFGR fields

// CPUCFGR values
     

// DMMUCFGR fields

// DMMUCFGR values

// IMMUCFGR fields

// IMMUCFGR values

// DCCFGR fields

// DCCFGR values

// ICCFGR fields

// ICCFGR values

// DCFGR fields

// DCFGR values

///////////////////////////////////////////////////////////////////////////////
// Boot Address Selection                                                    //
//                                                                           //
// Allows a definable boot address, potentially different to the usual reset //
// vector to allow for power-on code to be run, if desired.                  //
//                                                                           //
// OR1200_BOOT_ADR should be the 32-bit address of the boot location         //
//                                                                           //
// For default reset behavior uncomment the settings under the "Boot 0x100"  //
// comment below.                                                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
// Boot from 0xf0000100
//`define OR1200_BOOT_ADR 32'hf0000100
// Boot from 0x100
 
module or1200_sprs(
		   // Clk & Rst
		   clk, rst,

		   // Internal CPU interface
		   flagforw, flag_we, flag, cyforw, cy_we, carry,
		   ovforw, ov_we, dsx,
		   addrbase, addrofs, dat_i, branch_op, ex_spr_read, 
		   ex_spr_write, 
		   epcr, eear, esr, except_started,
		   to_wbmux, epcr_we, eear_we, esr_we, pc_we, sr_we, to_sr, sr,
		   spr_dat_cfgr, spr_dat_rf, spr_dat_npc, spr_dat_ppc, 
		   spr_dat_mac,
		   
		   boot_adr_sel_i,

		   // Floating point SPR input
		   fpcsr, fpcsr_we, spr_dat_fpu,

		   // From/to other RISC units
		   spr_dat_pic, spr_dat_tt, spr_dat_pm,
		   spr_dat_dmmu, spr_dat_immu, spr_dat_du,
		   spr_addr, spr_dat_o, spr_cs, spr_we,

		   du_addr, du_dat_du, du_read,
		   du_write, du_dat_cpu

		   );

   parameter width = 32;

   //
   // I/O Ports
   //

   //
   // Internal CPU interface
   //
   input				clk; 		// Clock
   input 				rst;		// Reset
   input 				flagforw;	// From ALU
   input 				flag_we;	// From ALU
   output 				flag;		// SR[F]
   input 				cyforw;		// From ALU
   input 				cy_we;		// From ALU
   output 				carry;		// SR[CY]
   input 				ovforw;		// From ALU
   input 				ov_we;		// From ALU
   input                                dsx;            // From except
   input [width-1:0] 			addrbase;	// SPR base address
   input [15:0] 			addrofs;	// SPR offset
   input [width-1:0] 			dat_i;		// SPR write data
   input 				ex_spr_read;	// l.mfspr in EX
   input 				ex_spr_write;	// l.mtspr in EX
   input [3-1:0] 	branch_op;	// Branch operation
   input [width-1:0] 			epcr /* verilator public */;// EPCR0
   input [width-1:0] 			eear /* verilator public */;// EEAR0
   input [17-1:0] 	esr /* verilator public */; // ESR0
   input 				except_started; // Exception was started
   output [width-1:0] 			to_wbmux;	// For l.mfspr
   output				epcr_we;	// EPCR0 write enable
   output				eear_we;	// EEAR0 write enable
   output				esr_we;		// ESR0 write enable
   output				pc_we;		// PC write enable
   output 				sr_we;		// Write enable SR
   output [17-1:0] 	to_sr;		// Data to SR
   output [17-1:0] 	sr /* verilator public */;// SR
   input [31:0] 			spr_dat_cfgr;	// Data from CFGR
   input [31:0] 			spr_dat_rf;	// Data from RF
   input [31:0] 			spr_dat_npc;	// Data from NPC
   input [31:0] 			spr_dat_ppc;	// Data from PPC   
   input [31:0] 			spr_dat_mac;	// Data from MAC
   input				boot_adr_sel_i;

   input [12-1:0] 	fpcsr;	// FPCSR
   output 				fpcsr_we;	// Write enable FPCSR   
   input [31:0] 			spr_dat_fpu;    // Data from FPU
   
   //
   // To/from other RISC units
   //
   input [31:0] 			spr_dat_pic;	// Data from PIC
   input [31:0] 			spr_dat_tt;	// Data from TT
   input [31:0] 			spr_dat_pm;	// Data from PM
   input [31:0] 			spr_dat_dmmu;	// Data from DMMU
   input [31:0] 			spr_dat_immu;	// Data from IMMU
   input [31:0] 			spr_dat_du;	// Data from DU
   output [31:0] 			spr_addr;	// SPR Address
   output [31:0] 			spr_dat_o;	// Data to unit
   output [31:0] 			spr_cs;		// Unit select
   output				spr_we;		// SPR write enable

   //
   // To/from Debug Unit
   //
   input [width-1:0] 			du_addr;	// Address
   input [width-1:0] 			du_dat_du;	// Data from DU to SPRS
   input				du_read;	// Read qualifier
   input				du_write;	// Write qualifier
   output [width-1:0] 			du_dat_cpu;	// Data from SPRS to DU

   //
   // Internal regs & wires
   //
   reg [17-1:0] 		sr_reg;		// SR
   reg 					sr_reg_bit_eph;	// SR_EPH bit
   reg 					sr_reg_bit_eph_select;// SR_EPH select
   wire 				sr_reg_bit_eph_muxed;// SR_EPH muxed bit
   reg [17-1:0] 		sr;			// SR
   reg [width-1:0] 			to_wbmux;	// For l.mfspr
   wire 				cfgr_sel;	// Select for cfg regs
   wire 				rf_sel;		// Select for RF
   wire 				npc_sel;	// Select for NPC
   wire 				ppc_sel;	// Select for PPC
   wire 				sr_sel;		// Select for SR	
   wire 				epcr_sel;	// Select for EPCR0
   wire 				eear_sel;	// Select for EEAR0
   wire 				esr_sel;	// Select for ESR0
   wire 				fpcsr_sel;	// Select for FPCSR   
   wire [31:0] 				sys_data;// Read data from system SPRs
   wire 				du_access;// Debug unit access
   reg [31:0] 				unqualified_cs;	// Unqualified selects
   wire 				ex_spr_write; // jb
   
   //
   // Decide if it is debug unit access
   //
   assign du_access = du_read | du_write;

   //
   // Generate SPR address from base address and offset
   // OR from debug unit address
   //
   assign spr_addr = du_access ? du_addr : (addrbase | {16'h0000, addrofs});

   //
   // SPR is written by debug unit or by l.mtspr
   //
   assign spr_dat_o = du_write ? du_dat_du : dat_i;

   //
   // debug unit data input:
   //  - read of SPRS by debug unit
   //  - write into debug unit SPRs by debug unit itself
   //  - write into debug unit SPRs by l.mtspr
   //
   assign du_dat_cpu = du_read ? to_wbmux : du_write ? du_dat_du : dat_i;

   //
   // Write into SPRs when DU or l.mtspr
   //
   assign spr_we = du_write | ( ex_spr_write & !du_access );


   //
   // Qualify chip selects
   //
   assign spr_cs = unqualified_cs & {32{du_read | du_write | ex_spr_read | 
					(ex_spr_write & sr[0])}};

   //
   // Decoding of groups
   //
   always @(spr_addr)
     case (spr_addr[15:11])	// synopsys parallel_case
       5'd00: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000001;
       5'd01: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000010;
       5'd02: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000100;
       5'd03: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00001000;
       5'd04: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00010000;
       5'd05: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00100000;
       5'd06: unqualified_cs 
	 = 32'b00000000_00000000_00000000_01000000;
       5'd07: unqualified_cs 
	 = 32'b00000000_00000000_00000000_10000000;
       5'd08: unqualified_cs 
	 = 32'b00000000_00000000_00000001_00000000;
       5'd09: unqualified_cs 
	 = 32'b00000000_00000000_00000010_00000000;
       5'd10: unqualified_cs 
	 = 32'b00000000_00000000_00000100_00000000;
       5'd11: unqualified_cs 
	 = 32'b00000000_00000000_00001000_00000000;
       5'd12: unqualified_cs 
	 = 32'b00000000_00000000_00010000_00000000;
       5'd13: unqualified_cs 
	 = 32'b00000000_00000000_00100000_00000000;
       5'd14: unqualified_cs 
	 = 32'b00000000_00000000_01000000_00000000;
       5'd15: unqualified_cs 
	 = 32'b00000000_00000000_10000000_00000000;
       5'd16: unqualified_cs 
	 = 32'b00000000_00000001_00000000_00000000;
       5'd17: unqualified_cs 
	 = 32'b00000000_00000010_00000000_00000000;
       5'd18: unqualified_cs 
	 = 32'b00000000_00000100_00000000_00000000;
       5'd19: unqualified_cs 
	 = 32'b00000000_00001000_00000000_00000000;
       5'd20: unqualified_cs 
	 = 32'b00000000_00010000_00000000_00000000;
       5'd21: unqualified_cs 
	 = 32'b00000000_00100000_00000000_00000000;
       5'd22: unqualified_cs 
	 = 32'b00000000_01000000_00000000_00000000;
       5'd23: unqualified_cs 
	 = 32'b00000000_10000000_00000000_00000000;
       5'd24: unqualified_cs 
	 = 32'b00000001_00000000_00000000_00000000;
       5'd25: unqualified_cs 
	 = 32'b00000010_00000000_00000000_00000000;
       5'd26: unqualified_cs 
	 = 32'b00000100_00000000_00000000_00000000;
       5'd27: unqualified_cs 
	 = 32'b00001000_00000000_00000000_00000000;
       5'd28: unqualified_cs 
	 = 32'b00010000_00000000_00000000_00000000;
       5'd29: unqualified_cs 
	 = 32'b00100000_00000000_00000000_00000000;
       5'd30: unqualified_cs 
	 = 32'b01000000_00000000_00000000_00000000;
       5'd31: unqualified_cs 
	 = 32'b10000000_00000000_00000000_00000000;
     endcase

   //
   // SPRs System Group
   //

   //
   // What to write into SR
   //
   assign to_sr[15:12	] 
	    = (except_started) ? {sr[15:14],dsx,1'b0} :
	      (branch_op == 3'd6) ? 
	      esr[15:12	] : (spr_we && sr_sel) ? 
	      {1'b1, spr_dat_o[15-1:12	]} :
	      sr[15:12	];
   assign to_sr[16] 
	    = (except_started) ? 1'b1 :
	      (branch_op == 3'd6) ? esr[16] :
	      (spr_we && sr_sel) ? spr_dat_o[16] :
	      sr[16];
   assign to_sr[11	] 
	    = (except_started) ? sr[11	] :
	      (branch_op == 3'd6) ? esr[11	] :
	      ov_we ? ovforw :
	      (spr_we && sr_sel) ? spr_dat_o[11	] :
	      sr[11	];
   assign to_sr[10	] 
	    = (except_started) ? sr[10	] :
	      (branch_op == 3'd6) ? esr[10	] :
	      cy_we ? cyforw :
	      (spr_we && sr_sel) ? spr_dat_o[10	] :
	      sr[10	];
   assign to_sr[9] 
	    = (except_started) ? sr[9] :
	      (branch_op == 3'd6) ? esr[9] :
	      flag_we ? flagforw :
	      (spr_we && sr_sel) ? spr_dat_o[9] :
	      sr[9];
   
   assign to_sr[8:0] 
	    = (except_started) ? {sr[8:7], 2'b00, 
				  sr[4:3], 3'b001} :
	      (branch_op == 3'd6) ? 
	      esr[8:0] : (spr_we && sr_sel) ? 
	      spr_dat_o[8:0] :
	      sr[8:0];

   //
   // Selects for system SPRs
   //
   assign cfgr_sel = (spr_cs[5'd00] && 
		      (spr_addr[10:4] == 7'd0));
   assign rf_sel = (spr_cs[5'd00] && 
		    (spr_addr[10:5] == 6'd32	));
   assign npc_sel = (spr_cs[5'd00] && 
		     (spr_addr[10:0] == 11'd16));
   assign ppc_sel = (spr_cs[5'd00] && 
		     (spr_addr[10:0] == 11'd18));
   assign sr_sel = (spr_cs[5'd00] && 
		    (spr_addr[10:0] == 11'd17));
   assign epcr_sel = (spr_cs[5'd00] && 
		      (spr_addr[10:0] == 11'd32));
   assign eear_sel = (spr_cs[5'd00] && 
		      (spr_addr[10:0] == 11'd48));
   assign esr_sel = (spr_cs[5'd00] && 
		     (spr_addr[10:0] == 11'd64));
   assign fpcsr_sel = (spr_cs[5'd00] && 
		       (spr_addr[10:0] == 11'd20));


   //
   // Write enables for system SPRs
   //
   assign sr_we = (spr_we && sr_sel) | (branch_op == 3'd6) | 
		  flag_we | cy_we | ov_we;
   assign pc_we = (du_write && (npc_sel | ppc_sel));
   assign epcr_we = (spr_we && epcr_sel);
   assign eear_we = (spr_we && eear_sel);
   assign esr_we = (spr_we && esr_sel);
   assign fpcsr_we = (spr_we && fpcsr_sel);
   
   //
   // Output from system SPRs
   //
   assign sys_data = (spr_dat_cfgr & {32{cfgr_sel}}) |
		     (spr_dat_rf & {32{rf_sel}}) |
		     (spr_dat_npc & {32{npc_sel}}) |
		     (spr_dat_ppc & {32{ppc_sel}}) |
		     ({{32-17{1'b0}},sr} & {32{sr_sel}}) |
		     (epcr & {32{epcr_sel}}) |
		     (eear & {32{eear_sel}}) |
		     ({{32-12{1'b0}},fpcsr} & 
		      {32{fpcsr_sel}}) |
		     ({{32-17{1'b0}},esr} & {32{esr_sel}});

   //
   // Flag alias
   //
   assign flag = sr[9];

   //
   // Carry alias
   //
   assign carry = sr[10	];
   
   //
   // Supervision register
   //
   always @(posedge clk or posedge rst)
     if (rst == (1'b1))
       sr_reg <=  {2'b01, // Fixed one.
		   1'b0, {17-4{1'b0}}, 1'b1};
     else if (except_started)
       sr_reg <=  to_sr[17-1:0];
     else if (sr_we)
       sr_reg <=  to_sr[17-1:0];

   // EPH part of Supervision register
   always @(posedge clk or posedge rst)
     // default value 
     if (rst == (1'b1)) begin
	sr_reg_bit_eph <=  1'b0;
	// select async. value due to reset state
	sr_reg_bit_eph_select <=  1'b1;	
     end
   // selected value (different from default) is written into FF after reset 
   // state
     else if (sr_reg_bit_eph_select) begin
	// dynamic value can only be assigned to FF out of reset!
	sr_reg_bit_eph <=  boot_adr_sel_i;
	sr_reg_bit_eph_select <=  1'b0;	// select FF value
     end
     else if (sr_we) begin
	sr_reg_bit_eph <=  to_sr[14];
     end

   // select async. value of EPH bit after reset 
   assign	sr_reg_bit_eph_muxed = (sr_reg_bit_eph_select) ? 
				       boot_adr_sel_i : sr_reg_bit_eph;

   // EPH part joined together with rest of Supervision register
   always @(sr_reg or sr_reg_bit_eph_muxed)
     sr = {sr_reg[17-1:17-2], sr_reg_bit_eph_muxed,
	   sr_reg[17-4:0]};

   
   //
   // MTSPR/MFSPR interface
   //
   always @(spr_addr or sys_data or spr_dat_mac or spr_dat_pic or spr_dat_pm or
	    spr_dat_fpu or
	    spr_dat_dmmu or spr_dat_immu or spr_dat_du or spr_dat_tt) begin
      casez (spr_addr[15:11]) // synopsys parallel_case
	5'd00:
	  to_wbmux = sys_data;
	5'd10:
	  to_wbmux = spr_dat_tt;
	5'd09:
	  to_wbmux = spr_dat_pic;
	5'd08:
	  to_wbmux = spr_dat_pm;
	5'd01:
	  to_wbmux = spr_dat_dmmu;
	5'd02:
	  to_wbmux = spr_dat_immu;
	5'd05:
	  to_wbmux = spr_dat_mac;
	5'd11:
	  to_wbmux = spr_dat_fpu;
	default: //`OR1200_SPR_GROUP_DU:
	  to_wbmux = spr_dat_du;
      endcase
   end

endmodule
