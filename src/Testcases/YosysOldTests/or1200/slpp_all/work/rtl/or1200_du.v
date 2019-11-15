//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Debug Unit                                         ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Basic OR1200 debug unit.                                    ////
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
//
// $Log: or1200_du.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 

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
 
//
// Debug unit
//

module or1200_du(
	// RISC Internal Interface
	clk, rst,
	dcpu_cycstb_i, dcpu_we_i, dcpu_adr_i, dcpu_dat_lsu,
	dcpu_dat_dc, icpu_cycstb_i,
	ex_freeze, branch_op, ex_insn, id_pc,
	spr_dat_npc, rf_dataw,
	du_dsr, du_dmr1, du_stall, du_addr, du_dat_i, du_dat_o,
	du_read, du_write, du_except_stop, du_hwbkpt,
	spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o,

	// External Debug Interface
	dbg_stall_i, dbg_ewt_i,	dbg_lss_o, dbg_is_o, dbg_wp_o, dbg_bp_o,
	dbg_stb_i, dbg_we_i, dbg_adr_i, dbg_dat_i, dbg_dat_o, dbg_ack_o
);

parameter dw = 32;
parameter aw = 32;

//
// I/O
//

//
// RISC Internal Interface
//
input				clk;		// Clock
input				rst;		// Reset
input				dcpu_cycstb_i;	// LSU status
input				dcpu_we_i;	// LSU status
input	[31:0]			dcpu_adr_i;	// LSU addr
input	[31:0]			dcpu_dat_lsu;	// LSU store data
input	[31:0]			dcpu_dat_dc;	// LSU load data
input	[1-1:0]	icpu_cycstb_i;	// IFETCH unit status
input				ex_freeze;	// EX stage freeze
input	[3-1:0]	branch_op;	// Branch op
input	[dw-1:0]		ex_insn;	// EX insn
input	[31:0]			id_pc;		// insn fetch EA
input	[31:0]			spr_dat_npc;	// Next PC (for trace)
input	[31:0]			rf_dataw;	// ALU result (for trace)
output	[14-1:0]     du_dsr;		// DSR
output	[24: 0]			du_dmr1;
output				du_stall;	// Debug Unit Stall
output	[aw-1:0]		du_addr;	// Debug Unit Address
input	[dw-1:0]		du_dat_i;	// Debug Unit Data In
output	[dw-1:0]		du_dat_o;	// Debug Unit Data Out
output				du_read;	// Debug Unit Read Enable
output				du_write;	// Debug Unit Write Enable
input	[13:0]			du_except_stop;	// Exception masked by DSR
output				du_hwbkpt;	// Cause trap exception (HW Breakpoints)
input				spr_cs;		// SPR Chip Select
input				spr_write;	// SPR Read/Write
input	[aw-1:0]		spr_addr;	// SPR Address
input	[dw-1:0]		spr_dat_i;	// SPR Data Input
output	[dw-1:0]		spr_dat_o;	// SPR Data Output

//
// External Debug Interface
//
input			dbg_stall_i;	// External Stall Input
input			dbg_ewt_i;	// External Watchpoint Trigger Input
output	[3:0]		dbg_lss_o;	// External Load/Store Unit Status
output	[1:0]		dbg_is_o;	// External Insn Fetch Status
output	[10:0]		dbg_wp_o;	// Watchpoints Outputs
output			dbg_bp_o;	// Breakpoint Output
input			dbg_stb_i;      // External Address/Data Strobe
input			dbg_we_i;       // External Write Enable
input	[aw-1:0]	dbg_adr_i;	// External Address Input
input	[dw-1:0]	dbg_dat_i;	// External Data Input
output	[dw-1:0]	dbg_dat_o;	// External Data Output
output			dbg_ack_o;	// External Data Acknowledge (not WB compatible)
reg	[dw-1:0]	dbg_dat_o;	// External Data Output
reg			dbg_ack_o;	// External Data Acknowledge (not WB compatible)


//
// Some connections go directly from the CPU through DU to Debug I/F
//
assign dbg_lss_o = 4'b0000;

reg	[1:0]			dbg_is_o;
//
// Show insn activity (temp, must be removed)
//
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		dbg_is_o <=  2'b00;
	else if (!ex_freeze & ~((ex_insn[31:26] == 6'b000101) & ex_insn[16]))
		dbg_is_o <=  ~dbg_is_o;
assign dbg_wp_o = 11'b000_0000_0000;

//
// Some connections go directly from Debug I/F through DU to the CPU
//
assign du_stall = dbg_stall_i;
assign du_addr = dbg_adr_i;
assign du_dat_o = dbg_dat_i;
assign du_read = dbg_stb_i && !dbg_we_i;
assign du_write = dbg_stb_i && dbg_we_i;

reg				dbg_ack;
//
// Generate acknowledge -- just delay stb signal
//
always @(posedge clk or posedge rst) begin
	if (rst == (1'b1)) begin
		dbg_ack   <=  1'b0;
		dbg_ack_o <=  1'b0;
	end
	else begin
		dbg_ack   <=  dbg_stb_i;		// valid when du_dat_i 
		dbg_ack_o <=  dbg_ack & dbg_stb_i;	// valid when dbg_dat_o 
	end
end

// 
// Register data output
//
always @(posedge clk)
    dbg_dat_o <=  du_dat_i;


//
// Debug Mode Register 1
//
reg	[24:0]			dmr1;		// DMR1 implemented
assign du_dmr1 = dmr1;

//
// Debug Mode Register 2
//
wire	[23:0]			dmr2;		// DMR2 not implemented

//
// Debug Stop Register
//
reg	[14-1:0]	dsr;		// DSR implemented

//
// Debug Reason Register
//
reg	[13:0]			drr;		// DRR implemented

//
// Debug Value Register N
//
wire	[31:0]			dvr0;

//
// Debug Value Register N
//
wire	[31:0]			dvr1;

//
// Debug Value Register N
//
wire	[31:0]			dvr2;

//
// Debug Value Register N
//
wire	[31:0]			dvr3;

//
// Debug Value Register N
//
wire	[31:0]			dvr4;

//
// Debug Value Register N
//
wire	[31:0]			dvr5;

//
// Debug Value Register N
//
wire	[31:0]			dvr6;

//
// Debug Value Register N
//
wire	[31:0]			dvr7;

//
// Debug Control Register N
//
wire	[7:0]			dcr0;

//
// Debug Control Register N
//
wire	[7:0]			dcr1;

//
// Debug Control Register N
//
wire	[7:0]			dcr2;

//
// Debug Control Register N
//
wire	[7:0]			dcr3;

//
// Debug Control Register N
//
wire	[7:0]			dcr4;

//
// Debug Control Register N
//
wire	[7:0]			dcr5;

//
// Debug Control Register N
//
wire	[7:0]			dcr6;

//
// Debug Control Register N
//
wire	[7:0]			dcr7;

//
// Debug Watchpoint Counter Register 0
//
wire	[31:0]			dwcr0;

//
// Debug Watchpoint Counter Register 1
//
wire	[31:0]			dwcr1;

//
// Internal wires
//
wire				dmr1_sel; 	// DMR1 select
wire				dmr2_sel; 	// DMR2 select
wire				dsr_sel; 	// DSR select
wire				drr_sel; 	// DRR select
wire				dvr0_sel,
				dvr1_sel,
				dvr2_sel,
				dvr3_sel,
				dvr4_sel,
				dvr5_sel,
				dvr6_sel,
				dvr7_sel; 	// DVR selects
wire				dcr0_sel,
				dcr1_sel,
				dcr2_sel,
				dcr3_sel,
				dcr4_sel,
				dcr5_sel,
				dcr6_sel,
				dcr7_sel; 	// DCR selects
wire				dwcr0_sel,
				dwcr1_sel; 	// DWCR selects
reg				dbg_bp_r;
reg 				ex_freeze_q;
wire				du_hwbkpt;
reg				du_hwbkpt_hold;
reg	[31:0]			spr_dat_o;
reg	[13:0]			except_stop;	// Exceptions that stop because of DSR
wire	[31:0]			tbia_dat_o;
wire	[31:0]			tbim_dat_o;
wire	[31:0]			tbar_dat_o;
wire	[31:0]			tbts_dat_o;

//
// DU registers address decoder
//
assign dmr1_sel = (spr_cs && (spr_addr[10:0] == 11'd16));
assign dsr_sel = (spr_cs && (spr_addr[10:0] == 11'd20));
assign drr_sel = (spr_cs && (spr_addr[10:0] == 11'd21));

// Track previous ex_freeze to detect when signals are updated
always @(posedge clk)
  ex_freeze_q <= ex_freeze;

//
// Decode started exception
//
// du_except_stop comes from or1200_except
//   
always @(du_except_stop or ex_freeze_q) begin
	except_stop = 14'b00_0000_0000_0000;
	casez (du_except_stop)
	        14'b1?_????_????_????:
			except_stop[4] = 1'b1;
		14'b01_????_????_????: begin
			except_stop[7] = 1'b1;
		end
		14'b00_1???_????_????: begin
			except_stop[9] = 1'b1;
		end
		14'b00_01??_????_????:
			except_stop[3] = 1'b1;
		14'b00_001?_????_????: begin
			except_stop[1] = 1'b1;
		end
		14'b00_0001_????_????:
			except_stop[6] = 1'b1;
		14'b00_0000_1???_????: begin
			except_stop[5] = 1'b1;
		end
		14'b00_0000_01??_????: begin
			except_stop[8] = 1'b1;
		end
		14'b00_0000_001?_????:
			except_stop[2] = 1'b1;
		14'b00_0000_0001_????:
			except_stop[1] = 1'b1;
		14'b00_0000_0000_1???: begin
			except_stop[10] = 1'b1;
		end
		14'b00_0000_0000_01??: begin
			except_stop[13] = 1'b1 & ~ex_freeze_q;
		end
		14'b00_0000_0000_001?: begin
		        except_stop[12] = 1'b1;
		end	  
		14'b00_0000_0000_0001:
			except_stop[11] = 1'b1 & ~ex_freeze_q;
		default:
			except_stop = 14'b00_0000_0000_0000;
	endcase // casez (du_except_stop)
end

//
// dbg_bp_o is registered
//
assign dbg_bp_o = dbg_bp_r;

//
// Breakpoint activation register
//
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		dbg_bp_r <=  1'b0;
	else if (!ex_freeze)
		dbg_bp_r <=  |except_stop
                        | ~((ex_insn[31:26] == 6'b000101) & ex_insn[16]) & dmr1[22]
                        | (branch_op != 3'd0) & (branch_op != 3'd6) & dmr1[23]
			;
        else
                dbg_bp_r <=  |except_stop;

//
// Write to DMR1
//
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		dmr1 <= 25'h000_0000;
	else if (dmr1_sel && spr_write)
		dmr1 <=  {1'b0, spr_dat_i[23:22], 22'h00_0000};

//
// Write to DMR2
//
assign dmr2 = 24'h00_0000;

//
// Write to DSR
//
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		dsr <= {14{1'b0}};
	else if (dsr_sel && spr_write)
		dsr <=  spr_dat_i[14-1:0];

//
// Write to DRR
//
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		drr <= 14'b0;
	else if (drr_sel && spr_write)
		drr <=  spr_dat_i[13:0];
	else
		drr <=  drr | except_stop;

//
// Write to DVR0
//
assign dvr0 = 32'h0000_0000;

//
// Write to DVR1
//
assign dvr1 = 32'h0000_0000;

//
// Write to DVR2
//
assign dvr2 = 32'h0000_0000;

//
// Write to DVR3
//
assign dvr3 = 32'h0000_0000;

//
// Write to DVR4
//
assign dvr4 = 32'h0000_0000;

//
// Write to DVR5
//
assign dvr5 = 32'h0000_0000;

//
// Write to DVR6
//
assign dvr6 = 32'h0000_0000;

//
// Write to DVR7
//
assign dvr7 = 32'h0000_0000;

//
// Write to DCR0
//
assign dcr0 = 8'h00;

//
// Write to DCR1
//
assign dcr1 = 8'h00;

//
// Write to DCR2
//
assign dcr2 = 8'h00;

//
// Write to DCR3
//
assign dcr3 = 8'h00;

//
// Write to DCR4
//
assign dcr4 = 8'h00;

//
// Write to DCR5
//
assign dcr5 = 8'h00;

//
// Write to DCR6
//
assign dcr6 = 8'h00;

//
// Write to DCR7
//
assign dcr7 = 8'h00;

//
// Write to DWCR0
//
assign dwcr0 = 32'h0000_0000;

//
// Write to DWCR1
//
assign dwcr1 = 32'h0000_0000;

//
// Read DU registers
//
always @(spr_addr or dsr or drr or dmr1 or dmr2
	or dvr0 or dvr1 or dvr2 or dvr3 or dvr4
	or dvr5 or dvr6 or dvr7
	or dcr0 or dcr1 or dcr2 or dcr3 or dcr4
	or dcr5 or dcr6 or dcr7
	or dwcr0 or dwcr1
	)
	casez (spr_addr[10:0]) // synopsys parallel_case
		11'd16:
			spr_dat_o = {7'h00, dmr1};
		11'd20:
			spr_dat_o = {18'b0, dsr};
		11'd21:
			spr_dat_o = {18'b0, drr};
		default:
			spr_dat_o = 32'h0000_0000;
	endcase

//
// DSR alias
//
assign du_dsr = dsr;


//
// Watchpoints can cause trap exception
//
assign du_hwbkpt = 1'b0;

// Hold du_hwbkpt if ex_freeze is active in order to cause trap exception 
always @(posedge clk or posedge rst)
	if (rst == (1'b1))
		du_hwbkpt_hold <=  1'b0;
	else if (du_hwbkpt & ex_freeze)
		du_hwbkpt_hold <=  1'b1;
	else if (!ex_freeze)
		du_hwbkpt_hold <=  1'b0;


assign tbia_dat_o = 32'h0000_0000;
assign tbim_dat_o = 32'h0000_0000;
assign tbar_dat_o = 32'h0000_0000;
assign tbts_dat_o = 32'h0000_0000;



endmodule
