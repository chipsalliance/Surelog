//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's WISHBONE BIU                                       ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Implements WISHBONE interface                               ////
////                                                              ////
////  To Do:                                                      ////
////   - if biu_cyc/stb are deasserted and wb_ack_i is asserted   ////
////   and this happens even before aborted_r is asssrted,        ////
////   wb_ack_i will be delivered even though transfer is         ////
////   internally considered already aborted. However most        ////
////   wb_ack_i are externally registered and delayed. Normally   ////
////   this shouldn't cause any problems.                         ////
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
// $Log: or1200_wb_biu.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Major update: 
// Structure reordered and bugs fixed. 
//

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
 
module or1200_wb_biu(
		     // RISC clock, reset and clock control
		     clk, rst, clmode,

		     // WISHBONE interface
		     wb_clk_i, wb_rst_i, wb_ack_i, wb_err_i, wb_rty_i, wb_dat_i,
		     wb_cyc_o, wb_adr_o, wb_stb_o, wb_we_o, wb_sel_o, wb_dat_o,
		     wb_cti_o, wb_bte_o,

		     // Internal RISC bus
		     biu_dat_i, biu_adr_i, biu_cyc_i, biu_stb_i, biu_we_i, biu_sel_i, biu_cab_i,
		     biu_dat_o, biu_ack_o, biu_err_o
		     );

   parameter dw = 32;
   parameter aw = 32;
   parameter bl = 4; /* Can currently be either 4 or 8 - the two optional line
		      sizes for the OR1200. */
		      
   
   //
   // RISC clock, reset and clock control
   //
   input				clk;		// RISC clock
   input				rst;		// RISC reset
   input [1:0] 				clmode;		// 00 WB=RISC, 01 WB=RISC/2, 10 N/A, 11 WB=RISC/4

   //
   // WISHBONE interface
   //
   input				wb_clk_i;	// clock input
   input				wb_rst_i;	// reset input
   input				wb_ack_i;	// normal termination
   input				wb_err_i;	// termination w/ error
   input				wb_rty_i;	// termination w/ retry
   input [dw-1:0] 			wb_dat_i;	// input data bus
   output				wb_cyc_o;	// cycle valid output
   output [aw-1:0] 			wb_adr_o;	// address bus outputs
   output				wb_stb_o;	// strobe output
   output				wb_we_o;	// indicates write transfer
   output [3:0] 			wb_sel_o;	// byte select outputs
   output [dw-1:0] 			wb_dat_o;	// output data bus
   output [2:0] 			wb_cti_o;	// cycle type identifier
   output [1:0] 			wb_bte_o;	// burst type extension

   //
   // Internal RISC interface
   //
   input [dw-1:0] 			biu_dat_i;	// input data bus
   input [aw-1:0] 			biu_adr_i;	// address bus
   input				biu_cyc_i;	// WB cycle
   input				biu_stb_i;	// WB strobe
   input				biu_we_i;	// WB write enable
   input				biu_cab_i;	// CAB input
   input [3:0] 				biu_sel_i;	// byte selects
   output [31:0] 			biu_dat_o;	// output data bus
   output				biu_ack_o;	// ack output
   output				biu_err_o;	// err output

   //
   // Registers
   //
   wire 				wb_ack;		// normal termination
   reg [aw-1:0] 			wb_adr_o;	// address bus outputs
   reg 					wb_cyc_o;	// cycle output
   reg 					wb_stb_o;	// strobe output
   reg 					wb_we_o;	// indicates write transfer
   reg [3:0] 				wb_sel_o;	// byte select outputs
   reg [2:0] 				wb_cti_o;	// cycle type identifier
   reg [1:0] 				wb_bte_o;	// burst type extension
   reg [dw-1:0] 			wb_dat_o;	// output data bus
   
   wire 				retry_cnt;
   assign retry_cnt = 1'b0;
   reg [3:0] 				burst_len;	// burst counter

   reg  				biu_stb_reg;	// WB strobe
   wire  				biu_stb;	// WB strobe
   reg 					wb_cyc_nxt;	// next WB cycle value
   reg 					wb_stb_nxt;	// next WB strobe value
   reg [2:0] 				wb_cti_nxt;	// next cycle type identifier value

   reg 					wb_ack_cnt;	// WB ack toggle counter
   reg 					wb_err_cnt;	// WB err toggle counter
   reg 					wb_rty_cnt;	// WB rty toggle counter
   reg 					biu_ack_cnt;	// BIU ack toggle counter
   reg 					biu_err_cnt;	// BIU err toggle counter
   reg 					biu_rty_cnt;	// BIU rty toggle counter
   wire 				biu_rty;	// BIU rty indicator

   reg [1:0] 				wb_fsm_state_cur;	// WB FSM - surrent state
   reg [1:0] 				wb_fsm_state_nxt;	// WB FSM - next state
   wire [1:0] 				wb_fsm_idle	= 2'h0;	// WB FSM state - IDLE
   wire [1:0] 				wb_fsm_trans	= 2'h1;	// WB FSM state - normal TRANSFER
   wire [1:0] 				wb_fsm_last	= 2'h2;	// EB FSM state - LAST transfer

   //
   // WISHBONE I/F <-> Internal RISC I/F conversion
   //
   //assign wb_ack = wb_ack_i;
   assign wb_ack = wb_ack_i & !wb_err_i & !wb_rty_i;

   //
   // WB FSM - register part
   // 
   always @(posedge wb_clk_i or posedge wb_rst_i) begin
      if (wb_rst_i == (1'b1)) 
	wb_fsm_state_cur <=  wb_fsm_idle;
      else 
	wb_fsm_state_cur <=  wb_fsm_state_nxt;
   end

   //
   // WB burst tength counter
   // 
   always @(posedge wb_clk_i or posedge wb_rst_i) begin
      if (wb_rst_i == (1'b1)) begin
	 burst_len <= 0;
      end
      else begin
	 // burst counter
	 if (wb_fsm_state_cur == wb_fsm_idle)
	   burst_len <=  bl[3:0] - 2;
	 else if (wb_stb_o & wb_ack)
	   burst_len <=  burst_len - 1;
      end
   end

   // 
   // WB FSM - combinatorial part
   // 
   always @(wb_fsm_state_cur or burst_len or wb_err_i or wb_rty_i or wb_ack or 
	    wb_cti_o or wb_sel_o or wb_stb_o or wb_we_o or biu_cyc_i or 
	    biu_stb or biu_cab_i or biu_sel_i or biu_we_i) begin
      // States of WISHBONE Finite State Machine
      case(wb_fsm_state_cur)
	// IDLE 
	wb_fsm_idle : begin
	   wb_cyc_nxt = biu_cyc_i & biu_stb;
	   wb_stb_nxt = biu_cyc_i & biu_stb;
	   wb_cti_nxt = {!biu_cab_i, 1'b1, !biu_cab_i};
	   if (biu_cyc_i & biu_stb)
	     wb_fsm_state_nxt = wb_fsm_trans;
	   else
	     wb_fsm_state_nxt = wb_fsm_idle;
	end
	// normal TRANSFER
	wb_fsm_trans : begin
	   wb_cyc_nxt = !wb_stb_o | !wb_err_i & !wb_rty_i & 
			!(wb_ack & wb_cti_o == 3'b111);
	   
	   wb_stb_nxt = !wb_stb_o | !wb_err_i & !wb_rty_i & !wb_ack | 
			!wb_err_i & !wb_rty_i & wb_cti_o == 3'b010 ;
	   wb_cti_nxt[2] = wb_stb_o & wb_ack & burst_len == 'h0 | wb_cti_o[2];
	   wb_cti_nxt[1] = 1'b1 ;
	   wb_cti_nxt[0] = wb_stb_o & wb_ack & burst_len == 'h0 | wb_cti_o[0];

	   if ((!biu_cyc_i | !biu_stb | !biu_cab_i | biu_sel_i != wb_sel_o | 
		biu_we_i != wb_we_o) & wb_cti_o == 3'b010)
	     wb_fsm_state_nxt = wb_fsm_last;
	   else if ((wb_err_i | wb_rty_i | wb_ack & wb_cti_o==3'b111) & 
		    wb_stb_o)
	     wb_fsm_state_nxt = wb_fsm_idle;
	   else
	     wb_fsm_state_nxt = wb_fsm_trans;
	end
	// LAST transfer
	wb_fsm_last : begin
	   wb_cyc_nxt = !wb_stb_o | !wb_err_i & !wb_rty_i & 
			!(wb_ack & wb_cti_o == 3'b111);
	   wb_stb_nxt = !wb_stb_o | !wb_err_i & !wb_rty_i & 
			!(wb_ack & wb_cti_o == 3'b111);
	   wb_cti_nxt[2] = wb_ack & wb_stb_o | wb_cti_o[2];
	   wb_cti_nxt[1] = 1'b1 ;
	   wb_cti_nxt[0] = wb_ack & wb_stb_o | wb_cti_o[0];
	   if ((wb_err_i | wb_rty_i | wb_ack & wb_cti_o == 3'b111) & wb_stb_o)
	     wb_fsm_state_nxt = wb_fsm_idle;
	   else
	     wb_fsm_state_nxt = wb_fsm_last;
	end
	// default state
	default:begin
	   wb_cyc_nxt = 1'bx;
	   wb_stb_nxt = 1'bx;
	   wb_cti_nxt = 3'bxxx;
	   wb_fsm_state_nxt = 2'bxx;
	end
      endcase
   end

   //
   // WB FSM - output signals
   // 
   always @(posedge wb_clk_i or posedge wb_rst_i) begin
      if (wb_rst_i == (1'b1)) begin
	 wb_cyc_o	<=  1'b0;
	 wb_stb_o	<=  1'b0;
	 wb_cti_o	<=  3'b111;
	 wb_bte_o	<=  (bl==8) ? 2'b10 : (bl==4) ? 2'b01 : 2'b00;
	 wb_we_o		<=  1'b0;
	 wb_sel_o	<=  4'hf;
	 wb_adr_o	<=  {aw{1'b0}};
	 wb_dat_o	<=  {dw{1'b0}};
      end
      else begin
	 wb_cyc_o	<=  wb_cyc_nxt;

         if (wb_ack & wb_cti_o == 3'b111) 
           wb_stb_o        <=  1'b0;
         else
           wb_stb_o        <=  wb_stb_nxt;
	 wb_cti_o	<=  wb_cti_nxt;
	 wb_bte_o	<=  (bl==8) ? 2'b10 : (bl==4) ? 2'b01 : 2'b00;
	 // we and sel - set at beginning of access 
	 if (wb_fsm_state_cur == wb_fsm_idle) begin
	    wb_we_o		<=  biu_we_i;
	    wb_sel_o	<=  biu_sel_i;
	 end
	 // adr - set at beginning of access and changed at every termination 
	 if (wb_fsm_state_cur == wb_fsm_idle) begin
	    wb_adr_o	<=  biu_adr_i;
	 end 
	 else if (wb_stb_o & wb_ack) begin
	    if (bl==4) begin
	       wb_adr_o[3:2]	<=  wb_adr_o[3:2] + 1;
	    end
	    if (bl==8) begin
	       wb_adr_o[4:2]	<=  wb_adr_o[4:2] + 1;
	    end
	 end
	 // dat - write data changed after avery subsequent write access
	 if (!wb_stb_o) begin
	    wb_dat_o 	<=  biu_dat_i;
	 end
      end
   end

   //
   // WB & BIU termination toggle counters
   // 
   always @(posedge wb_clk_i or posedge wb_rst_i) begin
      if (wb_rst_i == (1'b1)) begin
	 wb_ack_cnt	<=  1'b0;
	 wb_err_cnt	<=  1'b0;
	 wb_rty_cnt	<=  1'b0;
      end
      else begin
	 // WB ack toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   wb_ack_cnt	<=  1'b0;
	 else if (wb_stb_o & wb_ack)
	   wb_ack_cnt	<=  !wb_ack_cnt;
	 // WB err toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   wb_err_cnt	<=  1'b0;
	 else if (wb_stb_o & wb_err_i)
	   wb_err_cnt	<=  !wb_err_cnt;
	 // WB rty toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   wb_rty_cnt	<=  1'b0;
	 else if (wb_stb_o & wb_rty_i)
	   wb_rty_cnt	<=  !wb_rty_cnt;
      end
   end

   always @(posedge clk or posedge rst) begin
      if (rst == (1'b1)) begin
         biu_stb_reg	<=  1'b0;
	 biu_ack_cnt	<=  1'b0;
	 biu_err_cnt	<=  1'b0;
	 biu_rty_cnt	<=  1'b0;
      end
      else begin
	 // BIU strobe
	 if (biu_stb_i & !biu_cab_i & biu_ack_o)
	   biu_stb_reg	<=  1'b0;
	 else
	   biu_stb_reg	<=  biu_stb_i;
	 // BIU ack toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   biu_ack_cnt	<=  1'b0 ;
	 else if (biu_ack_o)
	   biu_ack_cnt	<=  !biu_ack_cnt ;
	 // BIU err toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   biu_err_cnt	<=  1'b0 ;
	 else if (wb_err_i & biu_err_o)
	   biu_err_cnt	<=  !biu_err_cnt ;
	 // BIU rty toggle counter
	 if (wb_fsm_state_cur == wb_fsm_idle | !(|clmode))
	   biu_rty_cnt	<=  1'b0 ;
	 else if (biu_rty)
	   biu_rty_cnt	<=  !biu_rty_cnt ;
      end
   end

   assign biu_stb = biu_stb_i & biu_stb_reg;

   //
   // Input BIU data bus
   //
   assign	biu_dat_o	= wb_dat_i;

   //
   // Input BIU termination signals 
   //
   assign	biu_rty		= (wb_fsm_state_cur == wb_fsm_trans) & wb_rty_i & wb_stb_o & (wb_rty_cnt ~^ biu_rty_cnt);
   assign	biu_ack_o	= (wb_fsm_state_cur == wb_fsm_trans) & wb_ack & wb_stb_o & (wb_ack_cnt ~^ biu_ack_cnt);
   assign	biu_err_o	= (wb_fsm_state_cur == wb_fsm_trans) & wb_err_i & wb_stb_o & (wb_err_cnt ~^ biu_err_cnt)
   ;


endmodule
