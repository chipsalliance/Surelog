//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
//
// *File Name: omsp_alu.v
// 
// *Module Description:
//                       openMSP430 ALU
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 134 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2012-03-22 21:31:06 +0100 (Thu, 22 Mar 2012) $
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
// 
// *File Name: openMSP430_defines.v
// 
// *Module Description:
//                      openMSP430 Configuration file
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 180 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2013-02-25 22:23:18 +0100 (Mon, 25 Feb 2013) $
//----------------------------------------------------------------------------
//`define OMSP_NO_INCLUDE
//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
// 
// *File Name: openMSP430_undefines.v
// 
// *Module Description:
//                      openMSP430 Verilog `undef file
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 23 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2009-08-30 18:39:26 +0200 (Sun, 30 Aug 2009) $
//----------------------------------------------------------------------------

//----------------------------------------------------------------------------
// BASIC SYSTEM CONFIGURATION
//----------------------------------------------------------------------------

// Program Memory sizes

// Data Memory sizes

// Include/Exclude Hardware Multiplier

// Include Debug interface


//----------------------------------------------------------------------------
// ADVANCED SYSTEM CONFIGURATION (FOR EXPERIENCED USERS)
//----------------------------------------------------------------------------

// Custom user version number

// Include/Exclude Watchdog timer

// Include/Exclude Non-Maskable-Interrupt support

// Input synchronizers

// Peripheral Memory Space:

// Let the CPU break after a PUC occurrence by default


//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Serial Debug interface protocol

// Enable the I2C broadcast address

// Number of hardware breakpoint units

// Enable/Disable the hardware breakpoint RANGE mode

// Custom Program/Data and Peripheral Memory Spaces







// ASIC version


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// ASIC/FPGA-like clocking

// Fine grained clock gating

// LFXT clock domain

// MCLK: Clock Mux

// SMCLK: Clock Mux

// WATCHDOG: Clock Mux

// MCLK: Clock divider

// SMCLK: Clock divider (/1/2/4/8)

// ACLK: Clock divider (/1/2/4/8)

// LOW POWER MODE: CPUOFF

// LOW POWER MODE: SCG0

// LOW POWER MODE: SCG1

// LOW POWER MODE: OSCOFF


//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//=====        SYSTEM CONSTANTS --- !!!!!!!! DO NOT EDIT !!!!!!!!      =====//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//

// Program Memory Size

// Data Memory Size

// Peripheral Memory Size

// Data Memory Base Adresses

// Program & Data Memory most significant address bit (for 16 bit words)

// Instructions type

// Single-operand arithmetic

// Conditional jump

// Two-operand arithmetic

// Addressing modes

// Instruction state machine

// Execution state machine

// ALU control signals

// Debug interface

// Debug interface CPU_CTL register

// Debug interface CPU_STAT register

// Debug interface BRKx_CTL register

// Basic clock module: BCSCTL1 Control Register

// Basic clock module: BCSCTL2 Control Register

// MCLK Clock gate

// SMCLK Clock gate

//
// DEBUG INTERFACE EXTRA CONFIGURATION
//======================================

// Debug interface: CPU version

// Debug interface: Software breakpoint opcode

// Debug UART interface auto data synchronization

// Debug UART interface data rate

// Debug interface input synchronizer

// Enable/Disable the hardware breakpoint RANGE mode

// Counter width for the debug interface UART

//
// MULTIPLIER CONFIGURATION
//======================================


//============================================================================
//============================================================================
// BASIC SYSTEM CONFIGURATION
//============================================================================
//============================================================================
//
// Note: the sum of program, data and peripheral memory spaces must not
//      exceed 64 kB
//

// Program Memory Size:
//                     Uncomment the required memory size
//-------------------------------------------------------
//`define PMEM_SIZE_CUSTOM
//`define PMEM_SIZE_59_KB
//`define PMEM_SIZE_55_KB
//`define PMEM_SIZE_54_KB
//`define PMEM_SIZE_51_KB
//`define PMEM_SIZE_48_KB
//`define PMEM_SIZE_41_KB
//`define PMEM_SIZE_32_KB
//`define PMEM_SIZE_24_KB
//`define PMEM_SIZE_16_KB
//`define PMEM_SIZE_12_KB
//`define PMEM_SIZE_8_KB
//`define PMEM_SIZE_4_KB
//`define PMEM_SIZE_1_KB


// Data Memory Size:
//                     Uncomment the required memory size
//-------------------------------------------------------
//`define DMEM_SIZE_CUSTOM
//`define DMEM_SIZE_32_KB
//`define DMEM_SIZE_24_KB
//`define DMEM_SIZE_16_KB
//`define DMEM_SIZE_10_KB
//`define DMEM_SIZE_8_KB
//`define DMEM_SIZE_5_KB
//`define DMEM_SIZE_4_KB
//`define DMEM_SIZE_2p5_KB
//`define DMEM_SIZE_2_KB
//`define DMEM_SIZE_1_KB
//`define DMEM_SIZE_512_B
//`define DMEM_SIZE_256_B


// Include/Exclude Hardware Multiplier


// Include/Exclude Serial Debug interface


//============================================================================
//============================================================================
// ADVANCED SYSTEM CONFIGURATION (FOR EXPERIENCED USERS)
//============================================================================
//============================================================================

//-------------------------------------------------------
// Custom user version number
//-------------------------------------------------------
// This 5 bit field can be freely used in order to allow
// custom identification of the system through the debug
// interface.
// (see CPU_ID.USER_VERSION field in the documentation)
//-------------------------------------------------------


//-------------------------------------------------------
// Include/Exclude Watchdog timer
//-------------------------------------------------------
// When excluded, the following functionality will be
// lost:
//        - Watchog (both interval and watchdog modes)
//        - NMI interrupt edge selection
//        - Possibility to generate a software PUC reset
//-------------------------------------------------------


//-------------------------------------------------------
// Include/Exclude Non-Maskable-Interrupt support
//-------------------------------------------------------


//-------------------------------------------------------
// Input synchronizers
//-------------------------------------------------------
// In some cases, the asynchronous input ports might
// already be synchronized externally.
// If an extensive CDC design review showed that this
// is really the case,  the individual synchronizers
// can be disabled with the following defines.
//
// Notes:
//        - all three signals are all sampled in the MCLK domain
//
//        - the dbg_en signal reset the debug interface
//         when 0. Therefore make sure it is glitch free.
//
//-------------------------------------------------------
//`define SYNC_CPU_EN
//`define SYNC_DBG_EN


//-------------------------------------------------------
// Peripheral Memory Space:
//-------------------------------------------------------
// The original MSP430 architecture map the peripherals
// from 0x0000 to 0x01FF (i.e. 512B of the memory space).
// The following defines allow you to expand this space
// up to 32 kB (i.e. from 0x0000 to 0x7fff).
// As a consequence, the data memory mapping will be
// shifted up and a custom linker script will therefore
// be required by the GCC compiler.
//-------------------------------------------------------
//`define PER_SIZE_CUSTOM
//`define PER_SIZE_32_KB
//`define PER_SIZE_16_KB
//`define PER_SIZE_8_KB
//`define PER_SIZE_4_KB
//`define PER_SIZE_2_KB
//`define PER_SIZE_1_KB


//-------------------------------------------------------
// Defines the debugger CPU_CTL.RST_BRK_EN reset value
// (CPU break on PUC reset)
//-------------------------------------------------------
// When defined, the CPU will automatically break after
// a PUC occurrence by default. This is typically useful
// when the program memory can only be initialized through
// the serial debug interface.
//-------------------------------------------------------


//============================================================================
//============================================================================
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//============================================================================
//============================================================================
//
// IMPORTANT NOTE:  Please update following configuration options ONLY if
//                 you have a good reason to do so... and if you know what
//                 you are doing :-P
//
//============================================================================

//-------------------------------------------------------
// Select serial debug interface protocol
//-------------------------------------------------------
//    DBG_UART -> Enable UART (8N1) debug interface
//    DBG_I2C  -> Enable I2C debug interface
//-------------------------------------------------------
//`define DBG_I2C


//-------------------------------------------------------
// Enable the I2C broadcast address
//-------------------------------------------------------
// For multicore systems, a common I2C broadcast address
// can be given to all oMSP cores in order to
// synchronously RESET, START, STOP, or STEP all CPUs
// at once with a single I2C command.
// If you have a single openMSP430 in your system,
// this option can stay commented-out.
//-------------------------------------------------------
//`define DBG_I2C_BROADCAST


//-------------------------------------------------------
// Number of hardware breakpoint/watchpoint units
// (each unit contains two hardware addresses available
// for breakpoints or watchpoints):
//   - DBG_HWBRK_0 -> Include hardware breakpoints unit 0
//   - DBG_HWBRK_1 -> Include hardware breakpoints unit 1
//   - DBG_HWBRK_2 -> Include hardware breakpoints unit 2
//   - DBG_HWBRK_3 -> Include hardware breakpoints unit 3
//-------------------------------------------------------
// Please keep in mind that hardware breakpoints only
// make sense whenever the program memory is not an SRAM
// (i.e. Flash/OTP/ROM/...) or when you are interested
// in data breakpoints.
//-------------------------------------------------------
//`define  DBG_HWBRK_0
//`define  DBG_HWBRK_1
//`define  DBG_HWBRK_2
//`define  DBG_HWBRK_3


//-------------------------------------------------------
// Enable/Disable the hardware breakpoint RANGE mode
//-------------------------------------------------------
// When enabled this feature allows the hardware breakpoint
// units to stop the cpu whenever an instruction or data
// access lays within an address range.
// Note that this feature is not supported by GDB.
//-------------------------------------------------------
//`define DBG_HWBRK_RANGE


//-------------------------------------------------------
// Custom Program/Data and Peripheral Memory Spaces
//-------------------------------------------------------
// The following values are valid only if the
// corresponding *_SIZE_CUSTOM defines are uncommented:
//
//  - *_SIZE   : size of the section in bytes.
//  - *_AWIDTH : address port width, this value must allow
//               to address all WORDS of the section
//               (i.e. the *_SIZE divided by 2)
//-------------------------------------------------------

// Custom Program memory (enabled with PMEM_SIZE_CUSTOM)

// Custom Data memory    (enabled with DMEM_SIZE_CUSTOM)

// Custom Peripheral memory  (enabled with PER_SIZE_CUSTOM)


//-------------------------------------------------------
// ASIC version
//-------------------------------------------------------
// When uncommented, this define will enable the
// ASIC system configuration section (see below) and
// will activate scan support for production test.
//
// WARNING: if you target an FPGA, leave this define
//          commented.
//-------------------------------------------------------
//`define ASIC


//============================================================================
//============================================================================
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS/PROFESSIONALS ONLY !!!! )
//============================================================================
//============================================================================

//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//=====        SYSTEM CONSTANTS --- !!!!!!!! DO NOT EDIT !!!!!!!!      =====//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//

//
// PROGRAM, DATA & PERIPHERAL MEMORY CONFIGURATION
//==================================================

// Program Memory Size
    
// Data Memory Size
    
// Peripheral Memory Size
    
// Data Memory Base Adresses

// Program & Data Memory most significant address bit (for 16 bit words)

//
// STATES, REGISTER FIELDS, ...
//======================================

// Instructions type

// Single-operand arithmetic

// Conditional jump

// Two-operand arithmetic

// Addressing modes

// Instruction state machine

// Execution state machine
// (swapped E_IRQ_0 and E_IRQ_2 values to suppress glitch generation warning from lint tool)

// ALU control signals

// Debug interface

// Debug interface CPU_CTL register

// Debug interface CPU_STAT register

// Debug interface BRKx_CTL register

// Basic clock module: BCSCTL1 Control Register

// Basic clock module: BCSCTL2 Control Register

// MCLK Clock gate

// SMCLK Clock gate

//
// DEBUG INTERFACE EXTRA CONFIGURATION
//======================================

// Debug interface: CPU version

// Debug interface: Software breakpoint opcode

// Debug UART interface auto data synchronization
// If the following define is commented out, then
// the DBG_UART_BAUD and DBG_DCO_FREQ need to be properly
// defined.

// Debug UART interface data rate
//      In order to properly setup the UART debug interface, you
//      need to specify the DCO_CLK frequency (DBG_DCO_FREQ) and
//      the chosen BAUD rate from the UART interface.
//
//`define DBG_UART_BAUD    9600
//`define DBG_UART_BAUD   19200
//`define DBG_UART_BAUD   38400
//`define DBG_UART_BAUD   57600
//`define DBG_UART_BAUD  115200
//`define DBG_UART_BAUD  230400
//`define DBG_UART_BAUD  460800
//`define DBG_UART_BAUD  576000
//`define DBG_UART_BAUD  921600

// Debug interface input synchronizer

// Enable/Disable the hardware breakpoint RANGE mode
 
// Counter width for the debug interface UART

// Check configuration
     
//
// MULTIPLIER CONFIGURATION
//======================================

// If uncommented, the following define selects
// the 16x16 multiplier (1 cycle) instead of the
// default 16x8 multplier (2 cycles)
//`define MPY_16x16
  
//======================================
// CONFIGURATION CHECKS
//======================================
        
module  omsp_alu (

// OUTPUTs
    alu_out,                       // ALU output value
    alu_out_add,                   // ALU adder output value
    alu_stat,                      // ALU Status {V,N,Z,C}
    alu_stat_wr,                   // ALU Status write {V,N,Z,C}

// INPUTs
    dbg_halt_st,                   // Halt/Run status from CPU
    exec_cycle,                    // Instruction execution cycle
    inst_alu,                      // ALU control signals
    inst_bw,                       // Decoded Inst: byte width
    inst_jmp,                      // Decoded Inst: Conditional jump
    inst_so,                       // Single-operand arithmetic
    op_dst,                        // Destination operand
    op_src,                        // Source operand
    status                         // R2 Status {V,N,Z,C}
);

// OUTPUTs
//=========
output       [15:0] alu_out;       // ALU output value
output       [15:0] alu_out_add;   // ALU adder output value
output        [3:0] alu_stat;      // ALU Status {V,N,Z,C}
output        [3:0] alu_stat_wr;   // ALU Status write {V,N,Z,C}

// INPUTs
//=========
input               dbg_halt_st;   // Halt/Run status from CPU
input               exec_cycle;    // Instruction execution cycle
input        [11:0] inst_alu;      // ALU control signals
input               inst_bw;       // Decoded Inst: byte width
input         [7:0] inst_jmp;      // Decoded Inst: Conditional jump
input         [7:0] inst_so;       // Single-operand arithmetic
input        [15:0] op_dst;        // Destination operand
input        [15:0] op_src;        // Source operand
input         [3:0] status;        // R2 Status {V,N,Z,C}


//=============================================================================
// 1)  FUNCTIONS
//=============================================================================

function [4:0] bcd_add;

   input [3:0] X;
   input [3:0] Y;
   input       C_;

   reg   [4:0] Z_;
   begin
      Z_ = {1'b0,X}+{1'b0,Y}+{4'b0,C_};
      if (Z_<5'd10) bcd_add = Z_;
      else          bcd_add = Z_+5'd6;
   end

endfunction


//=============================================================================
// 2)  INSTRUCTION FETCH/DECODE CONTROL STATE MACHINE
//=============================================================================
// SINGLE-OPERAND ARITHMETIC:
//-----------------------------------------------------------------------------
//   Mnemonic   S-Reg,   Operation                               Status bits
//              D-Reg,                                            V  N  Z  C
//
//   RRC         dst     C->MSB->...LSB->C                        *  *  *  *
//   RRA         dst     MSB->MSB->...LSB->C                      0  *  *  *
//   SWPB        dst     Swap bytes                               -  -  -  -
//   SXT         dst     Bit7->Bit8...Bit15                       0  *  *  *
//   PUSH        src     SP-2->SP, src->@SP                       -  -  -  -
//   CALL        dst     SP-2->SP, PC+2->@SP, dst->PC             -  -  -  -
//   RETI                TOS->SR, SP+2->SP, TOS->PC, SP+2->SP     *  *  *  *
//
//-----------------------------------------------------------------------------
// TWO-OPERAND ARITHMETIC:
//-----------------------------------------------------------------------------
//   Mnemonic   S-Reg,   Operation                               Status bits
//              D-Reg,                                            V  N  Z  C
//
//   MOV       src,dst    src            -> dst                   -  -  -  -
//   ADD       src,dst    src +  dst     -> dst                   *  *  *  *
//   ADDC      src,dst    src +  dst + C -> dst                   *  *  *  *
//   SUB       src,dst    dst + ~src + 1 -> dst                   *  *  *  *
//   SUBC      src,dst    dst + ~src + C -> dst                   *  *  *  *
//   CMP       src,dst    dst + ~src + 1                          *  *  *  *
//   DADD      src,dst    src +  dst + C -> dst (decimaly)        *  *  *  *
//   BIT       src,dst    src &  dst                              0  *  *  *
//   BIC       src,dst   ~src &  dst     -> dst                   -  -  -  -
//   BIS       src,dst    src |  dst     -> dst                   -  -  -  -
//   XOR       src,dst    src ^  dst     -> dst                   *  *  *  *
//   AND       src,dst    src &  dst     -> dst                   0  *  *  *
//
//-----------------------------------------------------------------------------
// * the status bit is affected
// - the status bit is not affected
// 0 the status bit is cleared
// 1 the status bit is set
//-----------------------------------------------------------------------------

// Invert source for substract and compare instructions.
wire        op_src_inv_cmd = exec_cycle & (inst_alu[0]);
wire [15:0] op_src_inv     = {16{op_src_inv_cmd}} ^ op_src;


// Mask the bit 8 for the Byte instructions for correct flags generation
wire        op_bit8_msk     = ~exec_cycle | ~inst_bw;
wire [16:0] op_src_in       = {1'b0, {op_src_inv[15:8] & {8{op_bit8_msk}}}, op_src_inv[7:0]};
wire [16:0] op_dst_in       = {1'b0, {op_dst[15:8]     & {8{op_bit8_msk}}}, op_dst[7:0]};

// Clear the source operand (= jump offset) for conditional jumps
wire        jmp_not_taken  = (inst_jmp[6]  & ~(status[3]^status[2])) |
                             (inst_jmp[5] &  (status[3]^status[2])) |
                             (inst_jmp[4]  &  ~status[2])            |
                             (inst_jmp[3]  &  ~status[0])            |
                             (inst_jmp[2] &   status[0])            |
                             (inst_jmp[1] &  ~status[1])            |
                             (inst_jmp[0] &   status[1]);
wire [16:0] op_src_in_jmp  = op_src_in & {17{~jmp_not_taken}};

// Adder / AND / OR / XOR
wire [16:0] alu_add        = op_src_in_jmp + op_dst_in;
wire [16:0] alu_and        = op_src_in     & op_dst_in;
wire [16:0] alu_or         = op_src_in     | op_dst_in;
wire [16:0] alu_xor        = op_src_in     ^ op_dst_in;


// Incrementer
wire        alu_inc         = exec_cycle & ((inst_alu[2] & status[0]) |
                                             inst_alu[1]);
wire [16:0] alu_add_inc    = alu_add + {16'h0000, alu_inc};



// Decimal adder (DADD)
wire  [4:0] alu_dadd0      = bcd_add(op_src_in[3:0],   op_dst_in[3:0],  status[0]);
wire  [4:0] alu_dadd1      = bcd_add(op_src_in[7:4],   op_dst_in[7:4],  alu_dadd0[4]);
wire  [4:0] alu_dadd2      = bcd_add(op_src_in[11:8],  op_dst_in[11:8], alu_dadd1[4]);
wire  [4:0] alu_dadd3      = bcd_add(op_src_in[15:12], op_dst_in[15:12],alu_dadd2[4]);
wire [16:0] alu_dadd       = {alu_dadd3, alu_dadd2[3:0], alu_dadd1[3:0], alu_dadd0[3:0]};


// Shifter for rotate instructions (RRC & RRA)
wire        alu_shift_msb  = inst_so[0] ? status[0]     :
	                     inst_bw       ? op_src[7]     : op_src[15];
wire        alu_shift_7    = inst_bw       ? alu_shift_msb : op_src[8];
wire [16:0] alu_shift      = {1'b0, alu_shift_msb, op_src[15:9], alu_shift_7, op_src[7:1]};


// Swap bytes / Extend Sign
wire [16:0] alu_swpb       = {1'b0, op_src[7:0],op_src[15:8]};
wire [16:0] alu_sxt        = {1'b0, {8{op_src[7]}},op_src[7:0]};


// Combine short paths toghether to simplify final ALU mux
wire        alu_short_thro = ~(inst_alu[4]   |
                               inst_alu[5]    |
                               inst_alu[6]   |
                               inst_alu[10] |
                               inst_so[1]       |
                               inst_so[3]);

wire [16:0] alu_short      = ({17{inst_alu[4]}}   & alu_and)   |
                             ({17{inst_alu[5]}}    & alu_or)    |
                             ({17{inst_alu[6]}}   & alu_xor)   |
                             ({17{inst_alu[10]}} & alu_shift) |
                             ({17{inst_so[1]}}       & alu_swpb)  |
                             ({17{inst_so[3]}}        & alu_sxt)   |
                             ({17{alu_short_thro}}       & op_src_in);


// ALU output mux
wire [16:0] alu_out_nxt    = (inst_so[7] | dbg_halt_st |
                              inst_alu[3]) ? alu_add_inc :
                              inst_alu[7] ? alu_dadd    : alu_short;

assign      alu_out        =  alu_out_nxt[15:0];
assign      alu_out_add    =  alu_add[15:0];


//-----------------------------------------------------------------------------
// STATUS FLAG GENERATION
//-----------------------------------------------------------------------------

wire    V_xor       = inst_bw ? (op_src_in[7]  & op_dst_in[7])  :
                                (op_src_in[15] & op_dst_in[15]);

wire    V           = inst_bw ? ((~op_src_in[7]  & ~op_dst_in[7]  &  alu_out[7])  |
                                 ( op_src_in[7]  &  op_dst_in[7]  & ~alu_out[7])) :
                                ((~op_src_in[15] & ~op_dst_in[15] &  alu_out[15]) |
                                 ( op_src_in[15] &  op_dst_in[15] & ~alu_out[15]));

wire    N           = inst_bw ?  alu_out[7]       : alu_out[15];
wire    Z           = inst_bw ? (alu_out[7:0]==0) : (alu_out==0);
wire    C           = inst_bw ?  alu_out[8]       : alu_out_nxt[16];

assign  alu_stat    = inst_alu[10]  ? {1'b0, N,Z,op_src_in[0]} :
                      inst_alu[8] ? {1'b0, N,Z,~Z}           :
                      inst_alu[6]    ? {V_xor,N,Z,~Z}           : {V,N,Z,C};

assign  alu_stat_wr = (inst_alu[9] & exec_cycle) ? 4'b1111 : 4'b0000;


endmodule // omsp_alu

//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
// 
// *File Name: openMSP430_undefines.v
// 
// *Module Description:
//                      openMSP430 Verilog `undef file
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 23 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2009-08-30 18:39:26 +0200 (Sun, 30 Aug 2009) $
//----------------------------------------------------------------------------

//----------------------------------------------------------------------------
// BASIC SYSTEM CONFIGURATION
//----------------------------------------------------------------------------

// Program Memory sizes


// Data Memory sizes


// Include/Exclude Hardware Multiplier


// Include Debug interface



//----------------------------------------------------------------------------
// ADVANCED SYSTEM CONFIGURATION (FOR EXPERIENCED USERS)
//----------------------------------------------------------------------------

// Custom user version number


// Include/Exclude Watchdog timer


// Include/Exclude Non-Maskable-Interrupt support


// Input synchronizers


// Peripheral Memory Space:


// Let the CPU break after a PUC occurrence by default



//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Serial Debug interface protocol


// Enable the I2C broadcast address

// Number of hardware breakpoint units

// Enable/Disable the hardware breakpoint RANGE mode

// Custom Program/Data and Peripheral Memory Spaces







// ASIC version


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// ASIC/FPGA-like clocking

// Fine grained clock gating

// LFXT clock domain

// MCLK: Clock Mux

// SMCLK: Clock Mux

// WATCHDOG: Clock Mux

// MCLK: Clock divider

// SMCLK: Clock divider (/1/2/4/8)

// ACLK: Clock divider (/1/2/4/8)

// LOW POWER MODE: CPUOFF

// LOW POWER MODE: SCG0

// LOW POWER MODE: SCG1

// LOW POWER MODE: OSCOFF


//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//=====        SYSTEM CONSTANTS --- !!!!!!!! DO NOT EDIT !!!!!!!!      =====//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//

// Program Memory Size



// Data Memory Size



// Peripheral Memory Size



// Data Memory Base Adresses


// Program & Data Memory most significant address bit (for 16 bit words)




// Instructions type




// Single-operand arithmetic









// Conditional jump









// Two-operand arithmetic













// Addressing modes









// Instruction state machine







// Execution state machine















// ALU control signals













// Debug interface




// Debug interface CPU_CTL register








// Debug interface CPU_STAT register






// Debug interface BRKx_CTL register







// Basic clock module: BCSCTL1 Control Register


// Basic clock module: BCSCTL2 Control Register





// MCLK Clock gate

// SMCLK Clock gate

//
// DEBUG INTERFACE EXTRA CONFIGURATION
//======================================

// Debug interface: CPU version


// Debug interface: Software breakpoint opcode


// Debug UART interface auto data synchronization


// Debug UART interface data rate




// Debug interface input synchronizer


// Enable/Disable the hardware breakpoint RANGE mode


// Counter width for the debug interface UART


//
// MULTIPLIER CONFIGURATION
//======================================

