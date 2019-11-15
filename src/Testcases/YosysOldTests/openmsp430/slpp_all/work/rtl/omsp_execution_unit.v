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
// *File Name: omsp_execution_unit.v
// 
// *Module Description:
//                       openMSP430 Execution unit
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

// Peripheral Memory Space:

// Let the CPU break after a PUC occurrence by default

// Custom user version number

// Include/Exclude Watchdog timer

// Include/Exclude Non-Maskable-Interrupt support

//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Number of hardware breakpoint units

// Enable/Disable the hardware breakpoint RANGE mode

// Input synchronizers

// ASIC version


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Fine grained clock gating

// LFXT clock domain

// MCLK: Clock Mux

// SMCLK: Clock Mux

// WATCHDOG: Clock Mux

// MCLK: Clock divider

// SMCLK: Clock divider (/1/2/4/8)

// ACLK: Clock divider (/1/2/4/8)

// LOW POWER MODE: CPUOFF

// LOW POWER MODE: OSCOFF

// LOW POWER MODE: SCG0

// LOW POWER MODE: SCG1


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

// Debug interface selection

// Enable/Disable the hardware breakpoint RANGE mode

// Counter width for the debug interface UART

//
// MULTIPLIER CONFIGURATION
//======================================

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
// $Rev: 151 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2012-07-23 00:24:11 +0200 (Mon, 23 Jul 2012) $
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

// Peripheral Memory Space:

// Let the CPU break after a PUC occurrence by default

// Custom user version number

// Include/Exclude Watchdog timer

// Include/Exclude Non-Maskable-Interrupt support

//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Number of hardware breakpoint units

// Enable/Disable the hardware breakpoint RANGE mode

// Input synchronizers

// ASIC version


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Fine grained clock gating

// LFXT clock domain

// MCLK: Clock Mux

// SMCLK: Clock Mux

// WATCHDOG: Clock Mux

// MCLK: Clock divider

// SMCLK: Clock divider (/1/2/4/8)

// ACLK: Clock divider (/1/2/4/8)

// LOW POWER MODE: CPUOFF

// LOW POWER MODE: OSCOFF

// LOW POWER MODE: SCG0

// LOW POWER MODE: SCG1


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

// Debug interface selection

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
//`define PMEM_SIZE_8_KB
//`define PMEM_SIZE_4_KB
//`define PMEM_SIZE_2_KB
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


///-------------------------------------------------------
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
///`define PER_SIZE_8_KB
//`define PER_SIZE_4_KB
//`define PER_SIZE_2_KB
//`define PER_SIZE_1_KB
//`define PER_SIZE_512_B


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

// Debug interface selection
//             `define DBG_UART -> Enable UART (8N1) debug interface
//             `define DBG_JTAG -> DON'T UNCOMMENT, NOT SUPPORTED
//
//`define DBG_JTAG

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
        
module  omsp_execution_unit (

// OUTPUTs
    cpuoff,                        // Turns off the CPU
    dbg_reg_din,                   // Debug unit CPU register data input
    gie,                           // General interrupt enable
    mab,                           // Memory address bus
    mb_en,                         // Memory bus enable
    mb_wr,                         // Memory bus write transfer
    mdb_out,                       // Memory data bus output
    oscoff,                        // Turns off LFXT1 clock input
    pc_sw,                         // Program counter software value
    pc_sw_wr,                      // Program counter software write
    scg0,                          // System clock generator 1. Turns off the DCO
    scg1,                          // System clock generator 1. Turns off the SMCLK

// INPUTs
    dbg_halt_st,                   // Halt/Run status from CPU
    dbg_mem_dout,                  // Debug unit data output
    dbg_reg_wr,                    // Debug unit CPU register write
    e_state,                       // Execution state
    exec_done,                     // Execution completed
    inst_ad,                       // Decoded Inst: destination addressing mode
    inst_as,                       // Decoded Inst: source addressing mode
    inst_alu,                      // ALU control signals
    inst_bw,                       // Decoded Inst: byte width
    inst_dest,                     // Decoded Inst: destination (one hot)
    inst_dext,                     // Decoded Inst: destination extended instruction word
    inst_irq_rst,                  // Decoded Inst: reset interrupt
    inst_jmp,                      // Decoded Inst: Conditional jump
    inst_mov,                      // Decoded Inst: mov instruction
    inst_sext,                     // Decoded Inst: source extended instruction word
    inst_so,                       // Decoded Inst: Single-operand arithmetic
    inst_src,                      // Decoded Inst: source (one hot)
    inst_type,                     // Decoded Instruction type
    mclk,                          // Main system clock
    mdb_in,                        // Memory data bus input
    pc,                            // Program counter
    pc_nxt,                        // Next PC value (for CALL & IRQ)
    puc_rst,                       // Main system reset
    scan_enable                    // Scan enable (active during scan shifting)
);

// OUTPUTs
//=========
output 	            cpuoff;        // Turns off the CPU
output       [15:0] dbg_reg_din;   // Debug unit CPU register data input
output 	            gie;           // General interrupt enable
output       [15:0] mab;           // Memory address bus
output              mb_en;         // Memory bus enable
output        [1:0] mb_wr;         // Memory bus write transfer
output       [15:0] mdb_out;       // Memory data bus output
output 	            oscoff;        // Turns off LFXT1 clock input
output       [15:0] pc_sw;         // Program counter software value
output              pc_sw_wr;      // Program counter software write
output              scg0;          // System clock generator 1. Turns off the DCO
output              scg1;          // System clock generator 1. Turns off the SMCLK

// INPUTs
//=========
input               dbg_halt_st;   // Halt/Run status from CPU
input        [15:0] dbg_mem_dout;  // Debug unit data output
input               dbg_reg_wr;    // Debug unit CPU register write
input         [3:0] e_state;       // Execution state
input               exec_done;     // Execution completed
input         [7:0] inst_ad;       // Decoded Inst: destination addressing mode
input         [7:0] inst_as;       // Decoded Inst: source addressing mode
input        [11:0] inst_alu;      // ALU control signals
input               inst_bw;       // Decoded Inst: byte width
input        [15:0] inst_dest;     // Decoded Inst: destination (one hot)
input        [15:0] inst_dext;     // Decoded Inst: destination extended instruction word
input               inst_irq_rst;  // Decoded Inst: reset interrupt
input         [7:0] inst_jmp;      // Decoded Inst: Conditional jump
input               inst_mov;      // Decoded Inst: mov instruction
input        [15:0] inst_sext;     // Decoded Inst: source extended instruction word
input         [7:0] inst_so;       // Decoded Inst: Single-operand arithmetic
input        [15:0] inst_src;      // Decoded Inst: source (one hot)
input         [2:0] inst_type;     // Decoded Instruction type
input               mclk;          // Main system clock
input        [15:0] mdb_in;        // Memory data bus input
input        [15:0] pc;            // Program counter
input        [15:0] pc_nxt;        // Next PC value (for CALL & IRQ)
input               puc_rst;       // Main system reset
input               scan_enable;   // Scan enable (active during scan shifting)


//=============================================================================
// 1)  INTERNAL WIRES/REGISTERS/PARAMETERS DECLARATION
//=============================================================================

wire         [15:0] alu_out;
wire         [15:0] alu_out_add;
wire          [3:0] alu_stat;
wire          [3:0] alu_stat_wr;
wire         [15:0] op_dst;
wire         [15:0] op_src;
wire         [15:0] reg_dest;
wire         [15:0] reg_src;
wire         [15:0] mdb_in_bw;
wire         [15:0] mdb_in_val;
wire          [3:0] status;


//=============================================================================
// 2)  REGISTER FILE
//=============================================================================

wire reg_dest_wr  = ((e_state==4'hB) & (
                     (inst_type[2] & inst_ad[0] & ~inst_alu[11])  |
                     (inst_type[0] & inst_as[0] & ~(inst_so[4] | inst_so[5] | inst_so[6])) |
                      inst_type[1])) | dbg_reg_wr;

wire reg_sp_wr    = (((e_state==4'h1) | (e_state==4'h3)) & ~inst_irq_rst) |
                     ((e_state==4'h9) & ((inst_so[4] | inst_so[5]) &  ~inst_as[1] & ~((inst_as[2] | inst_as[3]) & inst_src[1]))) |
                     ((e_state==4'h5) & ((inst_so[4] | inst_so[5]) &  inst_as[1])) |
                     ((e_state==4'h6) & ((inst_so[4] | inst_so[5]) &  ((inst_as[2] | inst_as[3]) & inst_src[1])));

wire reg_sr_wr    =  (e_state==4'h9) & inst_so[6];

wire reg_sr_clr   =  (e_state==4'h0);

wire reg_pc_call  = ((e_state==4'hB)   & inst_so[5]) | 
                    ((e_state==4'hA) & inst_so[6]);

wire reg_incr     =  (exec_done          & inst_as[3]) |
                    ((e_state==4'h6) & inst_so[6])    |
                    ((e_state==4'hB)   & inst_so[6]);

assign dbg_reg_din = reg_dest;


omsp_register_file register_file_0 (

// OUTPUTs
    .cpuoff       (cpuoff),       // Turns off the CPU
    .gie          (gie),          // General interrupt enable
    .oscoff       (oscoff),       // Turns off LFXT1 clock input
    .pc_sw        (pc_sw),        // Program counter software value
    .pc_sw_wr     (pc_sw_wr),     // Program counter software write
    .reg_dest     (reg_dest),     // Selected register destination content
    .reg_src      (reg_src),      // Selected register source content
    .scg0         (scg0),         // System clock generator 1. Turns off the DCO
    .scg1         (scg1),         // System clock generator 1. Turns off the SMCLK
    .status       (status),       // R2 Status {V,N,Z,C}

// INPUTs
    .alu_stat     (alu_stat),     // ALU Status {V,N,Z,C}
    .alu_stat_wr  (alu_stat_wr),  // ALU Status write {V,N,Z,C}
    .inst_bw      (inst_bw),      // Decoded Inst: byte width
    .inst_dest    (inst_dest),    // Register destination selection
    .inst_src     (inst_src),     // Register source selection
    .mclk         (mclk),         // Main system clock
    .pc           (pc),           // Program counter
    .puc_rst      (puc_rst),      // Main system reset
    .reg_dest_val (alu_out),      // Selected register destination value
    .reg_dest_wr  (reg_dest_wr),  // Write selected register destination
    .reg_pc_call  (reg_pc_call),  // Trigger PC update for a CALL instruction
    .reg_sp_val   (alu_out_add),  // Stack Pointer next value
    .reg_sp_wr    (reg_sp_wr),    // Stack Pointer write
    .reg_sr_clr   (reg_sr_clr),   // Status register clear for interrupts
    .reg_sr_wr    (reg_sr_wr),    // Status Register update for RETI instruction
    .reg_incr     (reg_incr),     // Increment source register
    .scan_enable  (scan_enable)   // Scan enable (active during scan shifting)
);


//=============================================================================
// 3)  SOURCE OPERAND MUXING
//=============================================================================
// inst_as[`DIR]    : Register direct.   -> Source is in register
// inst_as[`IDX]    : Register indexed.  -> Source is in memory, address is register+offset
// inst_as[`INDIR]  : Register indirect.
// inst_as[`INDIR_I]: Register indirect autoincrement.
// inst_as[`SYMB]   : Symbolic (operand is in memory at address PC+x).
// inst_as[`IMM]    : Immediate (operand is next word in the instruction stream).
// inst_as[`ABS]    : Absolute (operand is in memory at address x).
// inst_as[`CONST]  : Constant.

wire src_reg_src_sel    =  (e_state==4'h2)                    |
                           (e_state==4'h0)                    |
                          ((e_state==4'h6) & ~inst_as[6]) |
                          ((e_state==4'h7) & ~inst_as[6]) |
                          ((e_state==4'hB)   &  inst_as[0] & ~inst_type[1]);

wire src_reg_dest_sel   =  (e_state==4'h1)                    |
                           (e_state==4'h3)                    |
                          ((e_state==4'h9) & (inst_so[4] | inst_so[5])) |
                          ((e_state==4'h5) & (inst_so[4] | inst_so[5]) & inst_as[1]);

wire src_mdb_in_val_sel = ((e_state==4'h9) &  inst_so[6])                     |
                          ((e_state==4'hB)   & (inst_as[2] | inst_as[3] |
                                                   inst_as[1]   | inst_as[4]    |
                                                   inst_as[6]));

wire src_inst_dext_sel =  ((e_state==4'h9) & ~(inst_so[4] | inst_so[5])) |
                          ((e_state==4'hA) & ~(inst_so[4] | inst_so[5]   |
                                                    inst_so[6]));

wire src_inst_sext_sel =  ((e_state==4'hB)   &  (inst_type[1] | inst_as[5] |
                                                    inst_as[7]      | inst_so[6]));


assign op_src = src_reg_src_sel     ?  reg_src    :
                src_reg_dest_sel    ?  reg_dest   :
                src_mdb_in_val_sel  ?  mdb_in_val :
                src_inst_dext_sel   ?  inst_dext  :
                src_inst_sext_sel   ?  inst_sext  : 16'h0000;


//=============================================================================
// 4)  DESTINATION OPERAND MUXING
//=============================================================================
// inst_ad[`DIR]    : Register direct.
// inst_ad[`IDX]    : Register indexed.
// inst_ad[`SYMB]   : Symbolic (operand is in memory at address PC+x).
// inst_ad[`ABS]    : Absolute (operand is in memory at address x).


wire dst_inst_sext_sel  = ((e_state==4'h6) & (inst_as[1] | inst_as[4] |
                                                   inst_as[6]))                |
                          ((e_state==4'h7) & (inst_as[1] | inst_as[4] |
                                                   inst_as[6]));

wire dst_mdb_in_bw_sel  = ((e_state==4'hA) &   inst_so[6]) |
                          ((e_state==4'hB)   & ~(inst_ad[0] | inst_type[1] |
                                                    inst_type[0]) & ~inst_so[6]);

wire dst_fffe_sel       =  (e_state==4'h2)  |
                           (e_state==4'h1)  |
                           (e_state==4'h3)  |
                          ((e_state==4'h9) & (inst_so[4] | inst_so[5]) & ~inst_so[6]) |
                          ((e_state==4'h5) & (inst_so[4] | inst_so[5]) & inst_as[1]) |
                          ((e_state==4'h6) & (inst_so[4] | inst_so[5]) & (inst_as[2] | inst_as[3]) & inst_src[1]);

wire dst_reg_dest_sel   = ((e_state==4'h9) & ~(inst_so[4] | inst_so[5] | inst_ad[6] | inst_so[6])) |
                          ((e_state==4'hA) &  ~inst_ad[6]) |
                          ((e_state==4'hB)   &  (inst_ad[0] | inst_type[1] |
                                                    inst_type[0]) & ~inst_so[6]);


assign op_dst = dbg_halt_st        ? dbg_mem_dout  :
                dst_inst_sext_sel  ? inst_sext     :
                dst_mdb_in_bw_sel  ? mdb_in_bw     :
                dst_reg_dest_sel   ? reg_dest      :
                dst_fffe_sel       ? 16'hfffe : 16'h0000;


//=============================================================================
// 5)  ALU
//=============================================================================

wire exec_cycle = (e_state==4'hB);

omsp_alu alu_0 (

// OUTPUTs
    .alu_out      (alu_out),      // ALU output value
    .alu_out_add  (alu_out_add),  // ALU adder output value
    .alu_stat     (alu_stat),     // ALU Status {V,N,Z,C}
    .alu_stat_wr  (alu_stat_wr),  // ALU Status write {V,N,Z,C}

// INPUTs
    .dbg_halt_st  (dbg_halt_st),  // Halt/Run status from CPU
    .exec_cycle   (exec_cycle),   // Instruction execution cycle
    .inst_alu     (inst_alu),     // ALU control signals
    .inst_bw      (inst_bw),      // Decoded Inst: byte width
    .inst_jmp     (inst_jmp),     // Decoded Inst: Conditional jump
    .inst_so      (inst_so),      // Single-operand arithmetic
    .op_dst       (op_dst),       // Destination operand
    .op_src       (op_src),       // Source operand
    .status       (status)        // R2 Status {V,N,Z,C}
);


//=============================================================================
// 6)  MEMORY INTERFACE
//=============================================================================

// Detect memory read/write access
assign      mb_en     = ((e_state==4'h1)  & ~inst_irq_rst)        |
                        ((e_state==4'h3)  & ~inst_irq_rst)        |
                        ((e_state==4'h6) & ~inst_as[5])       |
                         (e_state==4'h7)                         |
                        ((e_state==4'hB)   &  inst_so[6])      |
                        ((e_state==4'h9) & ~inst_type[0]
                                              & ~inst_mov)            |
                         (e_state==4'hA);

wire  [1:0] mb_wr_msk =  inst_alu[11]  ? 2'b00 :
                        ~inst_bw                ? 2'b11 :
                         alu_out_add[0]         ? 2'b10 : 2'b01;
assign      mb_wr     = ({2{(e_state==4'h1)}}  |
                         {2{(e_state==4'h3)}}  |
                         {2{(e_state==4'hA)}} |
                         {2{(e_state==4'h7)}}) & mb_wr_msk;

// Memory address bus
assign      mab       = alu_out_add[15:0];

// Memory data bus output
reg  [15:0] mdb_out_nxt;

wire        mclk_mdb_out_nxt = mclk;

always @(posedge mclk_mdb_out_nxt or posedge puc_rst)
  if (puc_rst)                                        mdb_out_nxt <= 16'h0000;
  else if (e_state==4'h9)                        mdb_out_nxt <= pc_nxt;
  else if ((e_state==4'hB & ~inst_so[5]) |
           (e_state==4'h2) | (e_state==4'h0)) mdb_out_nxt <= alu_out;

assign      mdb_out = inst_bw ? {2{mdb_out_nxt[7:0]}} : mdb_out_nxt;

// Format memory data bus input depending on BW
reg        mab_lsb;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)    mab_lsb <= 1'b0;
  else if (mb_en) mab_lsb <= alu_out_add[0];

assign mdb_in_bw  = ~inst_bw ? mdb_in :
                     mab_lsb ? {2{mdb_in[15:8]}} : mdb_in;

// Memory data bus input buffer (buffer after a source read)
reg         mdb_in_buf_en;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  mdb_in_buf_en <= 1'b0;
  else          mdb_in_buf_en <= (e_state==4'h6);

reg         mdb_in_buf_valid;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)               mdb_in_buf_valid <= 1'b0;
  else if (e_state==4'hB) mdb_in_buf_valid <= 1'b0;
  else if (mdb_in_buf_en)    mdb_in_buf_valid <= 1'b1;

reg  [15:0] mdb_in_buf;

wire        mclk_mdb_in_buf = mclk;

always @(posedge mclk_mdb_in_buf or posedge puc_rst)
  if (puc_rst)            mdb_in_buf <= 16'h0000;
  else if (mdb_in_buf_en) mdb_in_buf <= mdb_in_bw;

assign mdb_in_val = mdb_in_buf_valid ? mdb_in_buf : mdb_in_bw;


endmodule // omsp_execution_unit

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

// Peripheral Memory Space:

// Let the CPU break after a PUC occurrence by default

// Custom user version number

// Include/Exclude Watchdog timer

// Include/Exclude Non-Maskable-Interrupt support

//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Number of hardware breakpoint units

// Enable/Disable the hardware breakpoint RANGE mode

// Input synchronizers

// ASIC version


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Fine grained clock gating

// LFXT clock domain

// MCLK: Clock Mux

// SMCLK: Clock Mux

// WATCHDOG: Clock Mux

// MCLK: Clock divider

// SMCLK: Clock divider (/1/2/4/8)

// ACLK: Clock divider (/1/2/4/8)

// LOW POWER MODE: CPUOFF

// LOW POWER MODE: OSCOFF

// LOW POWER MODE: SCG0

// LOW POWER MODE: SCG1


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

// Debug interface selection

// Enable/Disable the hardware breakpoint RANGE mode

// Counter width for the debug interface UART

//
// MULTIPLIER CONFIGURATION
//======================================

