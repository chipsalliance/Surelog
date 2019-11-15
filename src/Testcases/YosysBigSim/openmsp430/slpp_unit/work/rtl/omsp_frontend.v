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
// *File Name: omsp_frontend.v
// 
// *Module Description:
//                       openMSP430 Instruction fetch and decode unit
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
        
module  omsp_frontend (

// OUTPUTs
    dbg_halt_st,                   // Halt/Run status from CPU
    decode_noirq,                  // Frontend decode instruction
    e_state,                       // Execution state
    exec_done,                     // Execution completed
    inst_ad,                       // Decoded Inst: destination addressing mode
    inst_as,                       // Decoded Inst: source addressing mode
    inst_alu,                      // ALU control signals
    inst_bw,                       // Decoded Inst: byte width
    inst_dest,                     // Decoded Inst: destination (one hot)
    inst_dext,                     // Decoded Inst: destination extended instruction word
    inst_irq_rst,                  // Decoded Inst: Reset interrupt
    inst_jmp,                      // Decoded Inst: Conditional jump
    inst_mov,                      // Decoded Inst: mov instruction
    inst_sext,                     // Decoded Inst: source extended instruction word
    inst_so,                       // Decoded Inst: Single-operand arithmetic
    inst_src,                      // Decoded Inst: source (one hot)
    inst_type,                     // Decoded Instruction type
    irq_acc,                       // Interrupt request accepted (one-hot signal)
    mab,                           // Frontend Memory address bus
    mb_en,                         // Frontend Memory bus enable
    mclk_enable,                   // Main System Clock enable
    mclk_wkup,                     // Main System Clock wake-up (asynchronous)
    nmi_acc,                       // Non-Maskable interrupt request accepted
    pc,                            // Program counter
    pc_nxt,                        // Next PC value (for CALL & IRQ)

// INPUTs
    cpu_en_s,                      // Enable CPU code execution (synchronous)
    cpuoff,                        // Turns off the CPU
    dbg_halt_cmd,                  // Halt CPU command
    dbg_reg_sel,                   // Debug selected register for rd/wr access
    fe_pmem_wait,                  // Frontend wait for Instruction fetch
    gie,                           // General interrupt enable
    irq,                           // Maskable interrupts
    mclk,                          // Main system clock
    mdb_in,                        // Frontend Memory data bus input
    nmi_pnd,                       // Non-maskable interrupt pending
    nmi_wkup,                      // NMI Wakeup
    pc_sw,                         // Program counter software value
    pc_sw_wr,                      // Program counter software write
    puc_rst,                       // Main system reset
    scan_enable,                   // Scan enable (active during scan shifting)
    wdt_irq,                       // Watchdog-timer interrupt
    wdt_wkup,                      // Watchdog Wakeup
    wkup                           // System Wake-up (asynchronous)
);

// OUTPUTs
//=========
output              dbg_halt_st;   // Halt/Run status from CPU
output              decode_noirq;  // Frontend decode instruction
output        [3:0] e_state;       // Execution state
output              exec_done;     // Execution completed
output        [7:0] inst_ad;       // Decoded Inst: destination addressing mode
output        [7:0] inst_as;       // Decoded Inst: source addressing mode
output       [11:0] inst_alu;      // ALU control signals
output              inst_bw;       // Decoded Inst: byte width
output       [15:0] inst_dest;     // Decoded Inst: destination (one hot)
output       [15:0] inst_dext;     // Decoded Inst: destination extended instruction word
output              inst_irq_rst;  // Decoded Inst: Reset interrupt
output        [7:0] inst_jmp;      // Decoded Inst: Conditional jump
output              inst_mov;      // Decoded Inst: mov instruction
output       [15:0] inst_sext;     // Decoded Inst: source extended instruction word
output        [7:0] inst_so;       // Decoded Inst: Single-operand arithmetic
output       [15:0] inst_src;      // Decoded Inst: source (one hot)
output        [2:0] inst_type;     // Decoded Instruction type
output       [13:0] irq_acc;       // Interrupt request accepted (one-hot signal)
output       [15:0] mab;           // Frontend Memory address bus
output              mb_en;         // Frontend Memory bus enable
output              mclk_enable;   // Main System Clock enable
output              mclk_wkup;     // Main System Clock wake-up (asynchronous)
output              nmi_acc;       // Non-Maskable interrupt request accepted
output       [15:0] pc;            // Program counter
output       [15:0] pc_nxt;        // Next PC value (for CALL & IRQ)

// INPUTs
//=========
input               cpu_en_s;      // Enable CPU code execution (synchronous)
input               cpuoff;        // Turns off the CPU
input               dbg_halt_cmd;  // Halt CPU command
input         [3:0] dbg_reg_sel;   // Debug selected register for rd/wr access
input               fe_pmem_wait;  // Frontend wait for Instruction fetch
input               gie;           // General interrupt enable
input        [13:0] irq;           // Maskable interrupts
input               mclk;          // Main system clock
input        [15:0] mdb_in;        // Frontend Memory data bus input
input               nmi_pnd;       // Non-maskable interrupt pending
input               nmi_wkup;      // NMI Wakeup
input        [15:0] pc_sw;         // Program counter software value
input               pc_sw_wr;      // Program counter software write
input               puc_rst;       // Main system reset
input               scan_enable;   // Scan enable (active during scan shifting)
input               wdt_irq;       // Watchdog-timer interrupt
input               wdt_wkup;      // Watchdog Wakeup
input               wkup;          // System Wake-up (asynchronous)


//=============================================================================
// 1)  UTILITY FUNCTIONS
//=============================================================================

// 16 bits one-hot decoder
function [15:0] one_hot16;
   input  [3:0] binary;
   begin
      one_hot16         = 16'h0000;
      one_hot16[binary] =  1'b1;
   end
endfunction
   
// 8 bits one-hot decoder
function [7:0] one_hot8;
   input  [2:0] binary;
   begin
      one_hot8         = 8'h00;
      one_hot8[binary] = 1'b1;
   end
endfunction
   

//=============================================================================
// 2)  PARAMETER DEFINITIONS
//=============================================================================

//
// 2.1) Instruction State machine definitons
//-------------------------------------------

parameter I_IRQ_FETCH = 3'h0;
parameter I_IRQ_DONE  = 3'h1;
parameter I_DEC       = 3'h2;        // New instruction ready for decode
parameter I_EXT1      = 3'h3;       // 1st Extension word
parameter I_EXT2      = 3'h4;       // 2nd Extension word
parameter I_IDLE      = 3'h5;       // CPU is in IDLE mode

//
// 2.2) Execution State machine definitons
//-------------------------------------------

parameter E_IRQ_0     = 4'h2;
parameter E_IRQ_1     = 4'h1;
parameter E_IRQ_2     = 4'h0;
parameter E_IRQ_3     = 4'h3;
parameter E_IRQ_4     = 4'h4;
parameter E_SRC_AD    = 4'h5;
parameter E_SRC_RD    = 4'h6;
parameter E_SRC_WR    = 4'h7;
parameter E_DST_AD    = 4'h8;
parameter E_DST_RD    = 4'h9;
parameter E_DST_WR    = 4'hA;
parameter E_EXEC      = 4'hB;
parameter E_JUMP      = 4'hC;
parameter E_IDLE      = 4'hD;


//=============================================================================
// 3)  FRONTEND STATE MACHINE
//=============================================================================

// The wire "conv" is used as state bits to calculate the next response
reg  [2:0] i_state;
reg  [2:0] i_state_nxt;

reg  [1:0] inst_sz;
wire [1:0] inst_sz_nxt;
wire       irq_detect;
wire [2:0] inst_type_nxt;
wire       is_const;
reg [15:0] sconst_nxt;
reg  [3:0] e_state_nxt;
           
// CPU on/off through the debug interface or cpu_en port
wire   cpu_halt_cmd = dbg_halt_cmd | ~cpu_en_s;
   
// States Transitions
always @(i_state    or inst_sz  or inst_sz_nxt  or pc_sw_wr or exec_done or
         irq_detect or cpuoff   or cpu_halt_cmd or e_state)
    case(i_state)
      I_IDLE     : i_state_nxt = (irq_detect & ~cpu_halt_cmd) ? I_IRQ_FETCH :
                                 (~cpuoff    & ~cpu_halt_cmd) ? I_DEC       : I_IDLE;
      I_IRQ_FETCH: i_state_nxt =  I_IRQ_DONE;
      I_IRQ_DONE : i_state_nxt =  I_DEC;
      I_DEC      : i_state_nxt =  irq_detect                  ? I_IRQ_FETCH :
                          (cpuoff | cpu_halt_cmd) & exec_done ? I_IDLE      :
                            cpu_halt_cmd & (e_state==E_IDLE)  ? I_IDLE      :
                                  pc_sw_wr                    ? I_DEC       :
                             ~exec_done & ~(e_state==E_IDLE)  ? I_DEC       :        // Wait in decode state
                                  (inst_sz_nxt!=2'b00)        ? I_EXT1      : I_DEC; // until execution is completed
      I_EXT1     : i_state_nxt =  pc_sw_wr                    ? I_DEC       : 
                                  (inst_sz!=2'b01)            ? I_EXT2      : I_DEC;
      I_EXT2     : i_state_nxt =  I_DEC;
    // pragma coverage off
      default    : i_state_nxt =  I_IRQ_FETCH;
    // pragma coverage on
    endcase

// State machine
always @(posedge mclk or posedge puc_rst)
  if (puc_rst) i_state  <= I_IRQ_FETCH;
  else         i_state  <= i_state_nxt;

// Utility signals
wire   decode_noirq =  ((i_state==I_DEC) &  (exec_done | (e_state==E_IDLE)));
wire   decode       =  decode_noirq | irq_detect;
wire   fetch        = ~((i_state==I_DEC) & ~(exec_done | (e_state==E_IDLE))) & ~(e_state_nxt==E_IDLE);

// Debug interface cpu status
reg    dbg_halt_st;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  dbg_halt_st <= 1'b0;
  else          dbg_halt_st <= cpu_halt_cmd & (i_state_nxt==I_IDLE);


//=============================================================================
// 4)  INTERRUPT HANDLING & SYSTEM WAKEUP
//=============================================================================

//
// 4.1) INTERRUPT HANDLING
//-----------------------------------------

// Detect reset interrupt
reg         inst_irq_rst;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                  inst_irq_rst <= 1'b1;
  else if (exec_done)           inst_irq_rst <= 1'b0;

//  Detect other interrupts
assign  irq_detect = (nmi_pnd | ((|irq | wdt_irq) & gie)) & ~cpu_halt_cmd & ~dbg_halt_st & (exec_done | (i_state==I_IDLE));

wire       mclk_irq_num = mclk;

// Select interrupt vector
reg  [3:0] irq_num;
always @(posedge mclk_irq_num or posedge puc_rst)
  if (puc_rst)         irq_num <= 4'hf;
  else if (irq_detect) irq_num <= nmi_pnd            ?  4'he :
                                  irq[13]            ?  4'hd :
                                  irq[12]            ?  4'hc :
                                  irq[11]            ?  4'hb :
                                 (irq[10] | wdt_irq) ?  4'ha :
                                  irq[9]             ?  4'h9 :
                                  irq[8]             ?  4'h8 :
                                  irq[7]             ?  4'h7 :
                                  irq[6]             ?  4'h6 :
                                  irq[5]             ?  4'h5 :
                                  irq[4]             ?  4'h4 :
                                  irq[3]             ?  4'h3 :
                                  irq[2]             ?  4'h2 :
                                  irq[1]             ?  4'h1 :
                                  irq[0]             ?  4'h0 : 4'hf;

wire [15:0] irq_addr    = {11'h7ff, irq_num, 1'b0};

// Interrupt request accepted
wire [15:0] irq_acc_all = one_hot16(irq_num) & {16{(i_state==I_IRQ_FETCH)}};
wire [13:0] irq_acc     = irq_acc_all[13:0];
wire        nmi_acc     = irq_acc_all[14];

//
// 4.2) SYSTEM WAKEUP
//-----------------------------------------

// In the CPUOFF feature is disabled, the wake-up and enable signals are always 1
assign  mclk_wkup   = 1'b1;
assign  mclk_enable = 1'b1;

//=============================================================================
// 5)  FETCH INSTRUCTION
//=============================================================================

//
// 5.1) PROGRAM COUNTER & MEMORY INTERFACE
//-----------------------------------------

// Program counter
reg  [15:0] pc;

// Compute next PC value
wire [15:0] pc_incr = pc + {14'h0000, fetch, 1'b0};
wire [15:0] pc_nxt  = pc_sw_wr               ? pc_sw    :
                      (i_state==I_IRQ_FETCH) ? irq_addr :
                      (i_state==I_IRQ_DONE)  ? mdb_in   :  pc_incr;

wire       mclk_pc = mclk;

always @(posedge mclk_pc or posedge puc_rst)
  if (puc_rst)  pc <= 16'h0000;
  else          pc <= pc_nxt;

// Check if ROM has been busy in order to retry ROM access
reg pmem_busy;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  pmem_busy <= 1'b0;
  else          pmem_busy <= fe_pmem_wait;
   
// Memory interface
wire [15:0] mab      = pc_nxt;
wire        mb_en    = fetch | pc_sw_wr | (i_state==I_IRQ_FETCH) | pmem_busy | (dbg_halt_st & ~cpu_halt_cmd);


//
// 5.2) INSTRUCTION REGISTER
//--------------------------------

// Instruction register
wire [15:0] ir  = mdb_in;

// Detect if source extension word is required
wire is_sext = (inst_as[1] | inst_as[4] | inst_as[6] | inst_as[5]);

// For the Symbolic addressing mode, add -2 to the extension word in order
// to make up for the PC address
wire [15:0] ext_incr = ((i_state==I_EXT1)     &  inst_as[4]) |
                       ((i_state==I_EXT2)     &  inst_ad[4]) |
                       ((i_state==I_EXT1)     & ~inst_as[4] &
                       ~(i_state_nxt==I_EXT2) &  inst_ad[4])   ? 16'hfffe : 16'h0000;

wire [15:0] ext_nxt  = ir + ext_incr;

// Store source extension word
reg [15:0] inst_sext;

wire       mclk_inst_sext = mclk;

always @(posedge mclk_inst_sext or posedge puc_rst)
  if (puc_rst)                                 inst_sext <= 16'h0000;
  else if (decode & is_const)                  inst_sext <= sconst_nxt;
  else if (decode & inst_type_nxt[1])  inst_sext <= {{5{ir[9]}},ir[9:0],1'b0};
  else if ((i_state==I_EXT1) & is_sext)        inst_sext <= ext_nxt;

// Source extension word is ready
wire inst_sext_rdy = (i_state==I_EXT1) & is_sext;


// Store destination extension word
reg [15:0] inst_dext;

wire       mclk_inst_dext = mclk;

always @(posedge mclk_inst_dext or posedge puc_rst)
  if (puc_rst)                           inst_dext <= 16'h0000;
  else if ((i_state==I_EXT1) & ~is_sext) inst_dext <= ext_nxt;
  else if  (i_state==I_EXT2)             inst_dext <= ext_nxt;

// Destination extension word is ready
wire inst_dext_rdy = (((i_state==I_EXT1) & ~is_sext) | (i_state==I_EXT2));


//=============================================================================
// 6)  DECODE INSTRUCTION
//=============================================================================

wire       mclk_decode = mclk;

//
// 6.1) OPCODE: INSTRUCTION TYPE
//----------------------------------------
// Instructions type is encoded in a one hot fashion as following:
//
// 3'b001: Single-operand arithmetic
// 3'b010: Conditional jump
// 3'b100: Two-operand arithmetic

reg  [2:0] inst_type;
assign     inst_type_nxt = {(ir[15:14]!=2'b00),
                            (ir[15:13]==3'b001),
                            (ir[15:13]==3'b000)} & {3{~irq_detect}};
   
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)      inst_type <= 3'b000;
  else if (decode)  inst_type <= inst_type_nxt;

//
// 6.2) OPCODE: SINGLE-OPERAND ARITHMETIC
//----------------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 8'b00000001: RRC
// 8'b00000010: SWPB
// 8'b00000100: RRA
// 8'b00001000: SXT
// 8'b00010000: PUSH
// 8'b00100000: CALL
// 8'b01000000: RETI
// 8'b10000000: IRQ

reg   [7:0] inst_so;
wire  [7:0] inst_so_nxt = irq_detect ? 8'h80 : (one_hot8(ir[9:7]) & {8{inst_type_nxt[0]}});

always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_so <= 8'h00;
  else if (decode) inst_so <= inst_so_nxt;

//
// 6.3) OPCODE: CONDITIONAL JUMP
//--------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 8'b00000001: JNE/JNZ
// 8'b00000010: JEQ/JZ
// 8'b00000100: JNC/JLO
// 8'b00001000: JC/JHS
// 8'b00010000: JN
// 8'b00100000: JGE
// 8'b01000000: JL
// 8'b10000000: JMP

reg   [2:0] inst_jmp_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_jmp_bin <= 3'h0;
  else if (decode) inst_jmp_bin <= ir[12:10];

wire [7:0] inst_jmp = one_hot8(inst_jmp_bin) & {8{inst_type[1]}};


//
// 6.4) OPCODE: TWO-OPERAND ARITHMETIC
//-------------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 12'b000000000001: MOV
// 12'b000000000010: ADD
// 12'b000000000100: ADDC
// 12'b000000001000: SUBC
// 12'b000000010000: SUB
// 12'b000000100000: CMP
// 12'b000001000000: DADD
// 12'b000010000000: BIT
// 12'b000100000000: BIC
// 12'b001000000000: BIS
// 12'b010000000000: XOR
// 12'b100000000000: AND

wire [15:0] inst_to_1hot = one_hot16(ir[15:12]) & {16{inst_type_nxt[2]}};
wire [11:0] inst_to_nxt  = inst_to_1hot[15:4];

reg         inst_mov;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_mov <= 1'b0;
  else if (decode) inst_mov <= inst_to_nxt[0];


//
// 6.5) SOURCE AND DESTINATION REGISTERS
//---------------------------------------

// Destination register
reg [3:0] inst_dest_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_dest_bin <= 4'h0;
  else if (decode) inst_dest_bin <= ir[3:0];

wire  [15:0] inst_dest = dbg_halt_st          ? one_hot16(dbg_reg_sel) :
                         inst_type[1] ? 16'h0001 :
                         inst_so[7]  |
                         inst_so[4] |
                         inst_so[5]       ? 16'h0002 :
                                                one_hot16(inst_dest_bin);


// Source register
reg [3:0] inst_src_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_src_bin <= 4'h0;
  else if (decode) inst_src_bin <= ir[11:8];

wire  [15:0] inst_src = inst_type[2] ? one_hot16(inst_src_bin)  :
                        inst_so[6]      ? 16'h0002 :
                        inst_so[7]       ? 16'h0001 :
                        inst_type[0] ? one_hot16(inst_dest_bin) : 16'h0000;


//
// 6.6) SOURCE ADDRESSING MODES
//--------------------------------
// Source addressing modes are encoded in a one hot fashion as following:
//
// 13'b0000000000001: Register direct.
// 13'b0000000000010: Register indexed.
// 13'b0000000000100: Register indirect.
// 13'b0000000001000: Register indirect autoincrement.
// 13'b0000000010000: Symbolic (operand is in memory at address PC+x).
// 13'b0000000100000: Immediate (operand is next word in the instruction stream).
// 13'b0000001000000: Absolute (operand is in memory at address x).
// 13'b0000010000000: Constant 4.
// 13'b0000100000000: Constant 8.
// 13'b0001000000000: Constant 0.
// 13'b0010000000000: Constant 1.
// 13'b0100000000000: Constant 2.
// 13'b1000000000000: Constant -1.

reg [12:0] inst_as_nxt;

wire [3:0] src_reg = inst_type_nxt[0] ? ir[3:0] : ir[11:8];

always @(src_reg or ir or inst_type_nxt)
  begin
     if (inst_type_nxt[1])
       inst_as_nxt =  13'b0000000000001;
     else if (src_reg==4'h3) // Addressing mode using R3
       case (ir[5:4])
         2'b11 : inst_as_nxt =  13'b1000000000000;
         2'b10 : inst_as_nxt =  13'b0100000000000;
         2'b01 : inst_as_nxt =  13'b0010000000000;
         default: inst_as_nxt =  13'b0001000000000;
       endcase
     else if (src_reg==4'h2) // Addressing mode using R2
       case (ir[5:4])
         2'b11 : inst_as_nxt =  13'b0000100000000;
         2'b10 : inst_as_nxt =  13'b0000010000000;
         2'b01 : inst_as_nxt =  13'b0000001000000;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
     else if (src_reg==4'h0) // Addressing mode using R0
       case (ir[5:4])
         2'b11 : inst_as_nxt =  13'b0000000100000;
         2'b10 : inst_as_nxt =  13'b0000000000100;
         2'b01 : inst_as_nxt =  13'b0000000010000;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
     else                    // General Addressing mode
       case (ir[5:4])
         2'b11 : inst_as_nxt =  13'b0000000001000;
         2'b10 : inst_as_nxt =  13'b0000000000100;
         2'b01 : inst_as_nxt =  13'b0000000000010;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
  end
assign    is_const = |inst_as_nxt[12:7];

reg [7:0] inst_as;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_as <= 8'h00;
  else if (decode) inst_as <= {is_const, inst_as_nxt[6:0]};


// 13'b0000010000000: Constant 4.
// 13'b0000100000000: Constant 8.
// 13'b0001000000000: Constant 0.
// 13'b0010000000000: Constant 1.
// 13'b0100000000000: Constant 2.
// 13'b1000000000000: Constant -1.
always @(inst_as_nxt)
  begin
     if (inst_as_nxt[7])        sconst_nxt = 16'h0004;
     else if (inst_as_nxt[8])   sconst_nxt = 16'h0008;
     else if (inst_as_nxt[9])   sconst_nxt = 16'h0000;
     else if (inst_as_nxt[10])  sconst_nxt = 16'h0001;
     else if (inst_as_nxt[11])  sconst_nxt = 16'h0002;
     else if (inst_as_nxt[12])  sconst_nxt = 16'hffff;
     else                       sconst_nxt = 16'h0000;
  end


//
// 6.7) DESTINATION ADDRESSING MODES
//-----------------------------------
// Destination addressing modes are encoded in a one hot fashion as following:
//
// 8'b00000001: Register direct.
// 8'b00000010: Register indexed.
// 8'b00010000: Symbolic (operand is in memory at address PC+x).
// 8'b01000000: Absolute (operand is in memory at address x).

reg  [7:0] inst_ad_nxt;

wire [3:0] dest_reg = ir[3:0];

always @(dest_reg or ir or inst_type_nxt)
  begin
     if (~inst_type_nxt[2])
       inst_ad_nxt =  8'b00000000;
     else if (dest_reg==4'h2)   // Addressing mode using R2
       case (ir[7])
         1'b1 : inst_ad_nxt =  8'b01000000;
         default: inst_ad_nxt =  8'b00000001;
       endcase
     else if (dest_reg==4'h0)   // Addressing mode using R0
       case (ir[7])
         1'b1 : inst_ad_nxt =  8'b00010000;
         default: inst_ad_nxt =  8'b00000001;
       endcase
     else                       // General Addressing mode
       case (ir[7])
         1'b1 : inst_ad_nxt =  8'b00000010;
         default: inst_ad_nxt =  8'b00000001;
       endcase
  end

reg [7:0] inst_ad;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_ad <= 8'h00;
  else if (decode) inst_ad <= inst_ad_nxt;


//
// 6.8) REMAINING INSTRUCTION DECODING
//-------------------------------------

// Operation size
reg       inst_bw;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)     inst_bw     <= 1'b0;
  else if (decode) inst_bw     <= ir[6] & ~inst_type_nxt[1] & ~irq_detect & ~cpu_halt_cmd;

// Extended instruction size
assign    inst_sz_nxt = {1'b0,  (inst_as_nxt[1] | inst_as_nxt[4] | inst_as_nxt[6] | inst_as_nxt[5])} +
                        {1'b0, ((inst_ad_nxt[1] | inst_ad_nxt[4] | inst_ad_nxt[6]) & ~inst_type_nxt[0])};
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_sz     <= 2'b00;
  else if (decode) inst_sz     <= inst_sz_nxt;


//=============================================================================
// 7)  EXECUTION-UNIT STATE MACHINE
//=============================================================================

// State machine registers
reg  [3:0] e_state;


// State machine control signals
//--------------------------------

wire src_acalc_pre =  inst_as_nxt[1]   | inst_as_nxt[4]    | inst_as_nxt[6];
wire src_rd_pre    =  inst_as_nxt[2] | inst_as_nxt[3] | inst_as_nxt[5]  | inst_so_nxt[6];
wire dst_acalc_pre =  inst_ad_nxt[1]   | inst_ad_nxt[4]    | inst_ad_nxt[6];
wire dst_acalc     =  inst_ad[1]       | inst_ad[4]        | inst_ad[6];
wire dst_rd_pre    =  inst_ad_nxt[1]   | inst_so_nxt[4]    | inst_so_nxt[5] | inst_so_nxt[6];
wire dst_rd        =  inst_ad[1]       | inst_so[4]        | inst_so[5]     | inst_so[6];

wire inst_branch   =  (inst_ad_nxt[0] & (ir[3:0]==4'h0)) | inst_type_nxt[1] | inst_so_nxt[6];

reg exec_jmp;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                   exec_jmp <= 1'b0;
  else if (inst_branch & decode) exec_jmp <= 1'b1;
  else if (e_state==E_JUMP)      exec_jmp <= 1'b0;

reg exec_dst_wr;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                exec_dst_wr <= 1'b0;
  else if (e_state==E_DST_RD) exec_dst_wr <= 1'b1;
  else if (e_state==E_DST_WR) exec_dst_wr <= 1'b0;

reg exec_src_wr;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                                         exec_src_wr <= 1'b0;
  else if (inst_type[0] & (e_state==E_SRC_RD))  exec_src_wr <= 1'b1;
  else if ((e_state==E_SRC_WR) || (e_state==E_DST_WR)) exec_src_wr <= 1'b0;

reg exec_dext_rdy;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                exec_dext_rdy <= 1'b0;
  else if (e_state==E_DST_RD) exec_dext_rdy <= 1'b0;
  else if (inst_dext_rdy)     exec_dext_rdy <= 1'b1;

// Execution first state
wire [3:0] e_first_state = ~dbg_halt_st  & inst_so_nxt[7] ? E_IRQ_0  :
                            cpu_halt_cmd | (i_state==I_IDLE) ? E_IDLE   :
                            cpuoff                           ? E_IDLE   :
                            src_acalc_pre                    ? E_SRC_AD :
                            src_rd_pre                       ? E_SRC_RD :
                            dst_acalc_pre                    ? E_DST_AD :
                            dst_rd_pre                       ? E_DST_RD : E_EXEC;


// State machine
//--------------------------------

// States Transitions
always @(e_state       or dst_acalc     or dst_rd   or inst_sext_rdy or
         inst_dext_rdy or exec_dext_rdy or exec_jmp or exec_dst_wr   or
         e_first_state or exec_src_wr)
    case(e_state)
      E_IDLE   : e_state_nxt =  e_first_state;
      E_IRQ_0  : e_state_nxt =  E_IRQ_1;
      E_IRQ_1  : e_state_nxt =  E_IRQ_2;
      E_IRQ_2  : e_state_nxt =  E_IRQ_3;
      E_IRQ_3  : e_state_nxt =  E_IRQ_4;
      E_IRQ_4  : e_state_nxt =  E_EXEC;

      E_SRC_AD : e_state_nxt =  inst_sext_rdy     ? E_SRC_RD : E_SRC_AD;

      E_SRC_RD : e_state_nxt =  dst_acalc         ? E_DST_AD : 
                                 dst_rd           ? E_DST_RD : E_EXEC;

      E_DST_AD : e_state_nxt =  (inst_dext_rdy |
                                 exec_dext_rdy)   ? E_DST_RD : E_DST_AD;

      E_DST_RD : e_state_nxt =  E_EXEC;

      E_EXEC   : e_state_nxt =  exec_dst_wr       ? E_DST_WR :
                                exec_jmp          ? E_JUMP   :
                                exec_src_wr       ? E_SRC_WR : e_first_state;

      E_JUMP   : e_state_nxt =  e_first_state;
      E_DST_WR : e_state_nxt =  exec_jmp          ? E_JUMP   : e_first_state;
      E_SRC_WR : e_state_nxt =  e_first_state;
    // pragma coverage off
      default  : e_state_nxt =  E_IRQ_0;
    // pragma coverage on
    endcase

// State machine
always @(posedge mclk or posedge puc_rst)
  if (puc_rst) e_state  <= E_IRQ_1;
  else         e_state  <= e_state_nxt;


// Frontend State machine control signals
//----------------------------------------

wire exec_done = exec_jmp        ? (e_state==E_JUMP)   :
                 exec_dst_wr     ? (e_state==E_DST_WR) :
                 exec_src_wr     ? (e_state==E_SRC_WR) : (e_state==E_EXEC);


//=============================================================================
// 8)  EXECUTION-UNIT STATE CONTROL
//=============================================================================

//
// 8.1) ALU CONTROL SIGNALS
//-------------------------------------
//
// 12'b000000000001: Enable ALU source inverter
// 12'b000000000010: Enable Incrementer
// 12'b000000000100: Enable Incrementer on carry bit
// 12'b000000001000: Select Adder
// 12'b000000010000: Select AND
// 12'b000000100000: Select OR
// 12'b000001000000: Select XOR
// 12'b000010000000: Select DADD
// 12'b000100000000: Update N, Z & C (C=~Z)
// 12'b001000000000: Update all status bits
// 12'b010000000000: Update status bit for XOR instruction
// 12'b100000000000: Don't write to destination

reg  [11:0] inst_alu;

wire        alu_src_inv   = inst_to_nxt[4]  | inst_to_nxt[3] |
                            inst_to_nxt[5]  | inst_to_nxt[8] ;

wire        alu_inc       = inst_to_nxt[4]  | inst_to_nxt[5];

wire        alu_inc_c     = inst_to_nxt[2] | inst_to_nxt[6] |
                            inst_to_nxt[3];

wire        alu_add       = inst_to_nxt[1]  | inst_to_nxt[2]       |
                            inst_to_nxt[4]  | inst_to_nxt[3]       |
                            inst_to_nxt[5]  | inst_type_nxt[1] |
                            inst_so_nxt[6];

 
wire        alu_and       = inst_to_nxt[11]  | inst_to_nxt[8]  |
                            inst_to_nxt[7];

wire        alu_or        = inst_to_nxt[9];

wire        alu_xor       = inst_to_nxt[10];

wire        alu_dadd      = inst_to_nxt[6];

wire        alu_stat_7    = inst_to_nxt[7]  | inst_to_nxt[11]  |
                            inst_so_nxt[3];

wire        alu_stat_f    = inst_to_nxt[1]  | inst_to_nxt[2] |
                            inst_to_nxt[4]  | inst_to_nxt[3] |
                            inst_to_nxt[5]  | inst_to_nxt[6] |
                            inst_to_nxt[7]  | inst_to_nxt[10]  |
                            inst_to_nxt[11]  |
                            inst_so_nxt[0]  | inst_so_nxt[2]  |
                            inst_so_nxt[3];

wire        alu_shift     = inst_so_nxt[0]  | inst_so_nxt[2];

wire        exec_no_wr    = inst_to_nxt[5] | inst_to_nxt[7];

wire [11:0] inst_alu_nxt  = {exec_no_wr,
                             alu_shift,
                             alu_stat_f,
                             alu_stat_7,
                             alu_dadd,
                             alu_xor,
                             alu_or,
                             alu_and,
                             alu_add,
                             alu_inc_c,
                             alu_inc,
                             alu_src_inv};

always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_alu <= 12'h000;
  else if (decode) inst_alu <= inst_alu_nxt;


endmodule // omsp_frontend

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

