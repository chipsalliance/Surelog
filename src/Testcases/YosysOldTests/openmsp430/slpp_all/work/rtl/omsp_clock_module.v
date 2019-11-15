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
// *File Name: omsp_clock_module.v
// 
// *Module Description:
//                       Basic clock module implementation.
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
        
module  omsp_clock_module (

// OUTPUTs
    aclk,                         // ACLK
    aclk_en,                      // ACLK enable
    cpu_en_s,                     // Enable CPU code execution (synchronous)
    dbg_clk,                      // Debug unit clock
    dbg_en_s,                     // Debug interface enable (synchronous)
    dbg_rst,                      // Debug unit reset
    dco_enable,                   // Fast oscillator enable
    dco_wkup,                     // Fast oscillator wake-up (asynchronous)
    lfxt_enable,                  // Low frequency oscillator enable
    lfxt_wkup,                    // Low frequency oscillator wake-up (asynchronous)
    mclk,                         // Main system clock
    per_dout,                     // Peripheral data output
    por,                          // Power-on reset
    puc_pnd_set,                  // PUC pending set for the serial debug interface
    puc_rst,                      // Main system reset
    smclk,                        // SMCLK
    smclk_en,                     // SMCLK enable
	     
// INPUTs
    cpu_en,                       // Enable CPU code execution (asynchronous)
    cpuoff,                       // Turns off the CPU
    dbg_cpu_reset,                // Reset CPU from debug interface
    dbg_en,                       // Debug interface enable (asynchronous)
    dco_clk,                      // Fast oscillator (fast clock)
    lfxt_clk,                     // Low frequency oscillator (typ 32kHz)
    mclk_enable,                  // Main System Clock enable
    mclk_wkup,                    // Main System Clock wake-up (asynchronous)
    oscoff,                       // Turns off LFXT1 clock input
    per_addr,                     // Peripheral address
    per_din,                      // Peripheral data input
    per_en,                       // Peripheral enable (high active)
    per_we,                       // Peripheral write enable (high active)
    reset_n,                      // Reset Pin (low active, asynchronous)
    scan_enable,                  // Scan enable (active during scan shifting)
    scan_mode,                    // Scan mode
    scg0,                         // System clock generator 1. Turns off the DCO
    scg1,                         // System clock generator 1. Turns off the SMCLK
    wdt_reset                     // Watchdog-timer reset
);

// OUTPUTs
//=========
output              aclk;         // ACLK
output              aclk_en;      // ACLK enable
output              cpu_en_s;     // Enable CPU code execution (synchronous)
output              dbg_clk;      // Debug unit clock
output              dbg_en_s;     // Debug unit enable (synchronous)
output              dbg_rst;      // Debug unit reset
output              dco_enable;   // Fast oscillator enable
output              dco_wkup;     // Fast oscillator wake-up (asynchronous)
output              lfxt_enable;  // Low frequency oscillator enable
output              lfxt_wkup;    // Low frequency oscillator wake-up (asynchronous)
output              mclk;         // Main system clock
output       [15:0] per_dout;     // Peripheral data output
output              por;          // Power-on reset
output              puc_pnd_set;  // PUC pending set for the serial debug interface
output              puc_rst;      // Main system reset
output              smclk;        // SMCLK
output              smclk_en;     // SMCLK enable

// INPUTs
//=========
input               cpu_en;       // Enable CPU code execution (asynchronous)
input               cpuoff;       // Turns off the CPU
input               dbg_cpu_reset;// Reset CPU from debug interface
input               dbg_en;       // Debug interface enable (asynchronous)
input               dco_clk;      // Fast oscillator (fast clock)
input               lfxt_clk;     // Low frequency oscillator (typ 32kHz)
input               mclk_enable;  // Main System Clock enable
input               mclk_wkup;    // Main System Clock wake-up (asynchronous)
input               oscoff;       // Turns off LFXT1 clock input
input        [13:0] per_addr;     // Peripheral address
input        [15:0] per_din;      // Peripheral data input
input               per_en;       // Peripheral enable (high active)
input         [1:0] per_we;       // Peripheral write enable (high active)
input               reset_n;      // Reset Pin (low active, asynchronous)
input               scan_enable;  // Scan enable (active during scan shifting)
input               scan_mode;    // Scan mode
input               scg0;         // System clock generator 1. Turns off the DCO
input               scg1;         // System clock generator 1. Turns off the SMCLK
input               wdt_reset;    // Watchdog-timer reset


//=============================================================================
// 1)  WIRES & PARAMETER DECLARATION
//=============================================================================

// Register base address (must be aligned to decoder bit width)
parameter       [14:0] BASE_ADDR   = 15'h0050;

// Decoder bit width (defines how many bits are considered for address decoding)
parameter              DEC_WD      =  4;

// Register addresses offset
parameter [DEC_WD-1:0] BCSCTL1     =  'h7,
                       BCSCTL2     =  'h8;

// Register one-hot decoder utilities
parameter              DEC_SZ      =  (1 << DEC_WD);
parameter [DEC_SZ-1:0] BASE_REG    =  {{DEC_SZ-1{1'b0}}, 1'b1};

// Register one-hot decoder
parameter [DEC_SZ-1:0] BCSCTL1_D   = (BASE_REG << BCSCTL1),
                       BCSCTL2_D   = (BASE_REG << BCSCTL2);

// Local wire declarations
wire nodiv_mclk;
wire nodiv_mclk_n;
wire nodiv_smclk;


//============================================================================
// 2)  REGISTER DECODER
//============================================================================

// Local register selection
wire              reg_sel      =  per_en & (per_addr[13:DEC_WD-1]==BASE_ADDR[14:DEC_WD]);

// Register local address
wire [DEC_WD-1:0] reg_addr     =  {1'b0, per_addr[DEC_WD-2:0]};

// Register address decode
wire [DEC_SZ-1:0] reg_dec      = (BCSCTL1_D  &  {DEC_SZ{(reg_addr==(BCSCTL1 >>1))}}) |
                                 (BCSCTL2_D  &  {DEC_SZ{(reg_addr==(BCSCTL2 >>1))}});

// Read/Write probes
wire              reg_lo_write =  per_we[0] & reg_sel;
wire              reg_hi_write =  per_we[1] & reg_sel;
wire              reg_read     = ~|per_we   & reg_sel;

// Read/Write vectors
wire [DEC_SZ-1:0] reg_hi_wr    = reg_dec & {DEC_SZ{reg_hi_write}};
wire [DEC_SZ-1:0] reg_lo_wr    = reg_dec & {DEC_SZ{reg_lo_write}};
wire [DEC_SZ-1:0] reg_rd       = reg_dec & {DEC_SZ{reg_read}};


//============================================================================
// 3) REGISTERS
//============================================================================

// BCSCTL1 Register
//--------------
reg  [7:0] bcsctl1;
wire       bcsctl1_wr  = BCSCTL1[0] ? reg_hi_wr[BCSCTL1] : reg_lo_wr[BCSCTL1];
wire [7:0] bcsctl1_nxt = BCSCTL1[0] ? per_din[15:8]      : per_din[7:0];

wire [7:0] divax_mask = 8'h30;

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)          bcsctl1  <=  8'h00;
  else if (bcsctl1_wr)  bcsctl1  <=  bcsctl1_nxt & divax_mask; // Mask unused bits


// BCSCTL2 Register
//--------------
reg  [7:0] bcsctl2;
wire       bcsctl2_wr    = BCSCTL2[0] ? reg_hi_wr[BCSCTL2] : reg_lo_wr[BCSCTL2];
wire [7:0] bcsctl2_nxt   = BCSCTL2[0] ? per_din[15:8]      : per_din[7:0];

wire [7:0] selmx_mask = 8'h00;
wire [7:0] divmx_mask = 8'h00;
wire [7:0] sels_mask  = 8'h08;
wire [7:0] divsx_mask = 8'h06;

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)          bcsctl2  <=  8'h00;
  else if (bcsctl2_wr)  bcsctl2  <=  bcsctl2_nxt & ( sels_mask  | divsx_mask |
                                                     selmx_mask | divmx_mask); // Mask unused bits


//============================================================================
// 4) DATA OUTPUT GENERATION
//============================================================================

// Data output mux
wire [15:0] bcsctl1_rd   = {8'h00, (bcsctl1  & {8{reg_rd[BCSCTL1]}})}  << (8 & {4{BCSCTL1[0]}});
wire [15:0] bcsctl2_rd   = {8'h00, (bcsctl2  & {8{reg_rd[BCSCTL2]}})}  << (8 & {4{BCSCTL2[0]}});

wire [15:0] per_dout =  bcsctl1_rd   |
                        bcsctl2_rd;


//=============================================================================
// 5)  DCO_CLK / LFXT_CLK INTERFACES (WAKEUP, ENABLE, ...)
//=============================================================================


//-----------------------------------------------------------
// 5.1) HIGH SPEED SYSTEM CLOCK GENERATOR (DCO_CLK)
//-----------------------------------------------------------
// Note1: switching off the DCO osillator is only
//        supported in ASIC mode with SCG0 low power mode
//
// Note2: unlike the original MSP430 specification,
//        we allow to switch off the DCO even
//        if it is selected by MCLK or SMCLK.

wire por_a;
wire dco_wkup;
wire cpu_en_wkup;

   assign dco_enable    = 1'b1;
   assign dco_wkup      = 1'b1;


//-----------------------------------------------------------
// 5.2) LOW FREQUENCY CRYSTAL CLOCK GENERATOR (LFXT_CLK)
//-----------------------------------------------------------

// ASIC MODE
//------------------------------------------------
// Note: unlike the original MSP430 specification,
//       we allow to switch off the LFXT even
//       if it is selected by MCLK or SMCLK.

wire lfxt_clk_s;

omsp_sync_cell sync_cell_lfxt_clk (
    .data_out  (lfxt_clk_s),
    .data_in   (lfxt_clk),
    .clk       (mclk),
    .rst       (por)
);

reg  lfxt_clk_dly;
   
always @ (posedge mclk or posedge por)
  if (por) lfxt_clk_dly <=  1'b0;
  else     lfxt_clk_dly <=  lfxt_clk_s;    

wire   lfxt_clk_en = (lfxt_clk_s & ~lfxt_clk_dly) & ~(oscoff & ~bcsctl2[3]);
assign lfxt_enable = 1'b1;
assign lfxt_wkup   = 1'b0;

   
//=============================================================================
// 6)  CLOCK GENERATION
//=============================================================================

//-----------------------------------------------------------
// 6.1) GLOBAL CPU ENABLE
//-----------------------------------------------------------
// ACLK and SMCLK are directly switched-off
// with the cpu_en pin (after synchronization).
// MCLK will be switched off once the CPU reaches
// its IDLE state (through the mclk_enable signal)


// Synchronize CPU_EN signal to the MCLK domain
//----------------------------------------------
   assign cpu_en_s    = cpu_en;
   assign cpu_en_wkup = 1'b0;

// Synchronize CPU_EN signal to the ACLK domain
//----------------------------------------------
   wire   cpu_en_aux_s    = cpu_en_s;

// Synchronize CPU_EN signal to the SMCLK domain
//----------------------------------------------
// Note: the synchronizer is only required if there is a SMCLK_MUX


//-----------------------------------------------------------
// 6.2) MCLK GENERATION
//-----------------------------------------------------------

// Clock MUX
//----------------------------
assign nodiv_mclk   =  dco_clk;
assign nodiv_mclk_n = ~nodiv_mclk;
   

// Wakeup synchronizer
//----------------------------
wire mclk_wkup_s;

   assign mclk_wkup_s = 1'b0;


// Clock Divider
//----------------------------
// No need for extra synchronizer as bcsctl2
// comes from the same clock domain.

wire mclk_active = 1'b1;
   
  wire  mclk_div_en = mclk_active;


// Generate main system clock
//----------------------------
   assign mclk   = nodiv_mclk;


//-----------------------------------------------------------
// 6.3) ACLK GENERATION
//-----------------------------------------------------------

// ASIC MODE
//----------------------------
  reg       aclk_en;
  reg [2:0] aclk_div;
  wire      aclk_en_nxt =  lfxt_clk_en & ((bcsctl1[5:4]==2'b00) ?  1'b1 :
                                          (bcsctl1[5:4]==2'b01) ?  aclk_div[0]   :
                                          (bcsctl1[5:4]==2'b10) ? &aclk_div[1:0] :
                                                                     &aclk_div[2:0]);

  always @ (posedge mclk or posedge puc_rst)
    if (puc_rst)                                     aclk_div <=  3'h0;
    else if ((bcsctl1[5:4]!=2'b00) & lfxt_clk_en) aclk_div <=  aclk_div+3'h1;

  always @ (posedge mclk or posedge puc_rst)
    if (puc_rst)  aclk_en <=  1'b0;
    else          aclk_en <=  aclk_en_nxt & cpu_en_s;

  assign  aclk   = mclk;
   
//-----------------------------------------------------------
// 6.4) SMCLK GENERATION
//-----------------------------------------------------------

// Clock MUX
//----------------------------
assign nodiv_smclk = dco_clk;


// ASIC MODE
//----------------------------
reg       smclk_en;
reg [2:0] smclk_div;

wire      smclk_in     = ~scg1 & (bcsctl2[3] ? lfxt_clk_en : 1'b1);

wire      smclk_en_nxt = smclk_in & ((bcsctl2[2:1]==2'b00) ?  1'b1 :
                                     (bcsctl2[2:1]==2'b01) ?  smclk_div[0]   :
                                     (bcsctl2[2:1]==2'b10) ? &smclk_div[1:0] :
                                                                &smclk_div[2:0]);
   
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)  smclk_en <=  1'b0;
  else          smclk_en <=  smclk_en_nxt & cpu_en_s;

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)                                  smclk_div <=  3'h0;
  else if ((bcsctl2[2:1]!=2'b00) & smclk_in) smclk_div <=  smclk_div+3'h1;

wire  smclk  = mclk;


//-----------------------------------------------------------
// 6.5) DEBUG INTERFACE CLOCK GENERATION (DBG_CLK)
//-----------------------------------------------------------

// Synchronize DBG_EN signal to MCLK domain
//------------------------------------------
    assign dbg_en_s    =  dbg_en;
    wire   dbg_rst_nxt = ~dbg_en;


// Serial Debug Interface Clock gate
//------------------------------------------------
       assign dbg_clk = dco_clk;
  

//=============================================================================
// 7)  RESET GENERATION
//=============================================================================
//
// Whenever the reset pin (reset_n) is deasserted, the internal resets of the
// openMSP430 will be released in the following order:
//                1- POR
//                2- DBG_RST (if the sdi interface is enabled, i.e. dbg_en=1)
//                3- PUC
//
// Note: releasing the DBG_RST before PUC is particularly important in order
//       to allow the sdi interface to halt the cpu immediately after a PUC.
//
   
// Generate synchronized POR to MCLK domain
//------------------------------------------

// Asynchronous reset source
assign    por_a         =  !reset_n;
wire      por_noscan;

// Reset Synchronizer
omsp_sync_reset sync_reset_por (
    .rst_s        (por_noscan),
    .clk          (nodiv_mclk),
    .rst_a        (por_a)
);

// Scan Reset Mux
 assign por = por_noscan;

// Generate synchronized reset for the SDI
//------------------------------------------

// Reset Generation
reg  dbg_rst_noscan;
always @ (posedge mclk or posedge por)
  if (por)  dbg_rst_noscan <=  1'b1;
  else      dbg_rst_noscan <=  dbg_rst_nxt;

  // Scan Reset Mux
     assign dbg_rst = dbg_rst_noscan;
  


// Generate main system reset (PUC_RST)
//--------------------------------------
wire puc_noscan_n;
wire puc_a_scan;

// Asynchronous PUC reset
wire puc_a = por | wdt_reset;

// Synchronous PUC reset
wire puc_s = dbg_cpu_reset |                              // With the debug interface command

            (dbg_en_s & dbg_rst_noscan & ~puc_noscan_n);  // Sequencing making sure PUC is released
                                                          // after DBG_RST if the debug interface is
                                                          // enabled at power-on-reset time
// Scan Reset Mux
  assign puc_a_scan = puc_a;

// Reset Synchronizer
// (required because of the asynchronous watchdog reset)
omsp_sync_cell sync_cell_puc (
    .data_out  (puc_noscan_n),
    .data_in   (~puc_s),
    .clk       (mclk),
    .rst       (puc_a_scan)
);

// Scan Reset Mux
  assign puc_rst = ~puc_noscan_n;

// PUC pending set the serial debug interface
assign puc_pnd_set = ~puc_noscan_n;


endmodule // omsp_clock_module

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

