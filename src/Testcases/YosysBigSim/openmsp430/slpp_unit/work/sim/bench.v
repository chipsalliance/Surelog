
`timescale 1ns/1ps

// for memory layout
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
        
module testbench;

// UUT OUTPUTs
//============
wire               aclk;              // ASIC ONLY: ACLK
wire               aclk_en;           // FPGA ONLY: ACLK enable
wire               dbg_freeze;        // Freeze peripherals
wire               dbg_i2c_sda_out;   // Debug interface: I2C SDA OUT
wire               dbg_uart_txd;      // Debug interface: UART TXD
wire               dco_enable;        // ASIC ONLY: Fast oscillator enable
wire               dco_wkup;          // ASIC ONLY: Fast oscillator wake-up (asynchronous)
wire [6-1:0] dmem_addr;         // Data Memory address
wire               dmem_cen;          // Data Memory chip enable (low active)
wire        [15:0] dmem_din;          // Data Memory data input
wire         [1:0] dmem_wen;          // Data Memory write enable (low active)
wire        [13:0] irq_acc;           // Interrupt request accepted (one-hot signal)
wire               lfxt_enable;       // ASIC ONLY: Low frequency oscillator enable
wire               lfxt_wkup;         // ASIC ONLY: Low frequency oscillator wake-up (asynchronous)
wire               mclk;              // Main system clock
wire        [13:0] per_addr;          // Peripheral address
wire        [15:0] per_din;           // Peripheral data input
wire         [1:0] per_we;            // Peripheral write enable (high active)
wire               per_en;            // Peripheral enable (high active)
wire [10-1:0] pmem_addr;         // Program Memory address
wire               pmem_cen;          // Program Memory chip enable (low active)
wire        [15:0] pmem_din;          // Program Memory data input (optional)
wire         [1:0] pmem_wen;          // Program Memory write enable (low active) (optional)
wire               puc_rst;           // Main system reset
wire               smclk;             // ASIC ONLY: SMCLK
wire               smclk_en;          // FPGA ONLY: SMCLK enable


// UUT INPUTs
//===========
wire                cpu_en;            // Enable CPU code execution (asynchronous and non-glitchy)
wire                dbg_en;            // Debug interface enable (asynchronous and non-glitchy)
wire          [6:0] dbg_i2c_addr;      // Debug interface: I2C Address
wire          [6:0] dbg_i2c_broadcast; // Debug interface: I2C Broadcast Address (for multicore systems)
wire                dbg_i2c_scl;       // Debug interface: I2C SCL
wire                dbg_i2c_sda_in;    // Debug interface: I2C SDA IN
wire                dbg_uart_rxd;      // Debug interface: UART RXD (asynchronous)
wire                dco_clk;           // Fast oscillator (fast clock)
reg          [15:0] dmem_dout;         // Data Memory data output
wire  	     [13:0] irq;               // Maskable interrupts
wire                lfxt_clk;          // Low frequency oscillator (typ 32kHz)
wire  	            nmi;               // Non-maskable interrupt (asynchronous and non-glitchy)
reg          [15:0] per_dout;          // Peripheral data output
reg          [15:0] pmem_dout;         // Program Memory data output
wire                reset_n;           // Reset Pin (active low, asynchronous and non-glitchy)
wire                scan_enable;       // ASIC ONLY: Scan enable (active during scan shifting)
wire                scan_mode;         // ASIC ONLY: Scan mode
wire                wkup;              // ASIC ONLY: System Wake-up (asynchronous and non-glitchy)

openMSP430 UUT (

// OUTPUTs
    aclk,                               // ASIC ONLY: ACLK
    aclk_en,                            // FPGA ONLY: ACLK enable
    dbg_freeze,                         // Freeze peripherals
    dbg_i2c_sda_out,                    // Debug interface: I2C SDA OUT
    dbg_uart_txd,                       // Debug interface: UART TXD
    dco_enable,                         // ASIC ONLY: Fast oscillator enable
    dco_wkup,                           // ASIC ONLY: Fast oscillator wake-up (asynchronous)
    dmem_addr,                          // Data Memory address
    dmem_cen,                           // Data Memory chip enable (low active)
    dmem_din,                           // Data Memory data input
    dmem_wen,                           // Data Memory write enable (low active)
    irq_acc,                            // Interrupt request accepted (one-hot signal)
    lfxt_enable,                        // ASIC ONLY: Low frequency oscillator enable
    lfxt_wkup,                          // ASIC ONLY: Low frequency oscillator wake-up (asynchronous)
    mclk,                               // Main system clock
    per_addr,                           // Peripheral address
    per_din,                            // Peripheral data input
    per_we,                             // Peripheral write enable (high active)
    per_en,                             // Peripheral enable (high active)
    pmem_addr,                          // Program Memory address
    pmem_cen,                           // Program Memory chip enable (low active)
    pmem_din,                           // Program Memory data input (optional)
    pmem_wen,                           // Program Memory write enable (low active) (optional)
    puc_rst,                            // Main system reset
    smclk,                              // ASIC ONLY: SMCLK
    smclk_en,                           // FPGA ONLY: SMCLK enable

// INPUTs
    cpu_en,                             // Enable CPU code execution (asynchronous and non-glitchy)
    dbg_en,                             // Debug interface enable (asynchronous and non-glitchy)
    dbg_i2c_addr,                       // Debug interface: I2C Address
    dbg_i2c_broadcast,                  // Debug interface: I2C Broadcast Address (for multicore systems)
    dbg_i2c_scl,                        // Debug interface: I2C SCL
    dbg_i2c_sda_in,                     // Debug interface: I2C SDA IN
    dbg_uart_rxd,                       // Debug interface: UART RXD (asynchronous)
    dco_clk,                            // Fast oscillator (fast clock)
    dmem_dout,                          // Data Memory data output
    irq,                                // Maskable interrupts
    lfxt_clk,                           // Low frequency oscillator (typ 32kHz)
    nmi,                                // Non-maskable interrupt (asynchronous)
    per_dout,                           // Peripheral data output
    pmem_dout,                          // Program Memory data output
    reset_n,                            // Reset Pin (low active, asynchronous and non-glitchy)
    scan_enable,                        // ASIC ONLY: Scan enable (active during scan shifting)
    scan_mode,                          // ASIC ONLY: Scan mode
    wkup                                // ASIC ONLY: System Wake-up (asynchronous and non-glitchy)
);

// -----------------------------------------------------------------------------------

assign cpu_en = 1, dbg_en = 0;

reg clk, rst;
integer cycles;
initial begin
	clk <= 1;
	rst <= 0;
	cycles = 0;
	while (cycles < 8) begin
		#50; clk <= ~clk;
		cycles = cycles + 1;
		#50; clk <= ~clk;
	end
	rst <= #20 1;
	forever begin
		#50; clk <= ~clk;
		cycles = cycles + 1;
		#50; clk <= ~clk;
		if (cycles == 20000)
			$finish;
	end
end

assign dco_clk = clk;
assign lfxt_clk = 0;
assign irq = 0, nmi = 0;
assign reset_n = rst;
assign scan_enable = 0;
assign scan_mode = 0;
assign wkup = 0;

assign dbg_i2c_addr = 45;
assign dbg_i2c_broadcast = 67;
assign dbg_i2c_scl = 0;
assign dbg_i2c_sda_in = 0;
assign dbg_uart_rxd = 0;

// -----------------------------------------------------------------------------------

reg [15:0] addr;

reg [15:8] dmem_hi [128/2-1:0];
reg [ 7:0] dmem_lo [128/2-1:0];
reg [15:0] pmem    [2048/2-1:0];

integer output_idx;
reg [15:0] output_buf [1023:0];
event output_eof;

integer i;
initial begin
	for (i = 0; i < 128/2; i=i+1) begin
		dmem_hi[i] = 0;
		dmem_lo[i] = 0;
	end
	pmem[ 512] = 16'h4031;
pmem[ 513] = 16'h0280;
pmem[ 514] = 16'h4215;
pmem[ 515] = 16'h0120;
pmem[ 516] = 16'hf375;
pmem[ 517] = 16'hd035;
pmem[ 518] = 16'h5a08;
pmem[ 519] = 16'h403f;
pmem[ 520] = 16'h0000;
pmem[ 521] = 16'h930f;
pmem[ 522] = 16'h2407;
pmem[ 523] = 16'h4582;
pmem[ 524] = 16'h0120;
pmem[ 525] = 16'h832f;
pmem[ 526] = 16'h4f9f;
pmem[ 527] = 16'hfccc;
pmem[ 528] = 16'h0200;
pmem[ 529] = 16'h23f9;
pmem[ 530] = 16'h403f;
pmem[ 531] = 16'h0008;
pmem[ 532] = 16'h930f;
pmem[ 533] = 16'h2406;
pmem[ 534] = 16'h4582;
pmem[ 535] = 16'h0120;
pmem[ 536] = 16'h831f;
pmem[ 537] = 16'h43cf;
pmem[ 538] = 16'h0200;
pmem[ 539] = 16'h23fa;
pmem[ 540] = 16'h43a2;
pmem[ 541] = 16'h0100;
pmem[ 542] = 16'h403c;
pmem[ 543] = 16'h0003;
pmem[ 544] = 16'h430d;
pmem[ 545] = 16'h431a;
pmem[ 546] = 16'h4037;
pmem[ 547] = 16'h003f;
pmem[ 548] = 16'h4d0f;
pmem[ 549] = 16'hf03f;
pmem[ 550] = 16'h000f;
pmem[ 551] = 16'h4a0e;
pmem[ 552] = 16'h930f;
pmem[ 553] = 16'h2403;
pmem[ 554] = 16'h5e0e;
pmem[ 555] = 16'h831f;
pmem[ 556] = 16'h23fd;
pmem[ 557] = 16'h4d0f;
pmem[ 558] = 16'hc312;
pmem[ 559] = 16'h100f;
pmem[ 560] = 16'h110f;
pmem[ 561] = 16'h110f;
pmem[ 562] = 16'hf03f;
pmem[ 563] = 16'h7ffe;
pmem[ 564] = 16'hff1e;
pmem[ 565] = 16'h0200;
pmem[ 566] = 16'h2021;
pmem[ 567] = 16'h4c82;
pmem[ 568] = 16'h0100;
pmem[ 569] = 16'h4c0b;
pmem[ 570] = 16'h5b0b;
pmem[ 571] = 16'h4319;
pmem[ 572] = 16'hb31b;
pmem[ 573] = 16'h2418;
pmem[ 574] = 16'h4b0e;
pmem[ 575] = 16'h503e;
pmem[ 576] = 16'hfffd;
pmem[ 577] = 16'hc312;
pmem[ 578] = 16'h100e;
pmem[ 579] = 16'h9e07;
pmem[ 580] = 16'h2813;
pmem[ 581] = 16'h4e0f;
pmem[ 582] = 16'hc312;
pmem[ 583] = 16'h100f;
pmem[ 584] = 16'h110f;
pmem[ 585] = 16'h110f;
pmem[ 586] = 16'hf03f;
pmem[ 587] = 16'h3ffe;
pmem[ 588] = 16'hf03e;
pmem[ 589] = 16'h000f;
pmem[ 590] = 16'h4908;
pmem[ 591] = 16'h930e;
pmem[ 592] = 16'h2403;
pmem[ 593] = 16'h5808;
pmem[ 594] = 16'h831e;
pmem[ 595] = 16'h23fd;
pmem[ 596] = 16'hd88f;
pmem[ 597] = 16'h0200;
pmem[ 598] = 16'h5c0b;
pmem[ 599] = 16'h3fe4;
pmem[ 600] = 16'h531d;
pmem[ 601] = 16'h532c;
pmem[ 602] = 16'h903d;
pmem[ 603] = 16'h0040;
pmem[ 604] = 16'h23c7;
pmem[ 605] = 16'h4382;
pmem[ 606] = 16'h0100;
pmem[ 607] = 16'h430f;
pmem[ 608] = 16'hd032;
pmem[ 609] = 16'h00f0;
pmem[ 610] = 16'h3ffd;
pmem[ 611] = 16'h4030;
pmem[ 612] = 16'hfcca;
pmem[ 613] = 16'h1300;
pmem[1008] = 16'hfcc6;
pmem[1009] = 16'hfcc6;
pmem[1010] = 16'hfcc6;
pmem[1011] = 16'hfcc6;
pmem[1012] = 16'hfcc6;
pmem[1013] = 16'hfcc6;
pmem[1014] = 16'hfcc6;
pmem[1015] = 16'hfcc6;
pmem[1016] = 16'hfcc6;
pmem[1017] = 16'hfcc6;
pmem[1018] = 16'hfcc6;
pmem[1019] = 16'hfcc6;
pmem[1020] = 16'hfcc6;
pmem[1021] = 16'hfcc6;
pmem[1022] = 16'hfcc6;
pmem[1023] = 16'hfc00;
	output_idx = 0;
end

always @(posedge mclk) begin
	dmem_dout <= 'bx;
	pmem_dout <= 'bx;

	if (~dmem_cen && &dmem_wen) begin
		addr = 2*dmem_addr + 512;
		$display("+LOG+ %t -- DR  @%04x %x%x", $time, addr, dmem_hi[dmem_addr], dmem_lo[dmem_addr]);
		dmem_dout[15:8] <= dmem_hi[dmem_addr];
		dmem_dout[ 7:0] <= dmem_lo[dmem_addr];
	end

	if (~pmem_cen) begin
		addr = 2*pmem_addr - 2048;
		$display("+LOG+ %t -- PR  @%04x %x", $time, addr, pmem[pmem_addr]);
		pmem_dout <= pmem[pmem_addr];
	end

	if (~dmem_cen && ~dmem_wen) begin
		addr = 2*dmem_addr + 512;
		$display("+LOG+ %t -- DW  @%04x %x%x", $time, addr, ~dmem_wen[1] ? dmem_din[15:8] : 8'hzz, ~dmem_wen[0] ? dmem_din[ 7:0] : 8'hzz);
		if (~dmem_wen[1])
			dmem_hi[dmem_addr] <= dmem_din[15:8];
		if (~dmem_wen[0])
			dmem_lo[dmem_addr] <= dmem_din[ 7:0];
	end
end

always @(posedge mclk) begin
	per_dout <= 0;

	if (per_en && per_we) begin
		addr = 2*per_addr;
		$display("+LOG+ %t -- PER @%04x %x%x  <---", $time, addr, per_we[1] ? per_din[15:8] : 8'hzz, per_we[0] ? per_din[ 7:0] : 8'hzz);

		if (addr == 16'h0100) begin
			if (per_din == 0) begin
				-> output_eof;
			end else begin
				output_buf[output_idx] = per_din;
				output_idx = output_idx + 1;
			end
		end
	end
end

always @(output_eof) begin
	#1001;
	for (i = 0; i < output_idx; i = i + 1) begin
		$display("+OUT+ %t %d", $time, output_buf[i]);
	end
	$finish;
end

initial begin
	// $dumpfile("bench.vcd");
	// $dumpvars(0, testbench);
end

endmodule
