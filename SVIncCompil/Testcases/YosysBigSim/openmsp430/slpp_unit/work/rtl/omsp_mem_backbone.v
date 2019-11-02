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
// *File Name: omsp_mem_backbone.v
// 
// *Module Description:
//                       Memory interface backbone (decoder + arbiter)
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 151 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2012-07-23 00:24:11 +0200 (Mon, 23 Jul 2012) $
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
        
module  omsp_mem_backbone (

// OUTPUTs
    dbg_mem_din,                    // Debug unit Memory data input
    dmem_addr,                      // Data Memory address
    dmem_cen,                       // Data Memory chip enable (low active)
    dmem_din,                       // Data Memory data input
    dmem_wen,                       // Data Memory write enable (low active)
    eu_mdb_in,                      // Execution Unit Memory data bus input
    fe_mdb_in,                      // Frontend Memory data bus input
    fe_pmem_wait,                   // Frontend wait for Instruction fetch
    per_addr,                       // Peripheral address
    per_din,                        // Peripheral data input
    per_we,                         // Peripheral write enable (high active)
    per_en,                         // Peripheral enable (high active)
    pmem_addr,                      // Program Memory address
    pmem_cen,                       // Program Memory chip enable (low active)
    pmem_din,                       // Program Memory data input (optional)
    pmem_wen,                       // Program Memory write enable (low active) (optional)

// INPUTs
    dbg_halt_st,                    // Halt/Run status from CPU
    dbg_mem_addr,                   // Debug address for rd/wr access
    dbg_mem_dout,                   // Debug unit data output
    dbg_mem_en,                     // Debug unit memory enable
    dbg_mem_wr,                     // Debug unit memory write
    dmem_dout,                      // Data Memory data output
    eu_mab,                         // Execution Unit Memory address bus
    eu_mb_en,                       // Execution Unit Memory bus enable
    eu_mb_wr,                       // Execution Unit Memory bus write transfer
    eu_mdb_out,                     // Execution Unit Memory data bus output
    fe_mab,                         // Frontend Memory address bus
    fe_mb_en,                       // Frontend Memory bus enable
    mclk,                           // Main system clock
    per_dout,                       // Peripheral data output
    pmem_dout,                      // Program Memory data output
    puc_rst,                        // Main system reset
    scan_enable                     // Scan enable (active during scan shifting)
);

// OUTPUTs
//=========
output        [15:0] dbg_mem_din;   // Debug unit Memory data input
output [6-1:0] dmem_addr;     // Data Memory address
output               dmem_cen;      // Data Memory chip enable (low active)
output        [15:0] dmem_din;      // Data Memory data input
output         [1:0] dmem_wen;      // Data Memory write enable (low active)
output        [15:0] eu_mdb_in;     // Execution Unit Memory data bus input
output        [15:0] fe_mdb_in;     // Frontend Memory data bus input
output               fe_pmem_wait;  // Frontend wait for Instruction fetch
output        [13:0] per_addr;      // Peripheral address
output        [15:0] per_din;       // Peripheral data input
output         [1:0] per_we;        // Peripheral write enable (high active)
output               per_en;        // Peripheral enable (high active)
output [10-1:0] pmem_addr;     // Program Memory address
output               pmem_cen;      // Program Memory chip enable (low active)
output        [15:0] pmem_din;      // Program Memory data input (optional)
output         [1:0] pmem_wen;      // Program Memory write enable (low active) (optional)

// INPUTs
//=========
input                dbg_halt_st;   // Halt/Run status from CPU
input         [15:0] dbg_mem_addr;  // Debug address for rd/wr access
input         [15:0] dbg_mem_dout;  // Debug unit data output
input                dbg_mem_en;    // Debug unit memory enable
input          [1:0] dbg_mem_wr;    // Debug unit memory write
input         [15:0] dmem_dout;     // Data Memory data output
input         [14:0] eu_mab;        // Execution Unit Memory address bus
input                eu_mb_en;      // Execution Unit Memory bus enable
input          [1:0] eu_mb_wr;      // Execution Unit Memory bus write transfer
input         [15:0] eu_mdb_out;    // Execution Unit Memory data bus output
input         [14:0] fe_mab;        // Frontend Memory address bus
input                fe_mb_en;      // Frontend Memory bus enable
input                mclk;          // Main system clock
input         [15:0] per_dout;      // Peripheral data output
input         [15:0] pmem_dout;     // Program Memory data output
input                puc_rst;       // Main system reset
input                scan_enable;   // Scan enable (active during scan shifting)


//=============================================================================
// 1)  DECODER
//=============================================================================

// RAM Interface
//------------------

// Execution unit access
wire               eu_dmem_cen   = ~(eu_mb_en & (eu_mab>=(512>>1)) &
                                                (eu_mab<((512+128)>>1)));
wire        [15:0] eu_dmem_addr  = {1'b0, eu_mab}-(512>>1);

// Debug interface access
wire               dbg_dmem_cen  = ~(dbg_mem_en & (dbg_mem_addr[15:1]>=(512>>1)) &
                                                  (dbg_mem_addr[15:1]<((512+128)>>1)));
wire        [15:0] dbg_dmem_addr = {1'b0, dbg_mem_addr[15:1]}-(512>>1);

   
// RAM Interface
wire [6-1:0] dmem_addr     = ~dbg_dmem_cen ? dbg_dmem_addr[6-1:0] : eu_dmem_addr[6-1:0];
wire               dmem_cen      =  dbg_dmem_cen & eu_dmem_cen;
wire         [1:0] dmem_wen      = ~(dbg_mem_wr | eu_mb_wr);
wire        [15:0] dmem_din      = ~dbg_dmem_cen ? dbg_mem_dout : eu_mdb_out;


// ROM Interface
//------------------
parameter          PMEM_OFFSET   = (16'hFFFF-2048+1);

// Execution unit access (only read access are accepted)
wire               eu_pmem_cen   = ~(eu_mb_en & ~|eu_mb_wr & (eu_mab>=(PMEM_OFFSET>>1)));
wire        [15:0] eu_pmem_addr  = eu_mab-(PMEM_OFFSET>>1);

// Front-end access
wire               fe_pmem_cen   = ~(fe_mb_en & (fe_mab>=(PMEM_OFFSET>>1)));
wire        [15:0] fe_pmem_addr  = fe_mab-(PMEM_OFFSET>>1);

// Debug interface access
wire               dbg_pmem_cen  = ~(dbg_mem_en & (dbg_mem_addr[15:1]>=(PMEM_OFFSET>>1)));
wire        [15:0] dbg_pmem_addr = {1'b0, dbg_mem_addr[15:1]}-(PMEM_OFFSET>>1);

   
// ROM Interface (Execution unit has priority)
wire [10-1:0] pmem_addr     = ~dbg_pmem_cen ? dbg_pmem_addr[10-1:0] :
                                   ~eu_pmem_cen  ? eu_pmem_addr[10-1:0]  : fe_pmem_addr[10-1:0];
wire               pmem_cen      =  fe_pmem_cen & eu_pmem_cen & dbg_pmem_cen;
wire         [1:0] pmem_wen      = ~dbg_mem_wr;
wire        [15:0] pmem_din      =  dbg_mem_dout;

wire               fe_pmem_wait  = (~fe_pmem_cen & ~eu_pmem_cen);


// Peripherals
//--------------------
wire              dbg_per_en   =  dbg_mem_en & (dbg_mem_addr[15:1]<(512>>1));
wire              eu_per_en    =  eu_mb_en   & (eu_mab<(512>>1));

wire       [15:0] per_din      =  dbg_mem_en ? dbg_mem_dout               : eu_mdb_out;
wire        [1:0] per_we       =  dbg_mem_en ? dbg_mem_wr                 : eu_mb_wr;
wire              per_en       =  dbg_mem_en ? dbg_per_en                 : eu_per_en;
wire [8-1:0] per_addr_mux =  dbg_mem_en ? dbg_mem_addr[8-1+1:1] : eu_mab[8-1:0];
wire       [14:0] per_addr_ful =  {{15-8{1'b0}}, per_addr_mux};
wire       [13:0] per_addr     =   per_addr_ful[13:0];

reg   [15:0] per_dout_val;
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)  per_dout_val <= 16'h0000;
  else          per_dout_val <= per_dout;


// Frontend data Mux
//---------------------------------
// Whenever the frontend doesn't access the ROM,  backup the data

// Detect whenever the data should be backuped and restored
reg 	    fe_pmem_cen_dly;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst) fe_pmem_cen_dly <=  1'b0;
  else         fe_pmem_cen_dly <=  fe_pmem_cen;

wire fe_pmem_save    = ( fe_pmem_cen & ~fe_pmem_cen_dly) & ~dbg_halt_st;
wire fe_pmem_restore = (~fe_pmem_cen &  fe_pmem_cen_dly) |  dbg_halt_st;

wire mclk_bckup = mclk;
   
reg  [15:0] pmem_dout_bckup;
always @(posedge mclk_bckup or posedge puc_rst)
  if (puc_rst)           pmem_dout_bckup     <=  16'h0000;
  else if (fe_pmem_save) pmem_dout_bckup     <=  pmem_dout;

// Mux between the ROM data and the backup
reg         pmem_dout_bckup_sel;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)              pmem_dout_bckup_sel <=  1'b0;
  else if (fe_pmem_save)    pmem_dout_bckup_sel <=  1'b1;
  else if (fe_pmem_restore) pmem_dout_bckup_sel <=  1'b0;
    
assign fe_mdb_in = pmem_dout_bckup_sel ? pmem_dout_bckup : pmem_dout;


// Execution-Unit data Mux
//---------------------------------

// Select between peripherals, RAM and ROM
reg [1:0] eu_mdb_in_sel;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  eu_mdb_in_sel <= 2'b00;
  else          eu_mdb_in_sel <= {~eu_pmem_cen, per_en};

// Mux
assign      eu_mdb_in      = eu_mdb_in_sel[1] ? pmem_dout    :
                             eu_mdb_in_sel[0] ? per_dout_val : dmem_dout;

// Debug interface  data Mux
//---------------------------------

// Select between peripherals, RAM and ROM
reg   [1:0] dbg_mem_din_sel;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  dbg_mem_din_sel <= 2'b00;
  else          dbg_mem_din_sel <= {~dbg_pmem_cen, dbg_per_en};

       
// Mux
assign      dbg_mem_din  = dbg_mem_din_sel[1] ? pmem_dout    :
                           dbg_mem_din_sel[0] ? per_dout_val : dmem_dout;

   
endmodule // omsp_mem_backbone

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

