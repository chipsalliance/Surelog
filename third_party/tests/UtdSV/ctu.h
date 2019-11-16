/*
* ========== Copyright Header Begin ==========================================
* 
* OpenSPARC T1 Processor File: ctu.h
* Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
* DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
* 
* The above named program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public
* License version 2 as published by the Free Software Foundation.
* 
* The above named program is distributed in the hope that it will be 
* useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* General Public License for more details.
* 
* You should have received a copy of the GNU General Public
* License along with this work; if not, write to the Free Software
* Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
* 
* ========== Copyright Header End ============================================
*/

//*****************************
//Instruction Opcodes
//*****************************

`define TAP_EXTEST            6'h00
`define TAP_BYPASS            6'h3f
`define TAP_IDCODE            6'h01
`define TAP_SAMPLE_PRELOAD    6'h02
`define TAP_HIGHZ             6'h03
`define TAP_CLAMP             6'h04

`define TAP_CREG_ADDR          6'h08
`define TAP_CREG_WDATA         6'h09
`define TAP_CREG_RDATA         6'h0a
`define TAP_CREG_SCRATCH       6'h0b
`define TAP_IOB_WR             6'h0c
`define TAP_IOB_RD             6'h0d
`define TAP_IOB_WADDR          6'h0e
`define TAP_IOB_WDATA          6'h0f
`define TAP_IOB_RADDR          6'h10

`define TAP_MBIST_SERIAL       6'h14
`define TAP_MBIST_PARALLEL     6'h15
`define TAP_MBIST_RESULT       6'h16
`define TAP_MBIST_ABORT        6'h17

`define TAP_PLL_BYPASS         6'h18

`define TAP_CLK_STOP_ID        6'h1a
`define TAP_CLK_SEL            6'h1b  //mask ff00 for ck src

`define TAP_SSCAN_T0           6'h1c
`define TAP_SSCAN_T1           6'h1d
`define TAP_SSCAN_T2           6'h1e
`define TAP_SSCAN_T3           6'h1f

`define TAP_SCAN_PARALLEL      6'h20
`define TAP_SCAN_SERIAL        6'h21
`define TAP_SCAN_MTEST_LONG    6'h22
`define TAP_SCAN_MTEST_SHORT   6'h23
`define TAP_SCAN_BYPASS_EN     6'h24
`define TAP_SCAN_NSTEP         6'h25
`define TAP_SCAN_DUMP          6'h26

`define TAP_EFC_READ           6'h28 
`define TAP_EFC_BYPASS_DATA    6'h29 
`define TAP_EFC_BYPASS         6'h2a 
`define TAP_EFC_READ_MODE      6'h2b 
`define TAP_EFC_COL_ADDR       6'h2c
`define TAP_EFC_ROW_ADDR       6'h2d
`define TAP_EFC_DEST_SAMPLE    6'h2e

`define TAP_CMD_WIDTH           6
`define CTU_BIST_CNT           12
`define TAP_INSTR_WIDTH        18  // `TAP_CMD_WIDTH + `CTU_BIST_CNT


//*****************************
// CLK block
//*****************************

`define   CMP_GLOBAL_LATENCY  14'd7
`define   JBUS_GLOBAL_LATENCY 10'd3
`define   DRAM_GLOBAL_LATENCY 10'd2

`define   COIN_EDGE_LATENCY  14'd2

// Clock Unit Register Addresses (0x96_0000_00xx)
//      00   CLK_DIV
//      08   CLK_CTL
//      10   CLK_DBG_INT
//      18   CLK_DLL_CTRL
//      20   CLK_SCRATCH
//      28   CLK_JSYNC
//      2C   CLK_DSYNC

`define CLK_UPPER_ADDR  33'h 1_2C00_0000

`define CLK_ADDR_HI  6
`define CLK_DIV_ADDR   7'h00
`define CLK_CTRL_ADDR  7'h08
`define CLK_DBG_INIT_ADDR 7'h10
`define CLK_DLL_CTRL_ADDR 7'h18
`define CLK_SCRATCHPAD_ADDR 7'h20
`define CLK_JSYNC_ADDR 7'h28
`define CLK_DSYNC_ADDR 7'h30
`define CLK_DLL_BYP_ADDR 7'h38
`define CLK_VERSION_ADDR 7'h40

`define CLK_MAN_ID 16'h003E
`define CLK_IMPL_CODE 16'h0023
`define CLK_MAX_GLB_REG 3'b011
`define CLK_MAX_TRAP_LEVEL 8'h06
`define CLK_MAX_CWP 5'b00111


// CTRLSM


`define   ST_RSTSM_WAIT_POR 5'b00001
`define   ST_RSTSM_RST_PLL  5'b00010
`define   ST_RSTSM_WAIT_PLL_LCK 5'b00100
`define   ST_RSTSM_PLL_LCK     5'b01000
`define   ST_RSTSM_FREQ_CHG 5'b10000

`define   RSTSM_WAIT_POR 0
`define   RSTSM_RST_PLL  1
`define   RSTSM_WAIT_PLL_LCK 2
`define   RSTSM_PLL_LCK 3
`define   RSTSM_FREQ_CHG 4


`define    ST_CTRLSM_WAIT_LCK       14'b00000000000001 
`define    ST_CTRLSM_STR_CLK        14'b00000000000010
`define    ST_CTRLSM_EN_CLK         14'b00000000000100
`define    ST_CTRLSM_WAIT_J_RST     14'b00000000001000
`define    ST_CTRLSM_DE_DLLRST      14'b00000000010000
`define    ST_CTRLSM_DE_GRST        14'b00000000100000
`define    ST_CTRLSM_EFC_RD         14'b00000001000000
`define    ST_CTRLSM_WAIT_BISTDN    14'b00000010000000
`define    ST_CTRLSM_IDLE           14'b00000100000000
`define    ST_CTRLSM_A_GRST         14'b00001000000000
`define    ST_CTRLSM_A_DGRST        14'b00010000000000
`define    ST_CTRLSM_DIS_CLK        14'b00100000000000
`define    ST_CTRLSM_CHNG_FRQ       14'b01000000000000
`define    ST_CTRLSM_WAIT_RST       14'b10000000000000


`define    CTRLSM_WAIT_LCK       0
`define    CTRLSM_STR_CLK        1
`define    CTRLSM_EN_CLK         2
`define    CTRLSM_WAIT_J_RST     3
`define    CTRLSM_DE_DLLRST      4
`define    CTRLSM_DE_GRST        5
`define    CTRLSM_EFC_RD         6
`define    CTRLSM_WAIT_BISTDN    7 
`define    CTRLSM_IDLE           8
`define    CTRLSM_A_GRST         9 
`define    CTRLSM_A_DGRST        10
`define    CTRLSM_DIS_CLK        11 
`define    CTRLSM_CHNG_FRQ       12 
`define    CTRLSM_WAIT_RST       13 

// CLK CTRLSM

`define    CCTRLSM_MAX_ST     31

`define    CTU_SPARC0_ID      6'd0
`define    CTU_SPARC1_ID      6'd1
`define    CTU_SPARC2_ID      6'd2
`define    CTU_SPARC3_ID      6'd3
`define    CTU_SPARC4_ID      6'd4
`define    CTU_SPARC5_ID      6'd5
`define    CTU_SPARC6_ID      6'd6
`define    CTU_SPARC7_ID      6'd7
`define    CTU_SCDATA0_ID      6'd8
`define    CTU_SCDATA1_ID      6'd9 
`define    CTU_SCDATA2_ID      6'd10
`define    CTU_SCDATA3_ID      6'd11
`define    CTU_SCTAG0_ID      6'd12
`define    CTU_SCTAG1_ID      6'd13
`define    CTU_SCTAG2_ID      6'd14	
`define    CTU_SCTAG3_ID      6'd15	
`define    CTU_DRAM02_ID      6'd16	
`define    CTU_DRAM13_ID      6'd17
`define    CTU_CCX_ID      6'd18	
`define    CTU_FPU_ID      6'd19
`define    CTU_DDR0_ID     6'd20
`define    CTU_DDR1_ID     6'd21
`define    CTU_DDR2_ID     6'd22
`define    CTU_DDR3_ID     6'd23
`define    CTU_JBI_ID      6'd27
`define    CTU_JBUSL_ID    6'd29
`define    CTU_JBUSR_ID    6'd30
`define    CTU_IOB_ID      6'd31
`define    CTU_EFC_ID      6'd32
`define    CTU_DBG_ID      6'd33
`define    CTU_MISC_ID     6'd34

`define    CTU_SPARC0_IDD   31'b0000000000000000000000000000001   
`define    CTU_SPARC1_IDD   31'b0000000000000000000000000000010   
`define    CTU_SPARC2_IDD   31'b0000000000000000000000000000100   
`define    CTU_SPARC3_IDD   31'b0000000000000000000000000001000   
`define    CTU_SPARC4_IDD   31'b0000000000000000000000000010000   
`define    CTU_SPARC5_IDD   31'b0000000000000000000000000100000   
`define    CTU_SPARC6_IDD   31'b0000000000000000000000001000000   
`define    CTU_SPARC7_IDD   31'b0000000000000000000000010000000   
`define    CTU_SCDATA0_IDD  31'b0000000000000000000000100000000
`define    CTU_SCDATA1_IDD  31'b0000000000000000000001000000000
`define    CTU_SCDATA2_IDD  31'b0000000000000000000010000000000
`define    CTU_SCDATA3_IDD  31'b0000000000000000000100000000000
`define    CTU_SCTAG0_IDD   31'b0000000000000000001000000000000
`define    CTU_SCTAG1_IDD   31'b0000000000000000010000000000000
`define    CTU_SCTAG2_IDD   31'b0000000000000000100000000000000
`define    CTU_SCTAG3_IDD   31'b0000000000000001000000000000000
`define    CTU_DRAM02_IDD   31'b0000000000000010000000000000000
`define    CTU_DRAM13_IDD   31'b0000000000000100000000000000000
`define    CTU_CCX_IDD      31'b0000000000001000000000000000000
`define    CTU_FPU_IDD      31'b0000000000010000000000000000000
`define    CTU_DDR0_IDD     31'b0000000000100000000000000000000
`define    CTU_DDR1_IDD     31'b0000000001000000000000000000000
`define    CTU_DDR2_IDD     31'b0000000010000000000000000000000
`define    CTU_DDR3_IDD     31'b0000000100000000000000000000000
`define    CTU_JBI_IDD      31'b0000001000000000000000000000000
`define    CTU_JBUSL_IDD    31'b0000010000000000000000000000000
`define    CTU_JBUSR_IDD    31'b0000100000000000000000000000000
`define    CTU_IOB_IDD      31'b0001000000000000000000000000000
`define    CTU_EFC_IDD      31'b0010000000000000000000000000000
`define    CTU_DBG_IDD      31'b0100000000000000000000000000000
`define    CTU_MISC_IDD     31'b1000000000000000000000000000000


`define CCTRL_SPARC0_POS   0
`define CCTRL_SPARC1_POS   1
`define CCTRL_SPARC2_POS   2
`define CCTRL_SPARC3_POS   3
`define CCTRL_SPARC4_POS   4
`define CCTRL_SPARC5_POS   5
`define CCTRL_SPARC6_POS   6
`define CCTRL_SPARC7_POS   7
`define CCTRL_SCDATA0_POS   8
`define CCTRL_SCDATA1_POS   9
`define CCTRL_SCDATA2_POS   10 
`define CCTRL_SCDATA3_POS   11
`define CCTRL_SCTAG0_POS   12
`define CCTRL_SCTAG1_POS   13
`define CCTRL_SCTAG2_POS   14
`define CCTRL_SCTAG3_POS   15
`define CCTRL_DRAM02_POS   16
`define CCTRL_DRAM13_POS   17
`define CCTRL_CCX_POS   18
`define CCTRL_FPU_POS   19
`define CCTRL_DDR0_POS   20
`define CCTRL_DDR1_POS   21
`define CCTRL_DDR2_POS   22
`define CCTRL_DDR3_POS   23
`define CCTRL_JBI_POS   24
`define CCTRL_JBUSL_POS   25
`define CCTRL_JBUSR_POS   26
`define CCTRL_IOB_POS   27
`define CCTRL_EFC_POS   28
`define CCTRL_DBG_POS   29
`define CCTRL_MISC_POS   30

//*****************************
// Mask Codes
//*****************************

// Mask set code

`define MASK_MAJOR 4'h2

// 9-layer, 4-bit mask programmable codes

`define JTAGID     (9'b0, 9'b0, 9'b0, 9'b1)
`define MASK_MINOR (9'b0, 9'b0, 9'b0, 9'b0)

// Part Id and Manufacture Id for DW
`define CTU_PART_ID         16'h1AAA
`define CTU_MANUFACTURE_ID  11'h03E

