/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/
localparam   NUM_DFI_WPH       = 8;
localparam   NUM_DFI_RPH       = 8;
localparam   NUM_DFI_APH       = 8;
localparam   NUM_DFI_DQ        = 4;
localparam   NUM_DFI_CH        = 1;
localparam   NUM_CH            = 2;
localparam   NUM_DQ            = 2;
localparam   AWIDTH            = 7;
localparam   DQ_WIDTH          = 9;

//localparam   NUM_DFI_PHASES    = 4;
localparam   N                 = 12;  // DFI buffer Transactions
localparam   PLL_PERIOD        = 8 ;

// CSR RD/WRITE Macros.
`define REG_ADR(rname)      ```rname``_ADR

`define FRANGE(rname,fname) ```rname``_``fname``_FIELD

`define FWIDTH(rname,fname) ```rname``_``fname``_FIELD_WIDTH

`define CSR_WRF1(offset,rname,fname,fval) \
                                   csr_read(``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``fname``)] = fval; \
                                   csr_write(``offset``,`REG_ADR(``rname``), wdata)

`define CSR_WRF2(offset,rname,f1name,f2name,f1val,f2val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``f1name``)] = f1val; \
                                   wdata[`FRANGE(``rname``,``f2name``)] = f2val; \
                                   csr_write (``offset``,`REG_ADR(``rname``), wdata)

`define CSR_WRF3(offset,rname,f1name,f2name,f3name,f1val,f2val,f3val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``f1name``)] = f1val; \
                                   wdata[`FRANGE(``rname``,``f2name``)] = f2val; \
                                   wdata[`FRANGE(``rname``,``f3name``)] = f3val; \
                                   csr_write (``offset``,`REG_ADR(``rname``), wdata)

`define CSR_WRF4(offset,rname,f1name,f2name,f3name,f4name,f1val,f2val,f3val,f4val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``f1name``)] = f1val; \
                                   wdata[`FRANGE(``rname``,``f2name``)] = f2val; \
                                   wdata[`FRANGE(``rname``,``f3name``)] = f3val; \
                                   wdata[`FRANGE(``rname``,``f4name``)] = f4val; \
                                   csr_write (``offset``,`REG_ADR(``rname``), wdata)

`define CSR_WRF8(offset,rname,f1name,f2name,f3name,f4name,f5name,f6name,f7name,f8name,f1val,f2val,f3val,f4val,f5val,f6val,f7val,f8val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``f1name``)] = f1val; \
                                   wdata[`FRANGE(``rname``,``f2name``)] = f2val; \
                                   wdata[`FRANGE(``rname``,``f3name``)] = f3val; \
                                   wdata[`FRANGE(``rname``,``f4name``)] = f4val; \
                                   wdata[`FRANGE(``rname``,``f5name``)] = f5val; \
                                   wdata[`FRANGE(``rname``,``f6name``)] = f6val; \
                                   wdata[`FRANGE(``rname``,``f7name``)] = f7val; \
                                   wdata[`FRANGE(``rname``,``f8name``)] = f8val; \
                                   csr_write (``offset``,`REG_ADR(``rname``), wdata)

`define CSR_WR(offset,rname,val) \
                                   csr_write (``offset``,`REG_ADR(``rname``), val)

`define CSR_RDF1(offset,rname,fname,fval) \
                                   csr_read (``offset``,`REG_ADR(``rname``), rdata); \
                                   fval = rdata[`FRANGE(``rname``,``fname``)]

`define CSR_RDF2(offset,rname,f1name,f2name,f1val,f2val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), rdata); \
                                   f1val[`FWIDTH(``rname``,``f1name``)] = rdata[`FRANGE(``rname``,``f1name``)] ; \
                                   f2val[`FWIDTH(``rname``,``f2name``)] = rdata[`FRANGE(``rname``,``f2name``)]

`define CSR_RD(offset,rname,val) \
                                   csr_read (``offset``,`REG_ADR(``rname``), val)

//DUT Instantiation uses below parameters
localparam NUM_PHASE         =  4;                     // Number of Phases FIXME: update when `DDR_NUM_PHY_DATA_PHASES value changes.
localparam AHB_AWIDTH        =  32;                    // AHB Address width
localparam AHB_DWIDTH        =  32;                    // AHB Data width
localparam SWIDTH            =  8;                     // PHY Slice Width - FIXME - tie to the DQ width?
localparam DWIDTH            =  SWIDTH * 2;            // Data Width R+F
localparam BWIDTH            =  SWIDTH / 8;            // BYTE Width
localparam MWIDTH            =  BWIDTH ;               // Mask width
localparam TWIDTH            =  BWIDTH * 2;            // WCK Toggle width
localparam ERRWIDTH          =  BWIDTH * 4;            // Error Info Width
localparam TSWIDTH           =  8;                     // Timestamp Width
localparam DFI_BUF_IG_DEPTH  =  64;                    // DFI ingress buffer depth
localparam DFI_BUF_EG_DEPTH  =  64;                    // DFI egress buffer depth

// Clock Frequencies
localparam AHBCLK_PERIOD     = 10;
localparam REFCLK_FREQ       = 38.4;
localparam REFCLK_PERIOD     = 26;
localparam REFCLK_ALT_PERIOD = 26;
localparam TCK_PERIOD        = 25;

//DFI Buffer specific parameters.
localparam IG_WIDTH = TSWIDTH
                      + (NUM_DFI_WPH*(10+TWIDTH+((MWIDTH+SWIDTH)*NUM_DFI_DQ)))
                      + (NUM_DFI_APH*(2+2+1+AWIDTH));
localparam EG_WIDTH = TSWIDTH
                      + (NUM_DFI_RPH*(BWIDTH+MWIDTH+SWIDTH) * NUM_DFI_DQ)
                      + (NUM_DFI_APH*(2+2+AWIDTH));

typedef enum logic [2:0] {
  SDR_1   = 'd0,
  DDR_2   = 'd1,
  DDR_4   = 'd2,
  DDR_ALL = 'd3
} mode_t ;

typedef enum logic [3:0] {
  DQ0    = 'd1,
  DQ1    = 'd2,
  DQ_ALL = 'd3,
  CA     = 'd4,
  ALL    = 'd7
} byte_sel_t ;

typedef enum logic [2:0] {
  RANK0     = 'd1,
  RANK1     = 'd2,
  RANK_ALL  = 'd3
} rank_sel_t ;

`define TB_HIER wddr_tb_top.u_phy_1x32.u_phy
`define MCU_GP_REG_HIER `TB_HIER.u_ctrl_plane.u_ctrl_plane_csr.ctrl_csr
