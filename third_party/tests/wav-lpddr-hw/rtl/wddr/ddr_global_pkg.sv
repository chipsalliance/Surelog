
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

`ifndef DDR_GLOBAL_PKG
`define DDR_GLOBAL_PKG

`timescale 1ps/1ps

package ddr_global_pkg;

   // ------------------------------------------------------------------------
   // Memory Map
   // ------------------------------------------------------------------------

   parameter DDR_MCUTOP_OFFSET       = 32'h00000000;
   parameter DDR_MCUINTF_OFFSET      = 32'h00004000;
   parameter DDR_MCU_CSR_OFFSET      = 32'h00008000;
   parameter DDR_MCU_ITCM_OFFSET     = 32'h00010000;
   // parameter DDR_RESERVED_OFFSET  = 32'h00020000;
   parameter DDR_MCU_DTCM_OFFSET     = 32'h00050000;
   // parameter DDR_RESERVED_OFFSET  = 32'h00060000;
   parameter DDR_CMN_OFFSET          = 32'h00090000;
   parameter DDR_PLL_OFFSET          = 32'h00098000;
   parameter DDR_FSW_OFFSET          = 32'h000A0000;
   parameter DDR_CTRL_OFFSET         = 32'h000B0000;
   parameter DDR_DFI_OFFSET          = 32'h000C0000;
   parameter DDR_DFICH0_OFFSET       = 32'h000D0000;
   parameter DDR_DFICH1_OFFSET       = 32'h000E0000;
   parameter DDR_CH0_DQ0_OFFSET      = 32'h000F0000;
   parameter DDR_CH0_DQ1_OFFSET      = 32'h00100000;
   parameter DDR_CH0_CA_OFFSET       = 32'h00110000;
   parameter DDR_CH1_DQ0_OFFSET      = 32'h00120000;
   parameter DDR_CH1_DQ1_OFFSET      = 32'h00130000;
   parameter DDR_CH1_CA_OFFSET       = 32'h00140000;
   parameter DDR_PHY_SLV_RSVD_OFFSET = 32'h00150000;
   parameter DDR_EXT_SLV_OFFSET      = 32'h01000000;
   parameter DDR_EXT_RSVD_OFFSET     = 32'h02000000;

   parameter DDR_MCUMEM_SLV_OFFSET   = 32'h00010000;
   parameter DDR_INT_SLV_OFFSET      = 32'h00090000;

   parameter DDR_MCUTOP_SIZE         = 32'd 16384;
   parameter DDR_MCUINTF_SIZE        = 32'd 16384;
   parameter DDR_MCU_CSR_SIZE        = 32'd 32768;
   parameter DDR_MCU_ITCM_SIZE       = 32'd 65536;
   // parameter DDR_RESERVED_SIZE    = 32'd 196608;
   parameter DDR_MCU_DTCM_SIZE       = 32'd 65536;
   // parameter DDR_RESERVED_SIZE    = 32'd 196608;
   parameter DDR_CMN_SIZE            = 32'd 32768;
   parameter DDR_PLL_SIZE            = 32'd 32768;
   parameter DDR_FSW_SIZE            = 32'd 65536;
   parameter DDR_CTRL_SIZE           = 32'd 65536;
   parameter DDR_DFI_SIZE            = 32'd 65536;
   parameter DDR_DFICH0_SIZE         = 32'd 65536;
   parameter DDR_DFICH1_SIZE         = 32'd 65536;
   parameter DDR_CH0_DQ0_SIZE        = 32'd 65536;
   parameter DDR_CH0_DQ1_SIZE        = 32'd 65536;
   parameter DDR_CH0_CA_SIZE         = 32'd 65536;
   parameter DDR_CH1_DQ0_SIZE        = 32'd 65536;
   parameter DDR_CH1_DQ1_SIZE        = 32'd 65536;
   parameter DDR_CH1_CA_SIZE         = 32'd 65536;
   parameter DDR_PHY_SLV_RSVD_SIZE   = 32'd 15400960;
   parameter DDR_EXT_SLV_SIZE        = 32'd 16777216;
   // parameter DDR_RESERVED_SIZE    = 32'd 4261412863;

   // ------------------------------------------------------------------------
   // AXI
   // ------------------------------------------------------------------------

   parameter [1:0] AXI_RESP_OKAY      = 2'b00;
   parameter [1:0] AXI_RESP_EOKAY     = 2'b01;
   parameter [1:0] AXI_RESP_SLVERR    = 2'b10;
   parameter [1:0] AXI_RESP_DECERR    = 2'b11;

   parameter [3:0] AXI_CACHE_NA_NM_NB = 4'b0000;     // No allocation, No modify, No Buffer
   parameter [0:0] AXI_LOCK_NORM      = 1'b0;        // Normal access
   parameter [3:0] AXI_PROT_DA_NS_UP  = 4'b0010;     // Data access, Non-secure, unprivileged
   parameter [0:0] AXI_QOS_DEFAULT    = 1'b0;        // Default QoS

   parameter [1:0] AXI_BURST_INCR     = 2'b01;       // Only INCR is supported

   parameter [2:0] AXI_SIZE_BIT32     = 3'b010;      // 4-Byte (32-bit) per beat
   parameter [2:0] AXI_SIZE_BIT64     = 3'b011;      // 8-Byte (64-bit) per beat
   parameter [2:0] AXI_SIZE_BIT512    = 3'b110;      // 64-Byte (512-bit) per beat

   // ------------------------------------------------------------------------
   // Enumerations
   // ------------------------------------------------------------------------

   typedef enum logic [1:0] {
      WCK_STATIC_LOW  = 2'b00,
      WCK_STATIC_HIGH = 2'b01,
      WCK_TOGGLE      = 2'b10,
      WCK_FAST_TOGGLE = 2'b11
   } wck_t;

   // DFI GearBox
   parameter DFIGBWIDTH = 4;
   parameter DEC_DFIGBWIDTH = 10;

   typedef enum logic [DFIGBWIDTH-1:0] {
      DFIWGB_32TO16 = 'd8,
      DFIWGB_32TO8  = 'd7,
      DFIWGB_16TO8  = 'd6,
      DFIWGB_8TO8   = 'd5,
      DFIWGB_8TO4   = 'd4,
      DFIWGB_8TO2   = 'd3,   // Not Supported
      DFIWGB_4TO4   = 'd2,
      DFIWGB_4TO2   = 'd1,   // Not Supported
      DFIWGB_2TO2   = 'd0
   } dwgb_t;

   function automatic dwgb_t cast_dwgb_t (logic [DFIGBWIDTH-1:0] bits);
      dwgb_t cast;
      case(bits)
        'd8    : cast_dwgb_t = DFIWGB_32TO16;
        'd7    : cast_dwgb_t = DFIWGB_32TO8;
        'd6    : cast_dwgb_t = DFIWGB_16TO8;
        'd5    : cast_dwgb_t = DFIWGB_8TO8;
        'd4    : cast_dwgb_t = DFIWGB_8TO4;
        'd3    : cast_dwgb_t = DFIWGB_8TO2;
        'd2    : cast_dwgb_t = DFIWGB_4TO4;
        'd1    : cast_dwgb_t = DFIWGB_4TO2;
        'd0    : cast_dwgb_t = DFIWGB_2TO2;
        default: cast_dwgb_t = DFIWGB_2TO2;
      endcase
      return cast_dwgb_t;
   endfunction : cast_dwgb_t

   typedef enum logic [DFIGBWIDTH-1:0] {
      DFIRGB_16TO32 = 'd9,
      DFIRGB_8TO32  = 'd8,
      DFIRGB_8TO16  = 'd7,
      DFIRGB_8TO8   = 'd6,
      DFIRGB_4TO8   = 'd5,
      DFIRGB_4TO4   = 'd4,
      DFIRGB_2TO8   = 'd3,
      DFIRGB_2TO4   = 'd2,
      DFIRGB_2TO2   = 'd1,
      DFIRGB_1TO1   = 'd0
   } drgb_t;

   function automatic drgb_t cast_drgb_t(logic [DFIGBWIDTH-1:0] bits);
      case(bits)
        'd9    : cast_drgb_t = DFIRGB_16TO32;
        'd8    : cast_drgb_t = DFIRGB_8TO32;
        'd7    : cast_drgb_t = DFIRGB_8TO16;
        'd6    : cast_drgb_t = DFIRGB_8TO8;
        'd5    : cast_drgb_t = DFIRGB_4TO8;
        'd4    : cast_drgb_t = DFIRGB_4TO4;
        'd3    : cast_drgb_t = DFIRGB_2TO8;
        'd2    : cast_drgb_t = DFIRGB_2TO4;
        'd1    : cast_drgb_t = DFIRGB_2TO2;
        'd0    : cast_drgb_t = DFIRGB_1TO1;
        default: cast_drgb_t = DFIRGB_1TO1;
      endcase
      return cast_drgb_t;
   endfunction : cast_drgb_t

   parameter DEC_CK2WCKRWIDTH = 3;
   parameter CK2WCKRWIDTH = 2 ;
   //Datapath WCK2CK Ratio
   typedef enum logic [CK2WCKRWIDTH-1:0] {
      CK2WCK_1TO1 = 'd0,
      CK2WCK_1TO2 = 'd1,
      CK2WCK_1TO4 = 'd2
   } ck2wck_ratio_t;

   function automatic ck2wck_ratio_t cast_ck2wck_ratio_t(logic [CK2WCKRWIDTH-1:0] bits);
      case(bits)
        'd0     : cast_ck2wck_ratio_t = CK2WCK_1TO1;
        'd1     : cast_ck2wck_ratio_t = CK2WCK_1TO2;
        'd2     : cast_ck2wck_ratio_t = CK2WCK_1TO4;
        default : cast_ck2wck_ratio_t = CK2WCK_1TO1;
      endcase
      return cast_ck2wck_ratio_t;
   endfunction : cast_ck2wck_ratio_t

   parameter DGBWIDTH = 3;
   parameter DEC_DGBWIDTH = 8;

   // Datapath GearBox
   typedef enum logic [DGBWIDTH-1:0] {
      DGB_8TO1_HF = 'd7,  // High frequency 8TO1 mode
      DGB_8TO1_LF = 'd6,  // Low (iRDQS + DIV) frequency 8TO1 mode
      DGB_4TO1_IR = 'd5,  // High (iRDQS) frequency 4TO1 mode
      DGB_4TO1_HF = 'd4,  // High frequency 4TO1 mode
      DGB_4TO1_LF = 'd3,  // Low (iRDQS + DIV) frequency 4TO1 mode
      DGB_2TO1_IR = 'd2,  // High (iRDQS) frequency 2TO1 mode
      DGB_2TO1_HF = 'd1,  // High frequency 2TO1 mode
      DGB_1TO1_HF = 'd0   // High frequency 1TO1 mode
   } dgb_t;

   function automatic dgb_t cast_dgb_t(logic [DGBWIDTH-1:0] bits);
      case(bits)
        'd7     : cast_dgb_t = DGB_8TO1_HF;
        'd6     : cast_dgb_t = DGB_8TO1_LF;
        'd5     : cast_dgb_t = DGB_4TO1_IR;
        'd4     : cast_dgb_t = DGB_4TO1_HF;
        'd3     : cast_dgb_t = DGB_4TO1_LF;
        'd2     : cast_dgb_t = DGB_2TO1_IR;
        'd1     : cast_dgb_t = DGB_2TO1_HF;
        'd0     : cast_dgb_t = DGB_1TO1_HF;
        default : cast_dgb_t = DGB_1TO1_HF;
      endcase
      return cast_dgb_t;
   endfunction : cast_dgb_t

   parameter FGBWIDTH = 4;
   parameter DEC_FGBWIDTH = 11;

   // FIFO GearBox
   typedef enum logic [FGBWIDTH-1:0] {
      FGB_8TO16 = 'd10,
      FGB_8TO8  = 'd9,
      FGB_4TO8  = 'd8,
      FGB_4TO4  = 'd7,
      FGB_2TO8  = 'd6,
      FGB_2TO4  = 'd5,
      FGB_2TO2  = 'd4,
      FGB_1TO8  = 'd3,
      FGB_1TO4  = 'd2,
      FGB_1TO2  = 'd1,
      FGB_1TO1  = 'd0
   } fgb_t;

   function automatic fgb_t cast_fgb_t(logic [FGBWIDTH-1:0] bits);
      case(bits)
        'd10    : cast_fgb_t = FGB_8TO16;
        'd9     : cast_fgb_t = FGB_8TO8;
        'd8     : cast_fgb_t = FGB_4TO8;
        'd7     : cast_fgb_t = FGB_4TO4;
        'd6     : cast_fgb_t = FGB_2TO8;
        'd5     : cast_fgb_t = FGB_2TO4;
        'd4     : cast_fgb_t = FGB_2TO2;
        'd3     : cast_fgb_t = FGB_1TO8;
        'd2     : cast_fgb_t = FGB_1TO4;
        'd1     : cast_fgb_t = FGB_1TO2;
        'd0     : cast_fgb_t = FGB_1TO1;
        default : cast_fgb_t = FGB_1TO1;
      endcase
      return cast_fgb_t;
   endfunction : cast_fgb_t

   parameter WGBWIDTH = 4;
   parameter DEC_WGBWIDTH = 11;

   // Write GearBox
   typedef enum logic [WGBWIDTH-1:0] {
      WGB_16TO8 = 'd10,
      WGB_8TO8  = 'd9,
      WGB_8TO4  = 'd8,
      WGB_4TO4  = 'd7,
      WGB_8TO2  = 'd6,
      WGB_4TO2  = 'd5,
      WGB_2TO2  = 'd4,
      WGB_8TO1  = 'd3,
      WGB_4TO1  = 'd2,
      WGB_2TO1  = 'd1,
      WGB_1TO1  = 'd0
   } wgb_t;

   function automatic wgb_t cast_wgb_t(logic [WGBWIDTH-1:0] bits);
      case(bits)
        'd10    : cast_wgb_t = WGB_16TO8;
        'd9     : cast_wgb_t = WGB_8TO8;
        'd8     : cast_wgb_t = WGB_8TO4;
        'd7     : cast_wgb_t = WGB_4TO4;
        'd6     : cast_wgb_t = WGB_8TO2;
        'd5     : cast_wgb_t = WGB_4TO2;
        'd4     : cast_wgb_t = WGB_2TO2;
        'd3     : cast_wgb_t = WGB_8TO1;
        'd2     : cast_wgb_t = WGB_4TO1;
        'd1     : cast_wgb_t = WGB_2TO1;
        'd0     : cast_wgb_t = WGB_1TO1;
        default : cast_wgb_t = WGB_1TO1;
      endcase
      return cast_wgb_t;
   endfunction : cast_wgb_t

   parameter GBWIDTH = 3;

   typedef enum logic [1:0] {
      INT_RDQS = 2'b10,
      WCK_LB   = 2'b01,
      EXT_RDQS = 2'b00
   } rdqs_t;

   // ------------------------------------------------------------------------
   // Message Definitions
   // ------------------------------------------------------------------------

`ifdef MSG_ERROR
   `define ERROR(msg) \
      do begin $write("ERROR:"); $display(msg); end while (0)
`else
   `define MSG(msg) \
      do begin end while (0)
`endif

`ifdef MSG_WARN
   `define WARN(msg) \
      do begin $write("WARN:"); $display(msg); end while (0)
`else
   `define MSG(msg) \
      do begin end while (0)
`endif

`ifdef MSG_INFO
   `define INFO(msg) \
      do begin $write("INFO:"); $display(msg); end while (0)
`else
   `define MSG(msg) \
      do begin end while (0)
`endif

`ifdef MSG_NOTE
   `define NOTE(msg) \
      do begin $write("[%0t] %s:%d: ",$time, `__FILE__, `__LINE__); $display(msg); end while (0)
`else
   `define NOTE(msg) \
      do begin end while (0)
`endif

endpackage : ddr_global_pkg
`endif // DDR_GLOBAL_PKG
