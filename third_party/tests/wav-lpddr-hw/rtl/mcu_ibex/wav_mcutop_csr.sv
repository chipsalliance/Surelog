


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

`include "wav_mcutop_csr_defs.vh"



module wav_mcutop_csr #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic                i_write,
   input   logic                i_read,
   input   logic [AWIDTH-1:0]   i_addr,
   input   logic [DWIDTH-1:0]   i_wdata,
   output  logic [DWIDTH-1:0]   o_rdata,
   output  logic                o_error,
   output  logic                o_ready,
   output  logic [`WAV_MCUTOP_RSVD_RANGE] o_mcutop_rsvd,
   output  logic [`WAV_MCUTOP_CFG_RANGE] o_mcutop_cfg,
   input   logic [`WAV_MCUTOP_STA_RANGE] i_mcutop_sta
);

   typedef enum logic [2:0] {
      DECODE_WAV_MCUTOP_RSVD,
      DECODE_WAV_MCUTOP_CFG,
      DECODE_WAV_MCUTOP_STA,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `WAV_MCUTOP_RSVD_ADR : decode = DECODE_WAV_MCUTOP_RSVD;
         `WAV_MCUTOP_CFG_ADR : decode = DECODE_WAV_MCUTOP_CFG;
         `WAV_MCUTOP_STA_ADR : decode = DECODE_WAV_MCUTOP_STA;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] mcutop_rsvd_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcutop_rsvd_q <= `WAV_MCUTOP_RSVD_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUTOP_RSVD)
               mcutop_rsvd_q <= i_wdata;

   assign o_mcutop_rsvd = mcutop_rsvd_q & `WAV_MCUTOP_RSVD_MSK;

   logic [31:0] mcutop_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcutop_cfg_q <= `WAV_MCUTOP_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUTOP_CFG)
               mcutop_cfg_q <= i_wdata;

   assign o_mcutop_cfg = mcutop_cfg_q & `WAV_MCUTOP_CFG_MSK;

   logic [31:0] mcutop_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcutop_sta_q <= `WAV_MCUTOP_STA_POR;
      else
         mcutop_sta_q <= i_mcutop_sta;

   always_comb
      if (i_read)
         case (decode)
            DECODE_WAV_MCUTOP_RSVD : o_rdata = o_mcutop_rsvd;
            DECODE_WAV_MCUTOP_CFG : o_rdata = o_mcutop_cfg;
            DECODE_WAV_MCUTOP_STA : o_rdata = mcutop_sta_q;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
