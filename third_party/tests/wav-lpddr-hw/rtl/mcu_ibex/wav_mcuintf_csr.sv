


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

`include "wav_mcuintf_csr_defs.vh"



module wav_mcuintf_csr #(
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
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_DATA_RANGE] o_mcuintf_host2mcu_msg_data,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_ID_RANGE] o_mcuintf_host2mcu_msg_id,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_REQ_RANGE] o_mcuintf_host2mcu_msg_req,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_ACK_RANGE] o_mcuintf_host2mcu_msg_ack,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_DATA_RANGE] o_mcuintf_mcu2host_msg_data,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_ID_RANGE] o_mcuintf_mcu2host_msg_id,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_REQ_RANGE] o_mcuintf_mcu2host_msg_req,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_ACK_RANGE] o_mcuintf_mcu2host_msg_ack
);

   typedef enum logic [3:0] {
      DECODE_WAV_MCUINTF_HOST2MCU_MSG_DATA,
      DECODE_WAV_MCUINTF_HOST2MCU_MSG_ID,
      DECODE_WAV_MCUINTF_HOST2MCU_MSG_REQ,
      DECODE_WAV_MCUINTF_HOST2MCU_MSG_ACK,
      DECODE_WAV_MCUINTF_MCU2HOST_MSG_DATA,
      DECODE_WAV_MCUINTF_MCU2HOST_MSG_ID,
      DECODE_WAV_MCUINTF_MCU2HOST_MSG_REQ,
      DECODE_WAV_MCUINTF_MCU2HOST_MSG_ACK,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `WAV_MCUINTF_HOST2MCU_MSG_DATA_ADR : decode = DECODE_WAV_MCUINTF_HOST2MCU_MSG_DATA;
         `WAV_MCUINTF_HOST2MCU_MSG_ID_ADR : decode = DECODE_WAV_MCUINTF_HOST2MCU_MSG_ID;
         `WAV_MCUINTF_HOST2MCU_MSG_REQ_ADR : decode = DECODE_WAV_MCUINTF_HOST2MCU_MSG_REQ;
         `WAV_MCUINTF_HOST2MCU_MSG_ACK_ADR : decode = DECODE_WAV_MCUINTF_HOST2MCU_MSG_ACK;
         `WAV_MCUINTF_MCU2HOST_MSG_DATA_ADR : decode = DECODE_WAV_MCUINTF_MCU2HOST_MSG_DATA;
         `WAV_MCUINTF_MCU2HOST_MSG_ID_ADR : decode = DECODE_WAV_MCUINTF_MCU2HOST_MSG_ID;
         `WAV_MCUINTF_MCU2HOST_MSG_REQ_ADR : decode = DECODE_WAV_MCUINTF_MCU2HOST_MSG_REQ;
         `WAV_MCUINTF_MCU2HOST_MSG_ACK_ADR : decode = DECODE_WAV_MCUINTF_MCU2HOST_MSG_ACK;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] mcuintf_host2mcu_msg_data_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_host2mcu_msg_data_q <= `WAV_MCUINTF_HOST2MCU_MSG_DATA_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_HOST2MCU_MSG_DATA)
               mcuintf_host2mcu_msg_data_q <= i_wdata;

   assign o_mcuintf_host2mcu_msg_data = mcuintf_host2mcu_msg_data_q & `WAV_MCUINTF_HOST2MCU_MSG_DATA_MSK;

   logic [31:0] mcuintf_host2mcu_msg_id_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_host2mcu_msg_id_q <= `WAV_MCUINTF_HOST2MCU_MSG_ID_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_HOST2MCU_MSG_ID)
               mcuintf_host2mcu_msg_id_q <= i_wdata;

   assign o_mcuintf_host2mcu_msg_id = mcuintf_host2mcu_msg_id_q & `WAV_MCUINTF_HOST2MCU_MSG_ID_MSK;

   logic [31:0] mcuintf_host2mcu_msg_req_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_host2mcu_msg_req_q <= `WAV_MCUINTF_HOST2MCU_MSG_REQ_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_HOST2MCU_MSG_REQ)
               mcuintf_host2mcu_msg_req_q <= mcuintf_host2mcu_msg_req_q ^ i_wdata;

   assign o_mcuintf_host2mcu_msg_req = mcuintf_host2mcu_msg_req_q & `WAV_MCUINTF_HOST2MCU_MSG_REQ_MSK;

   logic [31:0] mcuintf_host2mcu_msg_ack_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_host2mcu_msg_ack_q <= `WAV_MCUINTF_HOST2MCU_MSG_ACK_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_HOST2MCU_MSG_ACK)
               mcuintf_host2mcu_msg_ack_q <= mcuintf_host2mcu_msg_ack_q ^ i_wdata;

   assign o_mcuintf_host2mcu_msg_ack = mcuintf_host2mcu_msg_ack_q & `WAV_MCUINTF_HOST2MCU_MSG_ACK_MSK;

   logic [31:0] mcuintf_mcu2host_msg_data_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_mcu2host_msg_data_q <= `WAV_MCUINTF_MCU2HOST_MSG_DATA_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_MCU2HOST_MSG_DATA)
               mcuintf_mcu2host_msg_data_q <= i_wdata;

   assign o_mcuintf_mcu2host_msg_data = mcuintf_mcu2host_msg_data_q & `WAV_MCUINTF_MCU2HOST_MSG_DATA_MSK;

   logic [31:0] mcuintf_mcu2host_msg_id_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_mcu2host_msg_id_q <= `WAV_MCUINTF_MCU2HOST_MSG_ID_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_MCU2HOST_MSG_ID)
               mcuintf_mcu2host_msg_id_q <= i_wdata;

   assign o_mcuintf_mcu2host_msg_id = mcuintf_mcu2host_msg_id_q & `WAV_MCUINTF_MCU2HOST_MSG_ID_MSK;

   logic [31:0] mcuintf_mcu2host_msg_req_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_mcu2host_msg_req_q <= `WAV_MCUINTF_MCU2HOST_MSG_REQ_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_MCU2HOST_MSG_REQ)
               mcuintf_mcu2host_msg_req_q <= mcuintf_mcu2host_msg_req_q ^ i_wdata;

   assign o_mcuintf_mcu2host_msg_req = mcuintf_mcu2host_msg_req_q & `WAV_MCUINTF_MCU2HOST_MSG_REQ_MSK;

   logic [31:0] mcuintf_mcu2host_msg_ack_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         mcuintf_mcu2host_msg_ack_q <= `WAV_MCUINTF_MCU2HOST_MSG_ACK_POR;
      else
         if (i_write)
            if (decode == DECODE_WAV_MCUINTF_MCU2HOST_MSG_ACK)
               mcuintf_mcu2host_msg_ack_q <= mcuintf_mcu2host_msg_ack_q ^ i_wdata;

   assign o_mcuintf_mcu2host_msg_ack = mcuintf_mcu2host_msg_ack_q & `WAV_MCUINTF_MCU2HOST_MSG_ACK_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_WAV_MCUINTF_HOST2MCU_MSG_DATA : o_rdata = o_mcuintf_host2mcu_msg_data;
            DECODE_WAV_MCUINTF_HOST2MCU_MSG_ID : o_rdata = o_mcuintf_host2mcu_msg_id;
            DECODE_WAV_MCUINTF_HOST2MCU_MSG_REQ : o_rdata = o_mcuintf_host2mcu_msg_req;
            DECODE_WAV_MCUINTF_HOST2MCU_MSG_ACK : o_rdata = o_mcuintf_host2mcu_msg_ack;
            DECODE_WAV_MCUINTF_MCU2HOST_MSG_DATA : o_rdata = o_mcuintf_mcu2host_msg_data;
            DECODE_WAV_MCUINTF_MCU2HOST_MSG_ID : o_rdata = o_mcuintf_mcu2host_msg_id;
            DECODE_WAV_MCUINTF_MCU2HOST_MSG_REQ : o_rdata = o_mcuintf_mcu2host_msg_req;
            DECODE_WAV_MCUINTF_MCU2HOST_MSG_ACK : o_rdata = o_mcuintf_mcu2host_msg_ack;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
