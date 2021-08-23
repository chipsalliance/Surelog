


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



module wav_mcuintf_ahb_csr #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
) (

   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic                i_hsel,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   input   logic                i_hreadyin,
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_DATA_RANGE] o_mcuintf_host2mcu_msg_data,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_ID_RANGE] o_mcuintf_host2mcu_msg_id,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_REQ_RANGE] o_mcuintf_host2mcu_msg_req,
   output  logic [`WAV_MCUINTF_HOST2MCU_MSG_ACK_RANGE] o_mcuintf_host2mcu_msg_ack,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_DATA_RANGE] o_mcuintf_mcu2host_msg_data,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_ID_RANGE] o_mcuintf_mcu2host_msg_id,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_REQ_RANGE] o_mcuintf_mcu2host_msg_req,
   output  logic [`WAV_MCUINTF_MCU2HOST_MSG_ACK_RANGE] o_mcuintf_mcu2host_msg_ack
);

   logic                slv_write;
   logic                slv_read;
   logic                slv_error;
   logic [AWIDTH-1:0]   slv_addr;
   logic [DWIDTH-1:0]   slv_wdata;
   logic [DWIDTH-1:0]   slv_rdata;
   logic                slv_ready;

   wav_ahb_slave #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) ahb_slave (
      .i_hclk     (i_hclk),
      .i_hreset   (i_hreset),
      .i_haddr    (i_haddr),
      .i_hwrite   (i_hwrite),
      .i_hsel     (i_hsel),
      .i_hwdata   (i_hwdata),
      .i_htrans   (i_htrans),
      .i_hsize    (i_hsize),
      .i_hburst   (i_hburst),
      .i_hreadyin (i_hreadyin),
      .o_hready   (o_hready),
      .o_hrdata   (o_hrdata),
      .o_hresp    (o_hresp),
      .o_write    (slv_write),
      .o_read     (slv_read),
      .o_wdata    (slv_wdata),
      .o_addr     (slv_addr),
      .i_rdata    (slv_rdata),
      .i_error    (slv_error),
      .i_ready    (slv_ready)
   );

   wav_mcuintf_csr #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH)
   ) mcuintf_csr (
      .i_hclk   (i_hclk),
      .i_hreset (i_hreset),
      .i_write  (slv_write),
      .i_read   (slv_read),
      .i_wdata  (slv_wdata),
      .i_addr   (slv_addr),
      .o_rdata  (slv_rdata),
      .o_error  (slv_error),
      .o_ready  (slv_ready),
      .o_mcuintf_host2mcu_msg_data (o_mcuintf_host2mcu_msg_data),
      .o_mcuintf_host2mcu_msg_id (o_mcuintf_host2mcu_msg_id),
      .o_mcuintf_host2mcu_msg_req (o_mcuintf_host2mcu_msg_req),
      .o_mcuintf_host2mcu_msg_ack (o_mcuintf_host2mcu_msg_ack),
      .o_mcuintf_mcu2host_msg_data (o_mcuintf_mcu2host_msg_data),
      .o_mcuintf_mcu2host_msg_id (o_mcuintf_mcu2host_msg_id),
      .o_mcuintf_mcu2host_msg_req (o_mcuintf_mcu2host_msg_req),
      .o_mcuintf_mcu2host_msg_ack (o_mcuintf_mcu2host_msg_ack)
   );

endmodule
