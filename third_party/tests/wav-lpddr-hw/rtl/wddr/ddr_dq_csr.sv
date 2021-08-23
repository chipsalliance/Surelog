
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

`include "ddr_global_define.vh"
`include "ddr_project_define.vh"
`include "ddr_dq_csr_defs.vh"

import ddr_global_pkg::*;

module ddr_dq_csr #(
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
   output  logic [`DDR_DQ_TOP_CFG_RANGE] o_dq_top_cfg,
   input   logic [`DDR_DQ_TOP_STA_RANGE] i_dq_top_sta,
   input   logic [`DDR_DQ_DQ_RX_BSCAN_STA_RANGE] i_dq_dq_rx_bscan_sta,
   output  logic [`DDR_DQ_DQ_RX_M0_CFG_RANGE] o_dq_dq_rx_m0_cfg,
   output  logic [`DDR_DQ_DQ_RX_M1_CFG_RANGE] o_dq_dq_rx_m1_cfg,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_0_RANGE] o_dq_dq_rx_io_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_1_RANGE] o_dq_dq_rx_io_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_2_RANGE] o_dq_dq_rx_io_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_3_RANGE] o_dq_dq_rx_io_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_4_RANGE] o_dq_dq_rx_io_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_5_RANGE] o_dq_dq_rx_io_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_6_RANGE] o_dq_dq_rx_io_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_7_RANGE] o_dq_dq_rx_io_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R0_CFG_8_RANGE] o_dq_dq_rx_io_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_0_RANGE] o_dq_dq_rx_io_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_1_RANGE] o_dq_dq_rx_io_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_2_RANGE] o_dq_dq_rx_io_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_3_RANGE] o_dq_dq_rx_io_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_4_RANGE] o_dq_dq_rx_io_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_5_RANGE] o_dq_dq_rx_io_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_6_RANGE] o_dq_dq_rx_io_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_7_RANGE] o_dq_dq_rx_io_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_IO_M0_R1_CFG_8_RANGE] o_dq_dq_rx_io_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_0_RANGE] o_dq_dq_rx_io_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_1_RANGE] o_dq_dq_rx_io_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_2_RANGE] o_dq_dq_rx_io_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_3_RANGE] o_dq_dq_rx_io_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_4_RANGE] o_dq_dq_rx_io_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_5_RANGE] o_dq_dq_rx_io_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_6_RANGE] o_dq_dq_rx_io_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_7_RANGE] o_dq_dq_rx_io_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R0_CFG_8_RANGE] o_dq_dq_rx_io_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_0_RANGE] o_dq_dq_rx_io_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_1_RANGE] o_dq_dq_rx_io_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_2_RANGE] o_dq_dq_rx_io_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_3_RANGE] o_dq_dq_rx_io_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_4_RANGE] o_dq_dq_rx_io_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_5_RANGE] o_dq_dq_rx_io_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_6_RANGE] o_dq_dq_rx_io_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_7_RANGE] o_dq_dq_rx_io_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_IO_M1_R1_CFG_8_RANGE] o_dq_dq_rx_io_m1_r1_cfg_8,
   input   logic [`DDR_DQ_DQ_RX_IO_STA_RANGE] i_dq_dq_rx_io_sta,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_0_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_1_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_2_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_3_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_4_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_5_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_6_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_7_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R0_CFG_8_RANGE] o_dq_dq_rx_sa_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_0_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_1_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_2_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_3_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_4_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_5_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_6_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_7_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_M0_R1_CFG_8_RANGE] o_dq_dq_rx_sa_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_0_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_1_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_2_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_3_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_4_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_5_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_6_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_7_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R0_CFG_8_RANGE] o_dq_dq_rx_sa_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_0_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_1_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_2_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_3_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_4_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_5_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_6_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_7_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_M1_R1_CFG_8_RANGE] o_dq_dq_rx_sa_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8_RANGE] o_dq_dq_rx_sa_dly_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8_RANGE] o_dq_dq_rx_sa_dly_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8_RANGE] o_dq_dq_rx_sa_dly_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8_RANGE] o_dq_dq_rx_sa_dly_m1_r1_cfg_8,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_0_RANGE] i_dq_dq_rx_sa_sta_0,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_1_RANGE] i_dq_dq_rx_sa_sta_1,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_2_RANGE] i_dq_dq_rx_sa_sta_2,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_3_RANGE] i_dq_dq_rx_sa_sta_3,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_4_RANGE] i_dq_dq_rx_sa_sta_4,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_5_RANGE] i_dq_dq_rx_sa_sta_5,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_6_RANGE] i_dq_dq_rx_sa_sta_6,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_7_RANGE] i_dq_dq_rx_sa_sta_7,
   input   logic [`DDR_DQ_DQ_RX_SA_STA_8_RANGE] i_dq_dq_rx_sa_sta_8,
   output  logic [`DDR_DQ_DQ_TX_BSCAN_CFG_RANGE] o_dq_dq_tx_bscan_cfg,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8_RANGE] o_dq_dq_tx_egress_ana_m0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8_RANGE] o_dq_dq_tx_egress_ana_m1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8_RANGE] o_dq_dq_tx_egress_dig_m0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8_RANGE] o_dq_dq_tx_egress_dig_m1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG_RANGE] o_dq_dq_tx_odr_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG_RANGE] o_dq_dq_tx_odr_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG_RANGE] o_dq_dq_tx_odr_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG_RANGE] o_dq_dq_tx_odr_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG_RANGE] o_dq_dq_tx_qdr_pi_0_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG_RANGE] o_dq_dq_tx_qdr_pi_0_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG_RANGE] o_dq_dq_tx_qdr_pi_0_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG_RANGE] o_dq_dq_tx_qdr_pi_0_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG_RANGE] o_dq_dq_tx_qdr_pi_1_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG_RANGE] o_dq_dq_tx_qdr_pi_1_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG_RANGE] o_dq_dq_tx_qdr_pi_1_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG_RANGE] o_dq_dq_tx_qdr_pi_1_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG_RANGE] o_dq_dq_tx_ddr_pi_0_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG_RANGE] o_dq_dq_tx_ddr_pi_0_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG_RANGE] o_dq_dq_tx_ddr_pi_0_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG_RANGE] o_dq_dq_tx_ddr_pi_0_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG_RANGE] o_dq_dq_tx_ddr_pi_1_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG_RANGE] o_dq_dq_tx_ddr_pi_1_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG_RANGE] o_dq_dq_tx_ddr_pi_1_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG_RANGE] o_dq_dq_tx_ddr_pi_1_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG_RANGE] o_dq_dq_tx_pi_rt_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG_RANGE] o_dq_dq_tx_pi_rt_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG_RANGE] o_dq_dq_tx_pi_rt_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG_RANGE] o_dq_dq_tx_pi_rt_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_RT_M0_R0_CFG_RANGE] o_dq_dq_tx_rt_m0_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_RT_M0_R1_CFG_RANGE] o_dq_dq_tx_rt_m0_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_RT_M1_R0_CFG_RANGE] o_dq_dq_tx_rt_m1_r0_cfg,
   output  logic [`DDR_DQ_DQ_TX_RT_M1_R1_CFG_RANGE] o_dq_dq_tx_rt_m1_r1_cfg,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_RANGE] o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8_RANGE] o_dq_dq_tx_ddr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8_RANGE] o_dq_dq_tx_ddr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8_RANGE] o_dq_dq_tx_ddr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8_RANGE] o_dq_dq_tx_ddr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8_RANGE] o_dq_dq_tx_qdr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8_RANGE] o_dq_dq_tx_qdr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8_RANGE] o_dq_dq_tx_qdr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8_RANGE] o_dq_dq_tx_qdr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8_RANGE] o_dq_dq_tx_lpde_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8_RANGE] o_dq_dq_tx_lpde_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8_RANGE] o_dq_dq_tx_lpde_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8_RANGE] o_dq_dq_tx_lpde_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_0_RANGE] o_dq_dq_tx_io_m0_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_1_RANGE] o_dq_dq_tx_io_m0_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_2_RANGE] o_dq_dq_tx_io_m0_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_3_RANGE] o_dq_dq_tx_io_m0_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_4_RANGE] o_dq_dq_tx_io_m0_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_5_RANGE] o_dq_dq_tx_io_m0_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_6_RANGE] o_dq_dq_tx_io_m0_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_7_RANGE] o_dq_dq_tx_io_m0_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_IO_M0_CFG_8_RANGE] o_dq_dq_tx_io_m0_cfg_8,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_0_RANGE] o_dq_dq_tx_io_m1_cfg_0,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_1_RANGE] o_dq_dq_tx_io_m1_cfg_1,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_2_RANGE] o_dq_dq_tx_io_m1_cfg_2,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_3_RANGE] o_dq_dq_tx_io_m1_cfg_3,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_4_RANGE] o_dq_dq_tx_io_m1_cfg_4,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_5_RANGE] o_dq_dq_tx_io_m1_cfg_5,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_6_RANGE] o_dq_dq_tx_io_m1_cfg_6,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_7_RANGE] o_dq_dq_tx_io_m1_cfg_7,
   output  logic [`DDR_DQ_DQ_TX_IO_M1_CFG_8_RANGE] o_dq_dq_tx_io_m1_cfg_8,
   output  logic [`DDR_DQ_DQS_RX_M0_CFG_RANGE] o_dq_dqs_rx_m0_cfg,
   output  logic [`DDR_DQ_DQS_RX_M1_CFG_RANGE] o_dq_dqs_rx_m1_cfg,
   input   logic [`DDR_DQ_DQS_RX_BSCAN_STA_RANGE] i_dq_dqs_rx_bscan_sta,
   output  logic [`DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG_RANGE] o_dq_dqs_rx_sdr_lpde_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG_RANGE] o_dq_dqs_rx_sdr_lpde_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG_RANGE] o_dq_dqs_rx_sdr_lpde_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG_RANGE] o_dq_dqs_rx_sdr_lpde_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG_RANGE] o_dq_dqs_rx_ren_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG_RANGE] o_dq_dqs_rx_ren_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG_RANGE] o_dq_dqs_rx_ren_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG_RANGE] o_dq_dqs_rx_ren_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG_RANGE] o_dq_dqs_rx_rcs_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG_RANGE] o_dq_dqs_rx_rcs_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG_RANGE] o_dq_dqs_rx_rcs_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG_RANGE] o_dq_dqs_rx_rcs_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_0_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_0_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_0_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_0_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_1_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_1_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_1_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG_RANGE] o_dq_dqs_rx_rdqs_pi_1_m1_r1_cfg,
   input   logic [`DDR_DQ_DQS_RX_PI_STA_RANGE] i_dq_dqs_rx_pi_sta,
   output  logic [`DDR_DQ_DQS_RX_IO_M0_R0_CFG_0_RANGE] o_dq_dqs_rx_io_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_IO_M0_R0_CFG_1_RANGE] o_dq_dqs_rx_io_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_IO_M0_R1_CFG_0_RANGE] o_dq_dqs_rx_io_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_IO_M0_R1_CFG_1_RANGE] o_dq_dqs_rx_io_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_IO_M1_R0_CFG_0_RANGE] o_dq_dqs_rx_io_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_IO_M1_R0_CFG_1_RANGE] o_dq_dqs_rx_io_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_IO_M1_R1_CFG_0_RANGE] o_dq_dqs_rx_io_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_IO_M1_R1_CFG_1_RANGE] o_dq_dqs_rx_io_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG_RANGE] o_dq_dqs_rx_io_cmn_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG_RANGE] o_dq_dqs_rx_io_cmn_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG_RANGE] o_dq_dqs_rx_io_cmn_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG_RANGE] o_dq_dqs_rx_io_cmn_m1_r1_cfg,
   input   logic [`DDR_DQ_DQS_RX_IO_STA_RANGE] i_dq_dqs_rx_io_sta,
   output  logic [`DDR_DQ_DQS_RX_SA_M0_R0_CFG_0_RANGE] o_dq_dqs_rx_sa_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_SA_M0_R0_CFG_1_RANGE] o_dq_dqs_rx_sa_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_SA_M0_R1_CFG_0_RANGE] o_dq_dqs_rx_sa_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_SA_M0_R1_CFG_1_RANGE] o_dq_dqs_rx_sa_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_SA_M1_R0_CFG_0_RANGE] o_dq_dqs_rx_sa_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_SA_M1_R0_CFG_1_RANGE] o_dq_dqs_rx_sa_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_SA_M1_R1_CFG_0_RANGE] o_dq_dqs_rx_sa_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_RX_SA_M1_R1_CFG_1_RANGE] o_dq_dqs_rx_sa_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_RX_SA_CMN_CFG_RANGE] o_dq_dqs_rx_sa_cmn_cfg,
   output  logic [`DDR_DQ_DQS_TX_M0_CFG_RANGE] o_dq_dqs_tx_m0_cfg,
   output  logic [`DDR_DQ_DQS_TX_M1_CFG_RANGE] o_dq_dqs_tx_m1_cfg,
   output  logic [`DDR_DQ_DQS_TX_BSCAN_CTRL_CFG_RANGE] o_dq_dqs_tx_bscan_ctrl_cfg,
   output  logic [`DDR_DQ_DQS_TX_BSCAN_CFG_RANGE] o_dq_dqs_tx_bscan_cfg,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8_RANGE] o_dq_dqs_tx_egress_ana_m0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8_RANGE] o_dq_dqs_tx_egress_ana_m1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8_RANGE] o_dq_dqs_tx_egress_dig_m0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8_RANGE] o_dq_dqs_tx_egress_dig_m1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG_RANGE] o_dq_dqs_tx_odr_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG_RANGE] o_dq_dqs_tx_odr_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG_RANGE] o_dq_dqs_tx_odr_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG_RANGE] o_dq_dqs_tx_odr_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG_RANGE] o_dq_dqs_tx_qdr_pi_0_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG_RANGE] o_dq_dqs_tx_qdr_pi_0_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG_RANGE] o_dq_dqs_tx_qdr_pi_0_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG_RANGE] o_dq_dqs_tx_qdr_pi_0_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG_RANGE] o_dq_dqs_tx_qdr_pi_1_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG_RANGE] o_dq_dqs_tx_qdr_pi_1_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG_RANGE] o_dq_dqs_tx_qdr_pi_1_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG_RANGE] o_dq_dqs_tx_qdr_pi_1_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG_RANGE] o_dq_dqs_tx_ddr_pi_0_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG_RANGE] o_dq_dqs_tx_ddr_pi_0_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG_RANGE] o_dq_dqs_tx_ddr_pi_0_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG_RANGE] o_dq_dqs_tx_ddr_pi_0_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG_RANGE] o_dq_dqs_tx_ddr_pi_1_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG_RANGE] o_dq_dqs_tx_ddr_pi_1_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG_RANGE] o_dq_dqs_tx_ddr_pi_1_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG_RANGE] o_dq_dqs_tx_ddr_pi_1_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG_RANGE] o_dq_dqs_tx_pi_rt_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG_RANGE] o_dq_dqs_tx_pi_rt_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG_RANGE] o_dq_dqs_tx_pi_rt_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG_RANGE] o_dq_dqs_tx_pi_rt_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG_RANGE] o_dq_dqs_tx_sdr_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG_RANGE] o_dq_dqs_tx_sdr_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG_RANGE] o_dq_dqs_tx_sdr_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG_RANGE] o_dq_dqs_tx_sdr_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG_RANGE] o_dq_dqs_tx_dfi_pi_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG_RANGE] o_dq_dqs_tx_dfi_pi_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG_RANGE] o_dq_dqs_tx_dfi_pi_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG_RANGE] o_dq_dqs_tx_dfi_pi_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_RT_M0_R0_CFG_RANGE] o_dq_dqs_tx_rt_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_RT_M0_R1_CFG_RANGE] o_dq_dqs_tx_rt_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_RT_M1_R0_CFG_RANGE] o_dq_dqs_tx_rt_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_RT_M1_R1_CFG_RANGE] o_dq_dqs_tx_rt_m1_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_ddr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_ddr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_ddr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_ddr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_qdr_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_qdr_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_qdr_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_qdr_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8_RANGE] o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7,
   output  logic [`DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8_RANGE] o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0_RANGE] o_dq_dqs_tx_lpde_m0_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1_RANGE] o_dq_dqs_tx_lpde_m0_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0_RANGE] o_dq_dqs_tx_lpde_m0_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1_RANGE] o_dq_dqs_tx_lpde_m0_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0_RANGE] o_dq_dqs_tx_lpde_m1_r0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1_RANGE] o_dq_dqs_tx_lpde_m1_r0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0_RANGE] o_dq_dqs_tx_lpde_m1_r1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1_RANGE] o_dq_dqs_tx_lpde_m1_r1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_IO_M0_CFG_0_RANGE] o_dq_dqs_tx_io_m0_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_IO_M0_CFG_1_RANGE] o_dq_dqs_tx_io_m0_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_IO_M1_CFG_0_RANGE] o_dq_dqs_tx_io_m1_cfg_0,
   output  logic [`DDR_DQ_DQS_TX_IO_M1_CFG_1_RANGE] o_dq_dqs_tx_io_m1_cfg_1,
   output  logic [`DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG_RANGE] o_dq_dqs_tx_io_cmn_m0_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG_RANGE] o_dq_dqs_tx_io_cmn_m0_r1_cfg,
   output  logic [`DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG_RANGE] o_dq_dqs_tx_io_cmn_m1_r0_cfg,
   output  logic [`DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG_RANGE] o_dq_dqs_tx_io_cmn_m1_r1_cfg
);

   typedef enum logic [10:0] {
      DECODE_DDR_DQ_TOP_CFG,
      DECODE_DDR_DQ_TOP_STA,
      DECODE_DDR_DQ_DQ_RX_BSCAN_STA,
      DECODE_DDR_DQ_DQ_RX_M0_CFG,
      DECODE_DDR_DQ_DQ_RX_M1_CFG,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_IO_STA,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_RX_SA_STA_0,
      DECODE_DDR_DQ_DQ_RX_SA_STA_1,
      DECODE_DDR_DQ_DQ_RX_SA_STA_2,
      DECODE_DDR_DQ_DQ_RX_SA_STA_3,
      DECODE_DDR_DQ_DQ_RX_SA_STA_4,
      DECODE_DDR_DQ_DQ_RX_SA_STA_5,
      DECODE_DDR_DQ_DQ_RX_SA_STA_6,
      DECODE_DDR_DQ_DQ_RX_SA_STA_7,
      DECODE_DDR_DQ_DQ_RX_SA_STA_8,
      DECODE_DDR_DQ_DQ_TX_BSCAN_CFG,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_RT_M0_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_RT_M0_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_RT_M1_R0_CFG,
      DECODE_DDR_DQ_DQ_TX_RT_M1_R1_CFG,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_0,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_1,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_2,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_3,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_4,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_5,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_6,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_7,
      DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_8,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_0,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_1,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_2,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_3,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_4,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_5,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_6,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_7,
      DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_8,
      DECODE_DDR_DQ_DQS_RX_M0_CFG,
      DECODE_DDR_DQ_DQS_RX_M1_CFG,
      DECODE_DDR_DQ_DQS_RX_BSCAN_STA,
      DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_PI_STA,
      DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_RX_IO_STA,
      DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_RX_SA_CMN_CFG,
      DECODE_DDR_DQ_DQS_TX_M0_CFG,
      DECODE_DDR_DQ_DQS_TX_M1_CFG,
      DECODE_DDR_DQ_DQS_TX_BSCAN_CTRL_CFG,
      DECODE_DDR_DQ_DQS_TX_BSCAN_CFG,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_RT_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_RT_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_RT_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_RT_M1_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7,
      DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8,
      DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_0,
      DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_1,
      DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_0,
      DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_1,
      DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,
      DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,
      DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,
      DECODE_NOOP
   } DECODE_T;

   DECODE_T decode;

   assign o_ready = 1'b1;

   always_comb begin
      o_error = 1'b0;
      case (i_addr)
         `DDR_DQ_TOP_CFG_ADR : decode = DECODE_DDR_DQ_TOP_CFG;
         `DDR_DQ_TOP_STA_ADR : decode = DECODE_DDR_DQ_TOP_STA;
         `DDR_DQ_DQ_RX_BSCAN_STA_ADR : decode = DECODE_DDR_DQ_DQ_RX_BSCAN_STA;
         `DDR_DQ_DQ_RX_M0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_RX_M0_CFG;
         `DDR_DQ_DQ_RX_M1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_RX_M1_CFG;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_0;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_1;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_2;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_3;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_4;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_5;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_6;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_7;
         `DDR_DQ_DQ_RX_IO_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_8;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_0;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_1;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_2;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_3;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_4;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_5;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_6;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_7;
         `DDR_DQ_DQ_RX_IO_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_8;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_0;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_1;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_2;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_3;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_4;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_5;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_6;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_7;
         `DDR_DQ_DQ_RX_IO_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_8;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_0;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_1;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_2;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_3;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_4;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_5;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_6;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_7;
         `DDR_DQ_DQ_RX_IO_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_8;
         `DDR_DQ_DQ_RX_IO_STA_ADR : decode = DECODE_DDR_DQ_DQ_RX_IO_STA;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_0;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_1;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_2;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_3;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_4;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_5;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_6;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_7;
         `DDR_DQ_DQ_RX_SA_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_8;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_0;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_1;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_2;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_3;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_4;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_5;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_6;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_7;
         `DDR_DQ_DQ_RX_SA_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_8;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_0;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_1;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_2;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_3;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_4;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_5;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_6;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_7;
         `DDR_DQ_DQ_RX_SA_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_8;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_0;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_1;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_2;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_3;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_4;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_5;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_6;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_7;
         `DDR_DQ_DQ_RX_SA_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_8;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7;
         `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7;
         `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8;
         `DDR_DQ_DQ_RX_SA_STA_0_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_0;
         `DDR_DQ_DQ_RX_SA_STA_1_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_1;
         `DDR_DQ_DQ_RX_SA_STA_2_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_2;
         `DDR_DQ_DQ_RX_SA_STA_3_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_3;
         `DDR_DQ_DQ_RX_SA_STA_4_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_4;
         `DDR_DQ_DQ_RX_SA_STA_5_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_5;
         `DDR_DQ_DQ_RX_SA_STA_6_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_6;
         `DDR_DQ_DQ_RX_SA_STA_7_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_7;
         `DDR_DQ_DQ_RX_SA_STA_8_ADR : decode = DECODE_DDR_DQ_DQ_RX_SA_STA_8;
         `DDR_DQ_DQ_TX_BSCAN_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_BSCAN_CFG;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7;
         `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7;
         `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8;
         `DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG;
         `DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG;
         `DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG;
         `DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG;
         `DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG;
         `DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG;
         `DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG;
         `DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG;
         `DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG;
         `DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG;
         `DDR_DQ_DQ_TX_RT_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_RT_M0_R0_CFG;
         `DDR_DQ_DQ_TX_RT_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_RT_M0_R1_CFG;
         `DDR_DQ_DQ_TX_RT_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_RT_M1_R0_CFG;
         `DDR_DQ_DQ_TX_RT_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQ_TX_RT_M1_R1_CFG;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7;
         `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7;
         `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7;
         `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7;
         `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8;
         `DDR_DQ_DQ_TX_IO_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_0;
         `DDR_DQ_DQ_TX_IO_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_1;
         `DDR_DQ_DQ_TX_IO_M0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_2;
         `DDR_DQ_DQ_TX_IO_M0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_3;
         `DDR_DQ_DQ_TX_IO_M0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_4;
         `DDR_DQ_DQ_TX_IO_M0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_5;
         `DDR_DQ_DQ_TX_IO_M0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_6;
         `DDR_DQ_DQ_TX_IO_M0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_7;
         `DDR_DQ_DQ_TX_IO_M0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_8;
         `DDR_DQ_DQ_TX_IO_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_0;
         `DDR_DQ_DQ_TX_IO_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_1;
         `DDR_DQ_DQ_TX_IO_M1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_2;
         `DDR_DQ_DQ_TX_IO_M1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_3;
         `DDR_DQ_DQ_TX_IO_M1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_4;
         `DDR_DQ_DQ_TX_IO_M1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_5;
         `DDR_DQ_DQ_TX_IO_M1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_6;
         `DDR_DQ_DQ_TX_IO_M1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_7;
         `DDR_DQ_DQ_TX_IO_M1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_8;
         `DDR_DQ_DQS_RX_M0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_M0_CFG;
         `DDR_DQ_DQS_RX_M1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_M1_CFG;
         `DDR_DQ_DQS_RX_BSCAN_STA_ADR : decode = DECODE_DDR_DQ_DQS_RX_BSCAN_STA;
         `DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG;
         `DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG;
         `DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG;
         `DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG;
         `DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG;
         `DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG;
         `DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG;
         `DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG;
         `DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG;
         `DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG;
         `DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG;
         `DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG;
         `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG;
         `DDR_DQ_DQS_RX_PI_STA_ADR : decode = DECODE_DDR_DQ_DQS_RX_PI_STA;
         `DDR_DQ_DQS_RX_IO_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_0;
         `DDR_DQ_DQS_RX_IO_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_1;
         `DDR_DQ_DQS_RX_IO_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_0;
         `DDR_DQ_DQS_RX_IO_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_1;
         `DDR_DQ_DQS_RX_IO_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_0;
         `DDR_DQ_DQS_RX_IO_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_1;
         `DDR_DQ_DQS_RX_IO_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_0;
         `DDR_DQ_DQS_RX_IO_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_1;
         `DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG;
         `DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG;
         `DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG;
         `DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG;
         `DDR_DQ_DQS_RX_IO_STA_ADR : decode = DECODE_DDR_DQ_DQS_RX_IO_STA;
         `DDR_DQ_DQS_RX_SA_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_0;
         `DDR_DQ_DQS_RX_SA_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_1;
         `DDR_DQ_DQS_RX_SA_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_0;
         `DDR_DQ_DQS_RX_SA_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_1;
         `DDR_DQ_DQS_RX_SA_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_0;
         `DDR_DQ_DQS_RX_SA_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_1;
         `DDR_DQ_DQS_RX_SA_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_0;
         `DDR_DQ_DQS_RX_SA_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_1;
         `DDR_DQ_DQS_RX_SA_CMN_CFG_ADR : decode = DECODE_DDR_DQ_DQS_RX_SA_CMN_CFG;
         `DDR_DQ_DQS_TX_M0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_M0_CFG;
         `DDR_DQ_DQS_TX_M1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_M1_CFG;
         `DDR_DQ_DQS_TX_BSCAN_CTRL_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_BSCAN_CTRL_CFG;
         `DDR_DQ_DQS_TX_BSCAN_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_BSCAN_CFG;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7;
         `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7;
         `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8;
         `DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG;
         `DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG;
         `DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG;
         `DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG;
         `DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG;
         `DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG;
         `DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG;
         `DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG;
         `DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG;
         `DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG;
         `DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG;
         `DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG;
         `DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG;
         `DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG;
         `DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG;
         `DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG;
         `DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG;
         `DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG;
         `DDR_DQ_DQS_TX_RT_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_RT_M0_R0_CFG;
         `DDR_DQ_DQS_TX_RT_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_RT_M0_R1_CFG;
         `DDR_DQ_DQS_TX_RT_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_RT_M1_R0_CFG;
         `DDR_DQ_DQS_TX_RT_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_RT_M1_R1_CFG;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7;
         `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8_ADR : decode = DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8;
         `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0;
         `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1;
         `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0;
         `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1;
         `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0;
         `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1;
         `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0;
         `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1;
         `DDR_DQ_DQS_TX_IO_M0_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_0;
         `DDR_DQ_DQS_TX_IO_M0_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_1;
         `DDR_DQ_DQS_TX_IO_M1_CFG_0_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_0;
         `DDR_DQ_DQS_TX_IO_M1_CFG_1_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_1;
         `DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG;
         `DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG;
         `DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG;
         `DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG_ADR : decode = DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG;
         default : begin 
            decode = DECODE_NOOP;
            o_error = 1'b1;
         end
      endcase
   end

   logic [31:0] dq_top_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_top_cfg_q <= `DDR_DQ_TOP_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_TOP_CFG)
               dq_top_cfg_q <= i_wdata;

   assign o_dq_top_cfg = dq_top_cfg_q & `DDR_DQ_TOP_CFG_MSK;

   logic [31:0] dq_top_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_top_sta_q <= `DDR_DQ_TOP_STA_POR;
      else
         dq_top_sta_q <= i_dq_top_sta;

   logic [31:0] dq_dq_rx_bscan_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_bscan_sta_q <= `DDR_DQ_DQ_RX_BSCAN_STA_POR;
      else
         dq_dq_rx_bscan_sta_q <= i_dq_dq_rx_bscan_sta;

   logic [31:0] dq_dq_rx_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_m0_cfg_q <= `DDR_DQ_DQ_RX_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_M0_CFG)
               dq_dq_rx_m0_cfg_q <= i_wdata;

   assign o_dq_dq_rx_m0_cfg = dq_dq_rx_m0_cfg_q & `DDR_DQ_DQ_RX_M0_CFG_MSK;

   logic [31:0] dq_dq_rx_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_m1_cfg_q <= `DDR_DQ_DQ_RX_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_M1_CFG)
               dq_dq_rx_m1_cfg_q <= i_wdata;

   assign o_dq_dq_rx_m1_cfg = dq_dq_rx_m1_cfg_q & `DDR_DQ_DQ_RX_M1_CFG_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_0_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_0)
               dq_dq_rx_io_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_0 = dq_dq_rx_io_m0_r0_cfg_0_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_1_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_1)
               dq_dq_rx_io_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_1 = dq_dq_rx_io_m0_r0_cfg_1_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_2_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_2)
               dq_dq_rx_io_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_2 = dq_dq_rx_io_m0_r0_cfg_2_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_3_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_3)
               dq_dq_rx_io_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_3 = dq_dq_rx_io_m0_r0_cfg_3_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_4_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_4)
               dq_dq_rx_io_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_4 = dq_dq_rx_io_m0_r0_cfg_4_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_5_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_5)
               dq_dq_rx_io_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_5 = dq_dq_rx_io_m0_r0_cfg_5_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_6_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_6)
               dq_dq_rx_io_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_6 = dq_dq_rx_io_m0_r0_cfg_6_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_7_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_7)
               dq_dq_rx_io_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_7 = dq_dq_rx_io_m0_r0_cfg_7_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_io_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r0_cfg_8_q <= `DDR_DQ_DQ_RX_IO_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_8)
               dq_dq_rx_io_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r0_cfg_8 = dq_dq_rx_io_m0_r0_cfg_8_q & `DDR_DQ_DQ_RX_IO_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_0_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_0)
               dq_dq_rx_io_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_0 = dq_dq_rx_io_m0_r1_cfg_0_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_1_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_1)
               dq_dq_rx_io_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_1 = dq_dq_rx_io_m0_r1_cfg_1_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_2_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_2)
               dq_dq_rx_io_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_2 = dq_dq_rx_io_m0_r1_cfg_2_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_3_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_3)
               dq_dq_rx_io_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_3 = dq_dq_rx_io_m0_r1_cfg_3_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_4_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_4)
               dq_dq_rx_io_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_4 = dq_dq_rx_io_m0_r1_cfg_4_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_5_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_5)
               dq_dq_rx_io_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_5 = dq_dq_rx_io_m0_r1_cfg_5_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_6_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_6)
               dq_dq_rx_io_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_6 = dq_dq_rx_io_m0_r1_cfg_6_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_7_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_7)
               dq_dq_rx_io_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_7 = dq_dq_rx_io_m0_r1_cfg_7_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_io_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m0_r1_cfg_8_q <= `DDR_DQ_DQ_RX_IO_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_8)
               dq_dq_rx_io_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_io_m0_r1_cfg_8 = dq_dq_rx_io_m0_r1_cfg_8_q & `DDR_DQ_DQ_RX_IO_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_0_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_0)
               dq_dq_rx_io_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_0 = dq_dq_rx_io_m1_r0_cfg_0_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_1_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_1)
               dq_dq_rx_io_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_1 = dq_dq_rx_io_m1_r0_cfg_1_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_2_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_2)
               dq_dq_rx_io_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_2 = dq_dq_rx_io_m1_r0_cfg_2_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_3_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_3)
               dq_dq_rx_io_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_3 = dq_dq_rx_io_m1_r0_cfg_3_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_4_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_4)
               dq_dq_rx_io_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_4 = dq_dq_rx_io_m1_r0_cfg_4_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_5_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_5)
               dq_dq_rx_io_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_5 = dq_dq_rx_io_m1_r0_cfg_5_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_6_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_6)
               dq_dq_rx_io_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_6 = dq_dq_rx_io_m1_r0_cfg_6_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_7_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_7)
               dq_dq_rx_io_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_7 = dq_dq_rx_io_m1_r0_cfg_7_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_io_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r0_cfg_8_q <= `DDR_DQ_DQ_RX_IO_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_8)
               dq_dq_rx_io_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r0_cfg_8 = dq_dq_rx_io_m1_r0_cfg_8_q & `DDR_DQ_DQ_RX_IO_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_0_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_0)
               dq_dq_rx_io_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_0 = dq_dq_rx_io_m1_r1_cfg_0_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_1_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_1)
               dq_dq_rx_io_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_1 = dq_dq_rx_io_m1_r1_cfg_1_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_2_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_2)
               dq_dq_rx_io_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_2 = dq_dq_rx_io_m1_r1_cfg_2_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_3_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_3)
               dq_dq_rx_io_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_3 = dq_dq_rx_io_m1_r1_cfg_3_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_4_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_4)
               dq_dq_rx_io_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_4 = dq_dq_rx_io_m1_r1_cfg_4_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_5_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_5)
               dq_dq_rx_io_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_5 = dq_dq_rx_io_m1_r1_cfg_5_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_6_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_6)
               dq_dq_rx_io_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_6 = dq_dq_rx_io_m1_r1_cfg_6_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_7_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_7)
               dq_dq_rx_io_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_7 = dq_dq_rx_io_m1_r1_cfg_7_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_io_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_m1_r1_cfg_8_q <= `DDR_DQ_DQ_RX_IO_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_8)
               dq_dq_rx_io_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_io_m1_r1_cfg_8 = dq_dq_rx_io_m1_r1_cfg_8_q & `DDR_DQ_DQ_RX_IO_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_io_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_io_sta_q <= `DDR_DQ_DQ_RX_IO_STA_POR;
      else
         dq_dq_rx_io_sta_q <= i_dq_dq_rx_io_sta;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_0_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_0)
               dq_dq_rx_sa_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_0 = dq_dq_rx_sa_m0_r0_cfg_0_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_1_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_1)
               dq_dq_rx_sa_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_1 = dq_dq_rx_sa_m0_r0_cfg_1_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_2_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_2)
               dq_dq_rx_sa_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_2 = dq_dq_rx_sa_m0_r0_cfg_2_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_3_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_3)
               dq_dq_rx_sa_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_3 = dq_dq_rx_sa_m0_r0_cfg_3_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_4_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_4)
               dq_dq_rx_sa_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_4 = dq_dq_rx_sa_m0_r0_cfg_4_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_5_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_5)
               dq_dq_rx_sa_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_5 = dq_dq_rx_sa_m0_r0_cfg_5_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_6_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_6)
               dq_dq_rx_sa_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_6 = dq_dq_rx_sa_m0_r0_cfg_6_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_7_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_7)
               dq_dq_rx_sa_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_7 = dq_dq_rx_sa_m0_r0_cfg_7_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r0_cfg_8_q <= `DDR_DQ_DQ_RX_SA_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_8)
               dq_dq_rx_sa_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r0_cfg_8 = dq_dq_rx_sa_m0_r0_cfg_8_q & `DDR_DQ_DQ_RX_SA_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_0_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_0)
               dq_dq_rx_sa_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_0 = dq_dq_rx_sa_m0_r1_cfg_0_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_1_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_1)
               dq_dq_rx_sa_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_1 = dq_dq_rx_sa_m0_r1_cfg_1_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_2_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_2)
               dq_dq_rx_sa_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_2 = dq_dq_rx_sa_m0_r1_cfg_2_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_3_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_3)
               dq_dq_rx_sa_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_3 = dq_dq_rx_sa_m0_r1_cfg_3_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_4_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_4)
               dq_dq_rx_sa_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_4 = dq_dq_rx_sa_m0_r1_cfg_4_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_5_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_5)
               dq_dq_rx_sa_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_5 = dq_dq_rx_sa_m0_r1_cfg_5_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_6_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_6)
               dq_dq_rx_sa_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_6 = dq_dq_rx_sa_m0_r1_cfg_6_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_7_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_7)
               dq_dq_rx_sa_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_7 = dq_dq_rx_sa_m0_r1_cfg_7_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m0_r1_cfg_8_q <= `DDR_DQ_DQ_RX_SA_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_8)
               dq_dq_rx_sa_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_m0_r1_cfg_8 = dq_dq_rx_sa_m0_r1_cfg_8_q & `DDR_DQ_DQ_RX_SA_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_0_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_0)
               dq_dq_rx_sa_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_0 = dq_dq_rx_sa_m1_r0_cfg_0_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_1_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_1)
               dq_dq_rx_sa_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_1 = dq_dq_rx_sa_m1_r0_cfg_1_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_2_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_2)
               dq_dq_rx_sa_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_2 = dq_dq_rx_sa_m1_r0_cfg_2_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_3_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_3)
               dq_dq_rx_sa_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_3 = dq_dq_rx_sa_m1_r0_cfg_3_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_4_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_4)
               dq_dq_rx_sa_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_4 = dq_dq_rx_sa_m1_r0_cfg_4_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_5_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_5)
               dq_dq_rx_sa_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_5 = dq_dq_rx_sa_m1_r0_cfg_5_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_6_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_6)
               dq_dq_rx_sa_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_6 = dq_dq_rx_sa_m1_r0_cfg_6_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_7_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_7)
               dq_dq_rx_sa_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_7 = dq_dq_rx_sa_m1_r0_cfg_7_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r0_cfg_8_q <= `DDR_DQ_DQ_RX_SA_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_8)
               dq_dq_rx_sa_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r0_cfg_8 = dq_dq_rx_sa_m1_r0_cfg_8_q & `DDR_DQ_DQ_RX_SA_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_0_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_0)
               dq_dq_rx_sa_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_0 = dq_dq_rx_sa_m1_r1_cfg_0_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_1_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_1)
               dq_dq_rx_sa_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_1 = dq_dq_rx_sa_m1_r1_cfg_1_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_2_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_2)
               dq_dq_rx_sa_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_2 = dq_dq_rx_sa_m1_r1_cfg_2_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_3_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_3)
               dq_dq_rx_sa_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_3 = dq_dq_rx_sa_m1_r1_cfg_3_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_4_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_4)
               dq_dq_rx_sa_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_4 = dq_dq_rx_sa_m1_r1_cfg_4_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_5_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_5)
               dq_dq_rx_sa_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_5 = dq_dq_rx_sa_m1_r1_cfg_5_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_6_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_6)
               dq_dq_rx_sa_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_6 = dq_dq_rx_sa_m1_r1_cfg_6_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_7_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_7)
               dq_dq_rx_sa_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_7 = dq_dq_rx_sa_m1_r1_cfg_7_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_m1_r1_cfg_8_q <= `DDR_DQ_DQ_RX_SA_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_8)
               dq_dq_rx_sa_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_m1_r1_cfg_8 = dq_dq_rx_sa_m1_r1_cfg_8_q & `DDR_DQ_DQ_RX_SA_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_0_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0)
               dq_dq_rx_sa_dly_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_0 = dq_dq_rx_sa_dly_m0_r0_cfg_0_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_1_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1)
               dq_dq_rx_sa_dly_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_1 = dq_dq_rx_sa_dly_m0_r0_cfg_1_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_2_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2)
               dq_dq_rx_sa_dly_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_2 = dq_dq_rx_sa_dly_m0_r0_cfg_2_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_3_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3)
               dq_dq_rx_sa_dly_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_3 = dq_dq_rx_sa_dly_m0_r0_cfg_3_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_4_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4)
               dq_dq_rx_sa_dly_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_4 = dq_dq_rx_sa_dly_m0_r0_cfg_4_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_5_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5)
               dq_dq_rx_sa_dly_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_5 = dq_dq_rx_sa_dly_m0_r0_cfg_5_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_6_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6)
               dq_dq_rx_sa_dly_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_6 = dq_dq_rx_sa_dly_m0_r0_cfg_6_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_7_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7)
               dq_dq_rx_sa_dly_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_7 = dq_dq_rx_sa_dly_m0_r0_cfg_7_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r0_cfg_8_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8)
               dq_dq_rx_sa_dly_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r0_cfg_8 = dq_dq_rx_sa_dly_m0_r0_cfg_8_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_0_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0)
               dq_dq_rx_sa_dly_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_0 = dq_dq_rx_sa_dly_m0_r1_cfg_0_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_1_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1)
               dq_dq_rx_sa_dly_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_1 = dq_dq_rx_sa_dly_m0_r1_cfg_1_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_2_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2)
               dq_dq_rx_sa_dly_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_2 = dq_dq_rx_sa_dly_m0_r1_cfg_2_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_3_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3)
               dq_dq_rx_sa_dly_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_3 = dq_dq_rx_sa_dly_m0_r1_cfg_3_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_4_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4)
               dq_dq_rx_sa_dly_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_4 = dq_dq_rx_sa_dly_m0_r1_cfg_4_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_5_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5)
               dq_dq_rx_sa_dly_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_5 = dq_dq_rx_sa_dly_m0_r1_cfg_5_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_6_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6)
               dq_dq_rx_sa_dly_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_6 = dq_dq_rx_sa_dly_m0_r1_cfg_6_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_7_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7)
               dq_dq_rx_sa_dly_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_7 = dq_dq_rx_sa_dly_m0_r1_cfg_7_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m0_r1_cfg_8_q <= `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8)
               dq_dq_rx_sa_dly_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m0_r1_cfg_8 = dq_dq_rx_sa_dly_m0_r1_cfg_8_q & `DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_0_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0)
               dq_dq_rx_sa_dly_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_0 = dq_dq_rx_sa_dly_m1_r0_cfg_0_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_1_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1)
               dq_dq_rx_sa_dly_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_1 = dq_dq_rx_sa_dly_m1_r0_cfg_1_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_2_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2)
               dq_dq_rx_sa_dly_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_2 = dq_dq_rx_sa_dly_m1_r0_cfg_2_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_3_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3)
               dq_dq_rx_sa_dly_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_3 = dq_dq_rx_sa_dly_m1_r0_cfg_3_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_4_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4)
               dq_dq_rx_sa_dly_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_4 = dq_dq_rx_sa_dly_m1_r0_cfg_4_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_5_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5)
               dq_dq_rx_sa_dly_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_5 = dq_dq_rx_sa_dly_m1_r0_cfg_5_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_6_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6)
               dq_dq_rx_sa_dly_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_6 = dq_dq_rx_sa_dly_m1_r0_cfg_6_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_7_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7)
               dq_dq_rx_sa_dly_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_7 = dq_dq_rx_sa_dly_m1_r0_cfg_7_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r0_cfg_8_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8)
               dq_dq_rx_sa_dly_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r0_cfg_8 = dq_dq_rx_sa_dly_m1_r0_cfg_8_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_0_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0)
               dq_dq_rx_sa_dly_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_0 = dq_dq_rx_sa_dly_m1_r1_cfg_0_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_1_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1)
               dq_dq_rx_sa_dly_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_1 = dq_dq_rx_sa_dly_m1_r1_cfg_1_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_2_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2)
               dq_dq_rx_sa_dly_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_2 = dq_dq_rx_sa_dly_m1_r1_cfg_2_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_3_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3)
               dq_dq_rx_sa_dly_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_3 = dq_dq_rx_sa_dly_m1_r1_cfg_3_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_4_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4)
               dq_dq_rx_sa_dly_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_4 = dq_dq_rx_sa_dly_m1_r1_cfg_4_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_5_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5)
               dq_dq_rx_sa_dly_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_5 = dq_dq_rx_sa_dly_m1_r1_cfg_5_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_6_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6)
               dq_dq_rx_sa_dly_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_6 = dq_dq_rx_sa_dly_m1_r1_cfg_6_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_7_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7)
               dq_dq_rx_sa_dly_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_7 = dq_dq_rx_sa_dly_m1_r1_cfg_7_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_rx_sa_dly_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_dly_m1_r1_cfg_8_q <= `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8)
               dq_dq_rx_sa_dly_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_rx_sa_dly_m1_r1_cfg_8 = dq_dq_rx_sa_dly_m1_r1_cfg_8_q & `DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_rx_sa_sta_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_0_q <= `DDR_DQ_DQ_RX_SA_STA_0_POR;
      else
         dq_dq_rx_sa_sta_0_q <= i_dq_dq_rx_sa_sta_0;

   logic [31:0] dq_dq_rx_sa_sta_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_1_q <= `DDR_DQ_DQ_RX_SA_STA_1_POR;
      else
         dq_dq_rx_sa_sta_1_q <= i_dq_dq_rx_sa_sta_1;

   logic [31:0] dq_dq_rx_sa_sta_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_2_q <= `DDR_DQ_DQ_RX_SA_STA_2_POR;
      else
         dq_dq_rx_sa_sta_2_q <= i_dq_dq_rx_sa_sta_2;

   logic [31:0] dq_dq_rx_sa_sta_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_3_q <= `DDR_DQ_DQ_RX_SA_STA_3_POR;
      else
         dq_dq_rx_sa_sta_3_q <= i_dq_dq_rx_sa_sta_3;

   logic [31:0] dq_dq_rx_sa_sta_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_4_q <= `DDR_DQ_DQ_RX_SA_STA_4_POR;
      else
         dq_dq_rx_sa_sta_4_q <= i_dq_dq_rx_sa_sta_4;

   logic [31:0] dq_dq_rx_sa_sta_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_5_q <= `DDR_DQ_DQ_RX_SA_STA_5_POR;
      else
         dq_dq_rx_sa_sta_5_q <= i_dq_dq_rx_sa_sta_5;

   logic [31:0] dq_dq_rx_sa_sta_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_6_q <= `DDR_DQ_DQ_RX_SA_STA_6_POR;
      else
         dq_dq_rx_sa_sta_6_q <= i_dq_dq_rx_sa_sta_6;

   logic [31:0] dq_dq_rx_sa_sta_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_7_q <= `DDR_DQ_DQ_RX_SA_STA_7_POR;
      else
         dq_dq_rx_sa_sta_7_q <= i_dq_dq_rx_sa_sta_7;

   logic [31:0] dq_dq_rx_sa_sta_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_rx_sa_sta_8_q <= `DDR_DQ_DQ_RX_SA_STA_8_POR;
      else
         dq_dq_rx_sa_sta_8_q <= i_dq_dq_rx_sa_sta_8;

   logic [31:0] dq_dq_tx_bscan_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_bscan_cfg_q <= `DDR_DQ_DQ_TX_BSCAN_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_BSCAN_CFG)
               dq_dq_tx_bscan_cfg_q <= i_wdata;

   assign o_dq_dq_tx_bscan_cfg = dq_dq_tx_bscan_cfg_q & `DDR_DQ_DQ_TX_BSCAN_CFG_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_0_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0)
               dq_dq_tx_egress_ana_m0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_0 = dq_dq_tx_egress_ana_m0_cfg_0_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_1_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1)
               dq_dq_tx_egress_ana_m0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_1 = dq_dq_tx_egress_ana_m0_cfg_1_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_2_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2)
               dq_dq_tx_egress_ana_m0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_2 = dq_dq_tx_egress_ana_m0_cfg_2_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_3_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3)
               dq_dq_tx_egress_ana_m0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_3 = dq_dq_tx_egress_ana_m0_cfg_3_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_4_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4)
               dq_dq_tx_egress_ana_m0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_4 = dq_dq_tx_egress_ana_m0_cfg_4_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_5_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5)
               dq_dq_tx_egress_ana_m0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_5 = dq_dq_tx_egress_ana_m0_cfg_5_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_6_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6)
               dq_dq_tx_egress_ana_m0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_6 = dq_dq_tx_egress_ana_m0_cfg_6_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_7_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7)
               dq_dq_tx_egress_ana_m0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_7 = dq_dq_tx_egress_ana_m0_cfg_7_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m0_cfg_8_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8)
               dq_dq_tx_egress_ana_m0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m0_cfg_8 = dq_dq_tx_egress_ana_m0_cfg_8_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_0_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0)
               dq_dq_tx_egress_ana_m1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_0 = dq_dq_tx_egress_ana_m1_cfg_0_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_1_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1)
               dq_dq_tx_egress_ana_m1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_1 = dq_dq_tx_egress_ana_m1_cfg_1_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_2_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2)
               dq_dq_tx_egress_ana_m1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_2 = dq_dq_tx_egress_ana_m1_cfg_2_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_3_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3)
               dq_dq_tx_egress_ana_m1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_3 = dq_dq_tx_egress_ana_m1_cfg_3_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_4_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4)
               dq_dq_tx_egress_ana_m1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_4 = dq_dq_tx_egress_ana_m1_cfg_4_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_5_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5)
               dq_dq_tx_egress_ana_m1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_5 = dq_dq_tx_egress_ana_m1_cfg_5_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_6_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6)
               dq_dq_tx_egress_ana_m1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_6 = dq_dq_tx_egress_ana_m1_cfg_6_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_7_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7)
               dq_dq_tx_egress_ana_m1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_7 = dq_dq_tx_egress_ana_m1_cfg_7_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_egress_ana_m1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_ana_m1_cfg_8_q <= `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8)
               dq_dq_tx_egress_ana_m1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_egress_ana_m1_cfg_8 = dq_dq_tx_egress_ana_m1_cfg_8_q & `DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_0_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0)
               dq_dq_tx_egress_dig_m0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_0 = dq_dq_tx_egress_dig_m0_cfg_0_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_1_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1)
               dq_dq_tx_egress_dig_m0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_1 = dq_dq_tx_egress_dig_m0_cfg_1_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_2_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2)
               dq_dq_tx_egress_dig_m0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_2 = dq_dq_tx_egress_dig_m0_cfg_2_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_3_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3)
               dq_dq_tx_egress_dig_m0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_3 = dq_dq_tx_egress_dig_m0_cfg_3_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_4_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4)
               dq_dq_tx_egress_dig_m0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_4 = dq_dq_tx_egress_dig_m0_cfg_4_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_5_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5)
               dq_dq_tx_egress_dig_m0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_5 = dq_dq_tx_egress_dig_m0_cfg_5_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_6_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6)
               dq_dq_tx_egress_dig_m0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_6 = dq_dq_tx_egress_dig_m0_cfg_6_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_7_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7)
               dq_dq_tx_egress_dig_m0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_7 = dq_dq_tx_egress_dig_m0_cfg_7_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m0_cfg_8_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8)
               dq_dq_tx_egress_dig_m0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m0_cfg_8 = dq_dq_tx_egress_dig_m0_cfg_8_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_0_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0)
               dq_dq_tx_egress_dig_m1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_0 = dq_dq_tx_egress_dig_m1_cfg_0_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_1_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1)
               dq_dq_tx_egress_dig_m1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_1 = dq_dq_tx_egress_dig_m1_cfg_1_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_2_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2)
               dq_dq_tx_egress_dig_m1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_2 = dq_dq_tx_egress_dig_m1_cfg_2_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_3_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3)
               dq_dq_tx_egress_dig_m1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_3 = dq_dq_tx_egress_dig_m1_cfg_3_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_4_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4)
               dq_dq_tx_egress_dig_m1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_4 = dq_dq_tx_egress_dig_m1_cfg_4_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_5_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5)
               dq_dq_tx_egress_dig_m1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_5 = dq_dq_tx_egress_dig_m1_cfg_5_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_6_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6)
               dq_dq_tx_egress_dig_m1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_6 = dq_dq_tx_egress_dig_m1_cfg_6_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_7_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7)
               dq_dq_tx_egress_dig_m1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_7 = dq_dq_tx_egress_dig_m1_cfg_7_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_egress_dig_m1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_egress_dig_m1_cfg_8_q <= `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8)
               dq_dq_tx_egress_dig_m1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_egress_dig_m1_cfg_8 = dq_dq_tx_egress_dig_m1_cfg_8_q & `DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_odr_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_odr_pi_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG)
               dq_dq_tx_odr_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_odr_pi_m0_r0_cfg = dq_dq_tx_odr_pi_m0_r0_cfg_q & `DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_odr_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_odr_pi_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG)
               dq_dq_tx_odr_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_odr_pi_m0_r1_cfg = dq_dq_tx_odr_pi_m0_r1_cfg_q & `DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_odr_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_odr_pi_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG)
               dq_dq_tx_odr_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_odr_pi_m1_r0_cfg = dq_dq_tx_odr_pi_m1_r0_cfg_q & `DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_odr_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_odr_pi_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG)
               dq_dq_tx_odr_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_odr_pi_m1_r1_cfg = dq_dq_tx_odr_pi_m1_r1_cfg_q & `DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_0_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_0_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG)
               dq_dq_tx_qdr_pi_0_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_0_m0_r0_cfg = dq_dq_tx_qdr_pi_0_m0_r0_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_0_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_0_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG)
               dq_dq_tx_qdr_pi_0_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_0_m0_r1_cfg = dq_dq_tx_qdr_pi_0_m0_r1_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_0_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_0_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG)
               dq_dq_tx_qdr_pi_0_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_0_m1_r0_cfg = dq_dq_tx_qdr_pi_0_m1_r0_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_0_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_0_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG)
               dq_dq_tx_qdr_pi_0_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_0_m1_r1_cfg = dq_dq_tx_qdr_pi_0_m1_r1_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_1_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_1_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG)
               dq_dq_tx_qdr_pi_1_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_1_m0_r0_cfg = dq_dq_tx_qdr_pi_1_m0_r0_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_1_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_1_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG)
               dq_dq_tx_qdr_pi_1_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_1_m0_r1_cfg = dq_dq_tx_qdr_pi_1_m0_r1_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_1_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_1_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG)
               dq_dq_tx_qdr_pi_1_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_1_m1_r0_cfg = dq_dq_tx_qdr_pi_1_m1_r0_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_qdr_pi_1_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_pi_1_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG)
               dq_dq_tx_qdr_pi_1_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_qdr_pi_1_m1_r1_cfg = dq_dq_tx_qdr_pi_1_m1_r1_cfg_q & `DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_0_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_0_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG)
               dq_dq_tx_ddr_pi_0_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_0_m0_r0_cfg = dq_dq_tx_ddr_pi_0_m0_r0_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_0_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_0_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG)
               dq_dq_tx_ddr_pi_0_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_0_m0_r1_cfg = dq_dq_tx_ddr_pi_0_m0_r1_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_0_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_0_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG)
               dq_dq_tx_ddr_pi_0_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_0_m1_r0_cfg = dq_dq_tx_ddr_pi_0_m1_r0_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_0_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_0_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG)
               dq_dq_tx_ddr_pi_0_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_0_m1_r1_cfg = dq_dq_tx_ddr_pi_0_m1_r1_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_1_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_1_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG)
               dq_dq_tx_ddr_pi_1_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_1_m0_r0_cfg = dq_dq_tx_ddr_pi_1_m0_r0_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_1_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_1_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG)
               dq_dq_tx_ddr_pi_1_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_1_m0_r1_cfg = dq_dq_tx_ddr_pi_1_m0_r1_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_1_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_1_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG)
               dq_dq_tx_ddr_pi_1_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_1_m1_r0_cfg = dq_dq_tx_ddr_pi_1_m1_r0_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_ddr_pi_1_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_pi_1_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG)
               dq_dq_tx_ddr_pi_1_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_ddr_pi_1_m1_r1_cfg = dq_dq_tx_ddr_pi_1_m1_r1_cfg_q & `DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_pi_rt_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_pi_rt_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG)
               dq_dq_tx_pi_rt_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_pi_rt_m0_r0_cfg = dq_dq_tx_pi_rt_m0_r0_cfg_q & `DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_pi_rt_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_pi_rt_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG)
               dq_dq_tx_pi_rt_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_pi_rt_m0_r1_cfg = dq_dq_tx_pi_rt_m0_r1_cfg_q & `DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_pi_rt_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_pi_rt_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG)
               dq_dq_tx_pi_rt_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_pi_rt_m1_r0_cfg = dq_dq_tx_pi_rt_m1_r0_cfg_q & `DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_pi_rt_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_pi_rt_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG)
               dq_dq_tx_pi_rt_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_pi_rt_m1_r1_cfg = dq_dq_tx_pi_rt_m1_r1_cfg_q & `DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_rt_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_rt_m0_r0_cfg_q <= `DDR_DQ_DQ_TX_RT_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_RT_M0_R0_CFG)
               dq_dq_tx_rt_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_rt_m0_r0_cfg = dq_dq_tx_rt_m0_r0_cfg_q & `DDR_DQ_DQ_TX_RT_M0_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_rt_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_rt_m0_r1_cfg_q <= `DDR_DQ_DQ_TX_RT_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_RT_M0_R1_CFG)
               dq_dq_tx_rt_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_rt_m0_r1_cfg = dq_dq_tx_rt_m0_r1_cfg_q & `DDR_DQ_DQ_TX_RT_M0_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_rt_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_rt_m1_r0_cfg_q <= `DDR_DQ_DQ_TX_RT_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_RT_M1_R0_CFG)
               dq_dq_tx_rt_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dq_tx_rt_m1_r0_cfg = dq_dq_tx_rt_m1_r0_cfg_q & `DDR_DQ_DQ_TX_RT_M1_R0_CFG_MSK;

   logic [31:0] dq_dq_tx_rt_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_rt_m1_r1_cfg_q <= `DDR_DQ_DQ_TX_RT_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_RT_M1_R1_CFG)
               dq_dq_tx_rt_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dq_tx_rt_m1_r1_cfg = dq_dq_tx_rt_m1_r1_cfg_q & `DDR_DQ_DQ_TX_RT_M1_R1_CFG_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0)
               dq_dq_tx_sdr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_0 = dq_dq_tx_sdr_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1)
               dq_dq_tx_sdr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_1 = dq_dq_tx_sdr_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2)
               dq_dq_tx_sdr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_2 = dq_dq_tx_sdr_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3)
               dq_dq_tx_sdr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_3 = dq_dq_tx_sdr_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4)
               dq_dq_tx_sdr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_4 = dq_dq_tx_sdr_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5)
               dq_dq_tx_sdr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_5 = dq_dq_tx_sdr_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6)
               dq_dq_tx_sdr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_6 = dq_dq_tx_sdr_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7)
               dq_dq_tx_sdr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_7 = dq_dq_tx_sdr_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8)
               dq_dq_tx_sdr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r0_cfg_8 = dq_dq_tx_sdr_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0)
               dq_dq_tx_sdr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_0 = dq_dq_tx_sdr_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1)
               dq_dq_tx_sdr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_1 = dq_dq_tx_sdr_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2)
               dq_dq_tx_sdr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_2 = dq_dq_tx_sdr_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3)
               dq_dq_tx_sdr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_3 = dq_dq_tx_sdr_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4)
               dq_dq_tx_sdr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_4 = dq_dq_tx_sdr_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5)
               dq_dq_tx_sdr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_5 = dq_dq_tx_sdr_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6)
               dq_dq_tx_sdr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_6 = dq_dq_tx_sdr_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7)
               dq_dq_tx_sdr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_7 = dq_dq_tx_sdr_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8)
               dq_dq_tx_sdr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m0_r1_cfg_8 = dq_dq_tx_sdr_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0)
               dq_dq_tx_sdr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_0 = dq_dq_tx_sdr_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1)
               dq_dq_tx_sdr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_1 = dq_dq_tx_sdr_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2)
               dq_dq_tx_sdr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_2 = dq_dq_tx_sdr_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3)
               dq_dq_tx_sdr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_3 = dq_dq_tx_sdr_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4)
               dq_dq_tx_sdr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_4 = dq_dq_tx_sdr_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5)
               dq_dq_tx_sdr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_5 = dq_dq_tx_sdr_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6)
               dq_dq_tx_sdr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_6 = dq_dq_tx_sdr_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7)
               dq_dq_tx_sdr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_7 = dq_dq_tx_sdr_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8)
               dq_dq_tx_sdr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r0_cfg_8 = dq_dq_tx_sdr_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0)
               dq_dq_tx_sdr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_0 = dq_dq_tx_sdr_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1)
               dq_dq_tx_sdr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_1 = dq_dq_tx_sdr_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2)
               dq_dq_tx_sdr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_2 = dq_dq_tx_sdr_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3)
               dq_dq_tx_sdr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_3 = dq_dq_tx_sdr_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4)
               dq_dq_tx_sdr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_4 = dq_dq_tx_sdr_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5)
               dq_dq_tx_sdr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_5 = dq_dq_tx_sdr_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6)
               dq_dq_tx_sdr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_6 = dq_dq_tx_sdr_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7)
               dq_dq_tx_sdr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_7 = dq_dq_tx_sdr_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8)
               dq_dq_tx_sdr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_m1_r1_cfg_8 = dq_dq_tx_sdr_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_0 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_1 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_2 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_3 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_4 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_5 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_6 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_7 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8)
               dq_dq_tx_sdr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_8 = dq_dq_tx_sdr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_0 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_1 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_2 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_3 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_4 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_5 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_6 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_7 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8)
               dq_dq_tx_sdr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_8 = dq_dq_tx_sdr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_0 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_1 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_2 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_3 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_4 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_5 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_6 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_7 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8)
               dq_dq_tx_sdr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_8 = dq_dq_tx_sdr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_0 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_1 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_2 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_3 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_4 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_5 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_6 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_7 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8)
               dq_dq_tx_sdr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_8 = dq_dq_tx_sdr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8)
               dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8 = dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8)
               dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8 = dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8)
               dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8 = dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8)
               dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8 = dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0)
               dq_dq_tx_ddr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_0 = dq_dq_tx_ddr_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1)
               dq_dq_tx_ddr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_1 = dq_dq_tx_ddr_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2)
               dq_dq_tx_ddr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_2 = dq_dq_tx_ddr_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3)
               dq_dq_tx_ddr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_3 = dq_dq_tx_ddr_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4)
               dq_dq_tx_ddr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_4 = dq_dq_tx_ddr_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5)
               dq_dq_tx_ddr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_5 = dq_dq_tx_ddr_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6)
               dq_dq_tx_ddr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_6 = dq_dq_tx_ddr_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7)
               dq_dq_tx_ddr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_7 = dq_dq_tx_ddr_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8)
               dq_dq_tx_ddr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r0_cfg_8 = dq_dq_tx_ddr_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0)
               dq_dq_tx_ddr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_0 = dq_dq_tx_ddr_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1)
               dq_dq_tx_ddr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_1 = dq_dq_tx_ddr_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2)
               dq_dq_tx_ddr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_2 = dq_dq_tx_ddr_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3)
               dq_dq_tx_ddr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_3 = dq_dq_tx_ddr_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4)
               dq_dq_tx_ddr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_4 = dq_dq_tx_ddr_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5)
               dq_dq_tx_ddr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_5 = dq_dq_tx_ddr_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6)
               dq_dq_tx_ddr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_6 = dq_dq_tx_ddr_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7)
               dq_dq_tx_ddr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_7 = dq_dq_tx_ddr_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8)
               dq_dq_tx_ddr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m0_r1_cfg_8 = dq_dq_tx_ddr_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0)
               dq_dq_tx_ddr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_0 = dq_dq_tx_ddr_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1)
               dq_dq_tx_ddr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_1 = dq_dq_tx_ddr_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2)
               dq_dq_tx_ddr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_2 = dq_dq_tx_ddr_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3)
               dq_dq_tx_ddr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_3 = dq_dq_tx_ddr_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4)
               dq_dq_tx_ddr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_4 = dq_dq_tx_ddr_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5)
               dq_dq_tx_ddr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_5 = dq_dq_tx_ddr_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6)
               dq_dq_tx_ddr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_6 = dq_dq_tx_ddr_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7)
               dq_dq_tx_ddr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_7 = dq_dq_tx_ddr_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8)
               dq_dq_tx_ddr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r0_cfg_8 = dq_dq_tx_ddr_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0)
               dq_dq_tx_ddr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_0 = dq_dq_tx_ddr_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1)
               dq_dq_tx_ddr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_1 = dq_dq_tx_ddr_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2)
               dq_dq_tx_ddr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_2 = dq_dq_tx_ddr_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3)
               dq_dq_tx_ddr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_3 = dq_dq_tx_ddr_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4)
               dq_dq_tx_ddr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_4 = dq_dq_tx_ddr_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5)
               dq_dq_tx_ddr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_5 = dq_dq_tx_ddr_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6)
               dq_dq_tx_ddr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_6 = dq_dq_tx_ddr_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7)
               dq_dq_tx_ddr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_7 = dq_dq_tx_ddr_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8)
               dq_dq_tx_ddr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_m1_r1_cfg_8 = dq_dq_tx_ddr_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_0 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_1 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_2 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_3 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_4 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_5 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_6 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_7 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8)
               dq_dq_tx_ddr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_8 = dq_dq_tx_ddr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_0 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_1 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_2 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_3 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_4 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_5 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_6 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_7 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8)
               dq_dq_tx_ddr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_8 = dq_dq_tx_ddr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_0 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_1 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_2 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_3 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_4 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_5 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_6 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_7 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8)
               dq_dq_tx_ddr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_8 = dq_dq_tx_ddr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_0 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_1 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_2 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_3 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_4 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_5 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_6 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_7 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_ddr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_ddr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8)
               dq_dq_tx_ddr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_8 = dq_dq_tx_ddr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0)
               dq_dq_tx_qdr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_0 = dq_dq_tx_qdr_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1)
               dq_dq_tx_qdr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_1 = dq_dq_tx_qdr_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2)
               dq_dq_tx_qdr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_2 = dq_dq_tx_qdr_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3)
               dq_dq_tx_qdr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_3 = dq_dq_tx_qdr_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4)
               dq_dq_tx_qdr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_4 = dq_dq_tx_qdr_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5)
               dq_dq_tx_qdr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_5 = dq_dq_tx_qdr_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6)
               dq_dq_tx_qdr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_6 = dq_dq_tx_qdr_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7)
               dq_dq_tx_qdr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_7 = dq_dq_tx_qdr_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8)
               dq_dq_tx_qdr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r0_cfg_8 = dq_dq_tx_qdr_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0)
               dq_dq_tx_qdr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_0 = dq_dq_tx_qdr_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1)
               dq_dq_tx_qdr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_1 = dq_dq_tx_qdr_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2)
               dq_dq_tx_qdr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_2 = dq_dq_tx_qdr_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3)
               dq_dq_tx_qdr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_3 = dq_dq_tx_qdr_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4)
               dq_dq_tx_qdr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_4 = dq_dq_tx_qdr_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5)
               dq_dq_tx_qdr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_5 = dq_dq_tx_qdr_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6)
               dq_dq_tx_qdr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_6 = dq_dq_tx_qdr_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7)
               dq_dq_tx_qdr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_7 = dq_dq_tx_qdr_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8)
               dq_dq_tx_qdr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m0_r1_cfg_8 = dq_dq_tx_qdr_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0)
               dq_dq_tx_qdr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_0 = dq_dq_tx_qdr_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1)
               dq_dq_tx_qdr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_1 = dq_dq_tx_qdr_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2)
               dq_dq_tx_qdr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_2 = dq_dq_tx_qdr_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3)
               dq_dq_tx_qdr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_3 = dq_dq_tx_qdr_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4)
               dq_dq_tx_qdr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_4 = dq_dq_tx_qdr_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5)
               dq_dq_tx_qdr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_5 = dq_dq_tx_qdr_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6)
               dq_dq_tx_qdr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_6 = dq_dq_tx_qdr_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7)
               dq_dq_tx_qdr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_7 = dq_dq_tx_qdr_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8)
               dq_dq_tx_qdr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r0_cfg_8 = dq_dq_tx_qdr_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0)
               dq_dq_tx_qdr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_0 = dq_dq_tx_qdr_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1)
               dq_dq_tx_qdr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_1 = dq_dq_tx_qdr_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2)
               dq_dq_tx_qdr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_2 = dq_dq_tx_qdr_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3)
               dq_dq_tx_qdr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_3 = dq_dq_tx_qdr_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4)
               dq_dq_tx_qdr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_4 = dq_dq_tx_qdr_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5)
               dq_dq_tx_qdr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_5 = dq_dq_tx_qdr_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6)
               dq_dq_tx_qdr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_6 = dq_dq_tx_qdr_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7)
               dq_dq_tx_qdr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_7 = dq_dq_tx_qdr_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8)
               dq_dq_tx_qdr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_m1_r1_cfg_8 = dq_dq_tx_qdr_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_0 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_1 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_2 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_3 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_4 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_5 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_6 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_7 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8)
               dq_dq_tx_qdr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_8 = dq_dq_tx_qdr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_0 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_1 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_2 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_3 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_4 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_5 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_6 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_7 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8)
               dq_dq_tx_qdr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_8 = dq_dq_tx_qdr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_0 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_1 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_2 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_3 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_4 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_5 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_6 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_7 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8)
               dq_dq_tx_qdr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_8 = dq_dq_tx_qdr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_0 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_1 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_2 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_3 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_4 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_5 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_6 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_7 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_qdr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_qdr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8)
               dq_dq_tx_qdr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_8 = dq_dq_tx_qdr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_0_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0)
               dq_dq_tx_lpde_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_0 = dq_dq_tx_lpde_m0_r0_cfg_0_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_1_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1)
               dq_dq_tx_lpde_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_1 = dq_dq_tx_lpde_m0_r0_cfg_1_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_2_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2)
               dq_dq_tx_lpde_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_2 = dq_dq_tx_lpde_m0_r0_cfg_2_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_3_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3)
               dq_dq_tx_lpde_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_3 = dq_dq_tx_lpde_m0_r0_cfg_3_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_4_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4)
               dq_dq_tx_lpde_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_4 = dq_dq_tx_lpde_m0_r0_cfg_4_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_5_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5)
               dq_dq_tx_lpde_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_5 = dq_dq_tx_lpde_m0_r0_cfg_5_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_6_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6)
               dq_dq_tx_lpde_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_6 = dq_dq_tx_lpde_m0_r0_cfg_6_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_7_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7)
               dq_dq_tx_lpde_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_7 = dq_dq_tx_lpde_m0_r0_cfg_7_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r0_cfg_8_q <= `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8)
               dq_dq_tx_lpde_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r0_cfg_8 = dq_dq_tx_lpde_m0_r0_cfg_8_q & `DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_0_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0)
               dq_dq_tx_lpde_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_0 = dq_dq_tx_lpde_m0_r1_cfg_0_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_1_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1)
               dq_dq_tx_lpde_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_1 = dq_dq_tx_lpde_m0_r1_cfg_1_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_2_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2)
               dq_dq_tx_lpde_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_2 = dq_dq_tx_lpde_m0_r1_cfg_2_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_3_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3)
               dq_dq_tx_lpde_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_3 = dq_dq_tx_lpde_m0_r1_cfg_3_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_4_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4)
               dq_dq_tx_lpde_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_4 = dq_dq_tx_lpde_m0_r1_cfg_4_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_5_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5)
               dq_dq_tx_lpde_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_5 = dq_dq_tx_lpde_m0_r1_cfg_5_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_6_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6)
               dq_dq_tx_lpde_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_6 = dq_dq_tx_lpde_m0_r1_cfg_6_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_7_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7)
               dq_dq_tx_lpde_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_7 = dq_dq_tx_lpde_m0_r1_cfg_7_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_lpde_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m0_r1_cfg_8_q <= `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8)
               dq_dq_tx_lpde_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m0_r1_cfg_8 = dq_dq_tx_lpde_m0_r1_cfg_8_q & `DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_0_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0)
               dq_dq_tx_lpde_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_0 = dq_dq_tx_lpde_m1_r0_cfg_0_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_1_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1)
               dq_dq_tx_lpde_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_1 = dq_dq_tx_lpde_m1_r0_cfg_1_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_2_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2)
               dq_dq_tx_lpde_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_2 = dq_dq_tx_lpde_m1_r0_cfg_2_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_3_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3)
               dq_dq_tx_lpde_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_3 = dq_dq_tx_lpde_m1_r0_cfg_3_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_4_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4)
               dq_dq_tx_lpde_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_4 = dq_dq_tx_lpde_m1_r0_cfg_4_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_5_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5)
               dq_dq_tx_lpde_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_5 = dq_dq_tx_lpde_m1_r0_cfg_5_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_6_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6)
               dq_dq_tx_lpde_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_6 = dq_dq_tx_lpde_m1_r0_cfg_6_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_7_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7)
               dq_dq_tx_lpde_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_7 = dq_dq_tx_lpde_m1_r0_cfg_7_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r0_cfg_8_q <= `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8)
               dq_dq_tx_lpde_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r0_cfg_8 = dq_dq_tx_lpde_m1_r0_cfg_8_q & `DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_0_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0)
               dq_dq_tx_lpde_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_0 = dq_dq_tx_lpde_m1_r1_cfg_0_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_1_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1)
               dq_dq_tx_lpde_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_1 = dq_dq_tx_lpde_m1_r1_cfg_1_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_2_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2)
               dq_dq_tx_lpde_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_2 = dq_dq_tx_lpde_m1_r1_cfg_2_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_3_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3)
               dq_dq_tx_lpde_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_3 = dq_dq_tx_lpde_m1_r1_cfg_3_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_4_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4)
               dq_dq_tx_lpde_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_4 = dq_dq_tx_lpde_m1_r1_cfg_4_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_5_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5)
               dq_dq_tx_lpde_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_5 = dq_dq_tx_lpde_m1_r1_cfg_5_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_6_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6)
               dq_dq_tx_lpde_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_6 = dq_dq_tx_lpde_m1_r1_cfg_6_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_7_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7)
               dq_dq_tx_lpde_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_7 = dq_dq_tx_lpde_m1_r1_cfg_7_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_lpde_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_lpde_m1_r1_cfg_8_q <= `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8)
               dq_dq_tx_lpde_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_lpde_m1_r1_cfg_8 = dq_dq_tx_lpde_m1_r1_cfg_8_q & `DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_0_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_0)
               dq_dq_tx_io_m0_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_0 = dq_dq_tx_io_m0_cfg_0_q & `DDR_DQ_DQ_TX_IO_M0_CFG_0_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_1_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_1)
               dq_dq_tx_io_m0_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_1 = dq_dq_tx_io_m0_cfg_1_q & `DDR_DQ_DQ_TX_IO_M0_CFG_1_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_2_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_2)
               dq_dq_tx_io_m0_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_2 = dq_dq_tx_io_m0_cfg_2_q & `DDR_DQ_DQ_TX_IO_M0_CFG_2_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_3_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_3)
               dq_dq_tx_io_m0_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_3 = dq_dq_tx_io_m0_cfg_3_q & `DDR_DQ_DQ_TX_IO_M0_CFG_3_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_4_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_4)
               dq_dq_tx_io_m0_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_4 = dq_dq_tx_io_m0_cfg_4_q & `DDR_DQ_DQ_TX_IO_M0_CFG_4_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_5_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_5)
               dq_dq_tx_io_m0_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_5 = dq_dq_tx_io_m0_cfg_5_q & `DDR_DQ_DQ_TX_IO_M0_CFG_5_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_6_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_6)
               dq_dq_tx_io_m0_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_6 = dq_dq_tx_io_m0_cfg_6_q & `DDR_DQ_DQ_TX_IO_M0_CFG_6_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_7_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_7)
               dq_dq_tx_io_m0_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_7 = dq_dq_tx_io_m0_cfg_7_q & `DDR_DQ_DQ_TX_IO_M0_CFG_7_MSK;

   logic [31:0] dq_dq_tx_io_m0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m0_cfg_8_q <= `DDR_DQ_DQ_TX_IO_M0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_8)
               dq_dq_tx_io_m0_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_io_m0_cfg_8 = dq_dq_tx_io_m0_cfg_8_q & `DDR_DQ_DQ_TX_IO_M0_CFG_8_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_0_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_0)
               dq_dq_tx_io_m1_cfg_0_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_0 = dq_dq_tx_io_m1_cfg_0_q & `DDR_DQ_DQ_TX_IO_M1_CFG_0_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_1_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_1)
               dq_dq_tx_io_m1_cfg_1_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_1 = dq_dq_tx_io_m1_cfg_1_q & `DDR_DQ_DQ_TX_IO_M1_CFG_1_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_2_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_2)
               dq_dq_tx_io_m1_cfg_2_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_2 = dq_dq_tx_io_m1_cfg_2_q & `DDR_DQ_DQ_TX_IO_M1_CFG_2_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_3_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_3)
               dq_dq_tx_io_m1_cfg_3_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_3 = dq_dq_tx_io_m1_cfg_3_q & `DDR_DQ_DQ_TX_IO_M1_CFG_3_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_4_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_4)
               dq_dq_tx_io_m1_cfg_4_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_4 = dq_dq_tx_io_m1_cfg_4_q & `DDR_DQ_DQ_TX_IO_M1_CFG_4_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_5_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_5)
               dq_dq_tx_io_m1_cfg_5_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_5 = dq_dq_tx_io_m1_cfg_5_q & `DDR_DQ_DQ_TX_IO_M1_CFG_5_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_6_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_6)
               dq_dq_tx_io_m1_cfg_6_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_6 = dq_dq_tx_io_m1_cfg_6_q & `DDR_DQ_DQ_TX_IO_M1_CFG_6_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_7_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_7)
               dq_dq_tx_io_m1_cfg_7_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_7 = dq_dq_tx_io_m1_cfg_7_q & `DDR_DQ_DQ_TX_IO_M1_CFG_7_MSK;

   logic [31:0] dq_dq_tx_io_m1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dq_tx_io_m1_cfg_8_q <= `DDR_DQ_DQ_TX_IO_M1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_8)
               dq_dq_tx_io_m1_cfg_8_q <= i_wdata;

   assign o_dq_dq_tx_io_m1_cfg_8 = dq_dq_tx_io_m1_cfg_8_q & `DDR_DQ_DQ_TX_IO_M1_CFG_8_MSK;

   logic [31:0] dq_dqs_rx_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_m0_cfg_q <= `DDR_DQ_DQS_RX_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_M0_CFG)
               dq_dqs_rx_m0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_m0_cfg = dq_dqs_rx_m0_cfg_q & `DDR_DQ_DQS_RX_M0_CFG_MSK;

   logic [31:0] dq_dqs_rx_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_m1_cfg_q <= `DDR_DQ_DQS_RX_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_M1_CFG)
               dq_dqs_rx_m1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_m1_cfg = dq_dqs_rx_m1_cfg_q & `DDR_DQ_DQS_RX_M1_CFG_MSK;

   logic [31:0] dq_dqs_rx_bscan_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_bscan_sta_q <= `DDR_DQ_DQS_RX_BSCAN_STA_POR;
      else
         dq_dqs_rx_bscan_sta_q <= i_dq_dqs_rx_bscan_sta;

   logic [31:0] dq_dqs_rx_sdr_lpde_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sdr_lpde_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG)
               dq_dqs_rx_sdr_lpde_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_sdr_lpde_m0_r0_cfg = dq_dqs_rx_sdr_lpde_m0_r0_cfg_q & `DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_sdr_lpde_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sdr_lpde_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG)
               dq_dqs_rx_sdr_lpde_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_sdr_lpde_m0_r1_cfg = dq_dqs_rx_sdr_lpde_m0_r1_cfg_q & `DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_sdr_lpde_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sdr_lpde_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG)
               dq_dqs_rx_sdr_lpde_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_sdr_lpde_m1_r0_cfg = dq_dqs_rx_sdr_lpde_m1_r0_cfg_q & `DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_sdr_lpde_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sdr_lpde_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG)
               dq_dqs_rx_sdr_lpde_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_sdr_lpde_m1_r1_cfg = dq_dqs_rx_sdr_lpde_m1_r1_cfg_q & `DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_ren_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_ren_pi_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG)
               dq_dqs_rx_ren_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_ren_pi_m0_r0_cfg = dq_dqs_rx_ren_pi_m0_r0_cfg_q & `DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_ren_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_ren_pi_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG)
               dq_dqs_rx_ren_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_ren_pi_m0_r1_cfg = dq_dqs_rx_ren_pi_m0_r1_cfg_q & `DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_ren_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_ren_pi_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG)
               dq_dqs_rx_ren_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_ren_pi_m1_r0_cfg = dq_dqs_rx_ren_pi_m1_r0_cfg_q & `DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_ren_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_ren_pi_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG)
               dq_dqs_rx_ren_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_ren_pi_m1_r1_cfg = dq_dqs_rx_ren_pi_m1_r1_cfg_q & `DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rcs_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rcs_pi_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG)
               dq_dqs_rx_rcs_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rcs_pi_m0_r0_cfg = dq_dqs_rx_rcs_pi_m0_r0_cfg_q & `DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rcs_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rcs_pi_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG)
               dq_dqs_rx_rcs_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rcs_pi_m0_r1_cfg = dq_dqs_rx_rcs_pi_m0_r1_cfg_q & `DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rcs_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rcs_pi_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG)
               dq_dqs_rx_rcs_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rcs_pi_m1_r0_cfg = dq_dqs_rx_rcs_pi_m1_r0_cfg_q & `DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rcs_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rcs_pi_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG)
               dq_dqs_rx_rcs_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rcs_pi_m1_r1_cfg = dq_dqs_rx_rcs_pi_m1_r1_cfg_q & `DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_0_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_0_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG)
               dq_dqs_rx_rdqs_pi_0_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_0_m0_r0_cfg = dq_dqs_rx_rdqs_pi_0_m0_r0_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_0_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_0_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG)
               dq_dqs_rx_rdqs_pi_0_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_0_m0_r1_cfg = dq_dqs_rx_rdqs_pi_0_m0_r1_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_0_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_0_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG)
               dq_dqs_rx_rdqs_pi_0_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_0_m1_r0_cfg = dq_dqs_rx_rdqs_pi_0_m1_r0_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_0_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_0_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG)
               dq_dqs_rx_rdqs_pi_0_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_0_m1_r1_cfg = dq_dqs_rx_rdqs_pi_0_m1_r1_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_1_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_1_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG)
               dq_dqs_rx_rdqs_pi_1_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_1_m0_r0_cfg = dq_dqs_rx_rdqs_pi_1_m0_r0_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_1_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_1_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG)
               dq_dqs_rx_rdqs_pi_1_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_1_m0_r1_cfg = dq_dqs_rx_rdqs_pi_1_m0_r1_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_1_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_1_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG)
               dq_dqs_rx_rdqs_pi_1_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_1_m1_r0_cfg = dq_dqs_rx_rdqs_pi_1_m1_r0_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_rdqs_pi_1_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_rdqs_pi_1_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG)
               dq_dqs_rx_rdqs_pi_1_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_rdqs_pi_1_m1_r1_cfg = dq_dqs_rx_rdqs_pi_1_m1_r1_cfg_q & `DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_pi_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_pi_sta_q <= `DDR_DQ_DQS_RX_PI_STA_POR;
      else
         dq_dqs_rx_pi_sta_q <= i_dq_dqs_rx_pi_sta;

   logic [31:0] dq_dqs_rx_io_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m0_r0_cfg_0_q <= `DDR_DQ_DQS_RX_IO_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_0)
               dq_dqs_rx_io_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_io_m0_r0_cfg_0 = dq_dqs_rx_io_m0_r0_cfg_0_q & `DDR_DQ_DQS_RX_IO_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_io_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m0_r0_cfg_1_q <= `DDR_DQ_DQS_RX_IO_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_1)
               dq_dqs_rx_io_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_io_m0_r0_cfg_1 = dq_dqs_rx_io_m0_r0_cfg_1_q & `DDR_DQ_DQS_RX_IO_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_io_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m0_r1_cfg_0_q <= `DDR_DQ_DQS_RX_IO_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_0)
               dq_dqs_rx_io_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_io_m0_r1_cfg_0 = dq_dqs_rx_io_m0_r1_cfg_0_q & `DDR_DQ_DQS_RX_IO_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_io_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m0_r1_cfg_1_q <= `DDR_DQ_DQS_RX_IO_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_1)
               dq_dqs_rx_io_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_io_m0_r1_cfg_1 = dq_dqs_rx_io_m0_r1_cfg_1_q & `DDR_DQ_DQS_RX_IO_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_io_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m1_r0_cfg_0_q <= `DDR_DQ_DQS_RX_IO_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_0)
               dq_dqs_rx_io_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_io_m1_r0_cfg_0 = dq_dqs_rx_io_m1_r0_cfg_0_q & `DDR_DQ_DQS_RX_IO_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_io_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m1_r0_cfg_1_q <= `DDR_DQ_DQS_RX_IO_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_1)
               dq_dqs_rx_io_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_io_m1_r0_cfg_1 = dq_dqs_rx_io_m1_r0_cfg_1_q & `DDR_DQ_DQS_RX_IO_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_io_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m1_r1_cfg_0_q <= `DDR_DQ_DQS_RX_IO_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_0)
               dq_dqs_rx_io_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_io_m1_r1_cfg_0 = dq_dqs_rx_io_m1_r1_cfg_0_q & `DDR_DQ_DQS_RX_IO_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_io_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_m1_r1_cfg_1_q <= `DDR_DQ_DQS_RX_IO_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_1)
               dq_dqs_rx_io_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_io_m1_r1_cfg_1 = dq_dqs_rx_io_m1_r1_cfg_1_q & `DDR_DQ_DQS_RX_IO_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_io_cmn_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_cmn_m0_r0_cfg_q <= `DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG)
               dq_dqs_rx_io_cmn_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_io_cmn_m0_r0_cfg = dq_dqs_rx_io_cmn_m0_r0_cfg_q & `DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_io_cmn_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_cmn_m0_r1_cfg_q <= `DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG)
               dq_dqs_rx_io_cmn_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_io_cmn_m0_r1_cfg = dq_dqs_rx_io_cmn_m0_r1_cfg_q & `DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_io_cmn_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_cmn_m1_r0_cfg_q <= `DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG)
               dq_dqs_rx_io_cmn_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_io_cmn_m1_r0_cfg = dq_dqs_rx_io_cmn_m1_r0_cfg_q & `DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_rx_io_cmn_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_cmn_m1_r1_cfg_q <= `DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG)
               dq_dqs_rx_io_cmn_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_io_cmn_m1_r1_cfg = dq_dqs_rx_io_cmn_m1_r1_cfg_q & `DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_rx_io_sta_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_io_sta_q <= `DDR_DQ_DQS_RX_IO_STA_POR;
      else
         dq_dqs_rx_io_sta_q <= i_dq_dqs_rx_io_sta;

   logic [31:0] dq_dqs_rx_sa_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m0_r0_cfg_0_q <= `DDR_DQ_DQS_RX_SA_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_0)
               dq_dqs_rx_sa_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m0_r0_cfg_0 = dq_dqs_rx_sa_m0_r0_cfg_0_q & `DDR_DQ_DQS_RX_SA_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_sa_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m0_r0_cfg_1_q <= `DDR_DQ_DQS_RX_SA_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_1)
               dq_dqs_rx_sa_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m0_r0_cfg_1 = dq_dqs_rx_sa_m0_r0_cfg_1_q & `DDR_DQ_DQS_RX_SA_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_sa_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m0_r1_cfg_0_q <= `DDR_DQ_DQS_RX_SA_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_0)
               dq_dqs_rx_sa_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m0_r1_cfg_0 = dq_dqs_rx_sa_m0_r1_cfg_0_q & `DDR_DQ_DQS_RX_SA_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_sa_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m0_r1_cfg_1_q <= `DDR_DQ_DQS_RX_SA_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_1)
               dq_dqs_rx_sa_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m0_r1_cfg_1 = dq_dqs_rx_sa_m0_r1_cfg_1_q & `DDR_DQ_DQS_RX_SA_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_sa_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m1_r0_cfg_0_q <= `DDR_DQ_DQS_RX_SA_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_0)
               dq_dqs_rx_sa_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m1_r0_cfg_0 = dq_dqs_rx_sa_m1_r0_cfg_0_q & `DDR_DQ_DQS_RX_SA_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_sa_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m1_r0_cfg_1_q <= `DDR_DQ_DQS_RX_SA_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_1)
               dq_dqs_rx_sa_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m1_r0_cfg_1 = dq_dqs_rx_sa_m1_r0_cfg_1_q & `DDR_DQ_DQS_RX_SA_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_sa_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m1_r1_cfg_0_q <= `DDR_DQ_DQS_RX_SA_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_0)
               dq_dqs_rx_sa_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m1_r1_cfg_0 = dq_dqs_rx_sa_m1_r1_cfg_0_q & `DDR_DQ_DQS_RX_SA_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_rx_sa_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_m1_r1_cfg_1_q <= `DDR_DQ_DQS_RX_SA_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_1)
               dq_dqs_rx_sa_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_rx_sa_m1_r1_cfg_1 = dq_dqs_rx_sa_m1_r1_cfg_1_q & `DDR_DQ_DQS_RX_SA_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_rx_sa_cmn_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_rx_sa_cmn_cfg_q <= `DDR_DQ_DQS_RX_SA_CMN_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_RX_SA_CMN_CFG)
               dq_dqs_rx_sa_cmn_cfg_q <= i_wdata;

   assign o_dq_dqs_rx_sa_cmn_cfg = dq_dqs_rx_sa_cmn_cfg_q & `DDR_DQ_DQS_RX_SA_CMN_CFG_MSK;

   logic [31:0] dq_dqs_tx_m0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_m0_cfg_q <= `DDR_DQ_DQS_TX_M0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_M0_CFG)
               dq_dqs_tx_m0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_m0_cfg = dq_dqs_tx_m0_cfg_q & `DDR_DQ_DQS_TX_M0_CFG_MSK;

   logic [31:0] dq_dqs_tx_m1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_m1_cfg_q <= `DDR_DQ_DQS_TX_M1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_M1_CFG)
               dq_dqs_tx_m1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_m1_cfg = dq_dqs_tx_m1_cfg_q & `DDR_DQ_DQS_TX_M1_CFG_MSK;

   logic [31:0] dq_dqs_tx_bscan_ctrl_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_bscan_ctrl_cfg_q <= `DDR_DQ_DQS_TX_BSCAN_CTRL_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_BSCAN_CTRL_CFG)
               dq_dqs_tx_bscan_ctrl_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_bscan_ctrl_cfg = dq_dqs_tx_bscan_ctrl_cfg_q & `DDR_DQ_DQS_TX_BSCAN_CTRL_CFG_MSK;

   logic [31:0] dq_dqs_tx_bscan_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_bscan_cfg_q <= `DDR_DQ_DQS_TX_BSCAN_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_BSCAN_CFG)
               dq_dqs_tx_bscan_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_bscan_cfg = dq_dqs_tx_bscan_cfg_q & `DDR_DQ_DQS_TX_BSCAN_CFG_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_0_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0)
               dq_dqs_tx_egress_ana_m0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_0 = dq_dqs_tx_egress_ana_m0_cfg_0_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_1_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1)
               dq_dqs_tx_egress_ana_m0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_1 = dq_dqs_tx_egress_ana_m0_cfg_1_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_2_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2)
               dq_dqs_tx_egress_ana_m0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_2 = dq_dqs_tx_egress_ana_m0_cfg_2_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_3_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3)
               dq_dqs_tx_egress_ana_m0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_3 = dq_dqs_tx_egress_ana_m0_cfg_3_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_4_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4)
               dq_dqs_tx_egress_ana_m0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_4 = dq_dqs_tx_egress_ana_m0_cfg_4_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_5_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5)
               dq_dqs_tx_egress_ana_m0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_5 = dq_dqs_tx_egress_ana_m0_cfg_5_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_6_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6)
               dq_dqs_tx_egress_ana_m0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_6 = dq_dqs_tx_egress_ana_m0_cfg_6_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_7_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7)
               dq_dqs_tx_egress_ana_m0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_7 = dq_dqs_tx_egress_ana_m0_cfg_7_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m0_cfg_8_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8)
               dq_dqs_tx_egress_ana_m0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m0_cfg_8 = dq_dqs_tx_egress_ana_m0_cfg_8_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_0_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0)
               dq_dqs_tx_egress_ana_m1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_0 = dq_dqs_tx_egress_ana_m1_cfg_0_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_1_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1)
               dq_dqs_tx_egress_ana_m1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_1 = dq_dqs_tx_egress_ana_m1_cfg_1_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_2_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2)
               dq_dqs_tx_egress_ana_m1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_2 = dq_dqs_tx_egress_ana_m1_cfg_2_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_3_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3)
               dq_dqs_tx_egress_ana_m1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_3 = dq_dqs_tx_egress_ana_m1_cfg_3_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_4_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4)
               dq_dqs_tx_egress_ana_m1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_4 = dq_dqs_tx_egress_ana_m1_cfg_4_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_5_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5)
               dq_dqs_tx_egress_ana_m1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_5 = dq_dqs_tx_egress_ana_m1_cfg_5_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_6_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6)
               dq_dqs_tx_egress_ana_m1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_6 = dq_dqs_tx_egress_ana_m1_cfg_6_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_7_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7)
               dq_dqs_tx_egress_ana_m1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_7 = dq_dqs_tx_egress_ana_m1_cfg_7_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_egress_ana_m1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_ana_m1_cfg_8_q <= `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8)
               dq_dqs_tx_egress_ana_m1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_egress_ana_m1_cfg_8 = dq_dqs_tx_egress_ana_m1_cfg_8_q & `DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_0_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0)
               dq_dqs_tx_egress_dig_m0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_0 = dq_dqs_tx_egress_dig_m0_cfg_0_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_1_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1)
               dq_dqs_tx_egress_dig_m0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_1 = dq_dqs_tx_egress_dig_m0_cfg_1_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_2_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2)
               dq_dqs_tx_egress_dig_m0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_2 = dq_dqs_tx_egress_dig_m0_cfg_2_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_3_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3)
               dq_dqs_tx_egress_dig_m0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_3 = dq_dqs_tx_egress_dig_m0_cfg_3_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_4_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4)
               dq_dqs_tx_egress_dig_m0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_4 = dq_dqs_tx_egress_dig_m0_cfg_4_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_5_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5)
               dq_dqs_tx_egress_dig_m0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_5 = dq_dqs_tx_egress_dig_m0_cfg_5_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_6_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6)
               dq_dqs_tx_egress_dig_m0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_6 = dq_dqs_tx_egress_dig_m0_cfg_6_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_7_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7)
               dq_dqs_tx_egress_dig_m0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_7 = dq_dqs_tx_egress_dig_m0_cfg_7_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m0_cfg_8_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8)
               dq_dqs_tx_egress_dig_m0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m0_cfg_8 = dq_dqs_tx_egress_dig_m0_cfg_8_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_0_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0)
               dq_dqs_tx_egress_dig_m1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_0 = dq_dqs_tx_egress_dig_m1_cfg_0_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_1_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1)
               dq_dqs_tx_egress_dig_m1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_1 = dq_dqs_tx_egress_dig_m1_cfg_1_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_2_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2)
               dq_dqs_tx_egress_dig_m1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_2 = dq_dqs_tx_egress_dig_m1_cfg_2_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_3_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3)
               dq_dqs_tx_egress_dig_m1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_3 = dq_dqs_tx_egress_dig_m1_cfg_3_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_4_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4)
               dq_dqs_tx_egress_dig_m1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_4 = dq_dqs_tx_egress_dig_m1_cfg_4_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_5_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5)
               dq_dqs_tx_egress_dig_m1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_5 = dq_dqs_tx_egress_dig_m1_cfg_5_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_6_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6)
               dq_dqs_tx_egress_dig_m1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_6 = dq_dqs_tx_egress_dig_m1_cfg_6_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_7_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7)
               dq_dqs_tx_egress_dig_m1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_7 = dq_dqs_tx_egress_dig_m1_cfg_7_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_egress_dig_m1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_egress_dig_m1_cfg_8_q <= `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8)
               dq_dqs_tx_egress_dig_m1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_egress_dig_m1_cfg_8 = dq_dqs_tx_egress_dig_m1_cfg_8_q & `DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_odr_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_odr_pi_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG)
               dq_dqs_tx_odr_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_odr_pi_m0_r0_cfg = dq_dqs_tx_odr_pi_m0_r0_cfg_q & `DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_odr_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_odr_pi_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG)
               dq_dqs_tx_odr_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_odr_pi_m0_r1_cfg = dq_dqs_tx_odr_pi_m0_r1_cfg_q & `DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_odr_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_odr_pi_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG)
               dq_dqs_tx_odr_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_odr_pi_m1_r0_cfg = dq_dqs_tx_odr_pi_m1_r0_cfg_q & `DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_odr_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_odr_pi_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG)
               dq_dqs_tx_odr_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_odr_pi_m1_r1_cfg = dq_dqs_tx_odr_pi_m1_r1_cfg_q & `DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_0_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_0_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG)
               dq_dqs_tx_qdr_pi_0_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_0_m0_r0_cfg = dq_dqs_tx_qdr_pi_0_m0_r0_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_0_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_0_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG)
               dq_dqs_tx_qdr_pi_0_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_0_m0_r1_cfg = dq_dqs_tx_qdr_pi_0_m0_r1_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_0_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_0_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG)
               dq_dqs_tx_qdr_pi_0_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_0_m1_r0_cfg = dq_dqs_tx_qdr_pi_0_m1_r0_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_0_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_0_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG)
               dq_dqs_tx_qdr_pi_0_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_0_m1_r1_cfg = dq_dqs_tx_qdr_pi_0_m1_r1_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_1_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_1_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG)
               dq_dqs_tx_qdr_pi_1_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_1_m0_r0_cfg = dq_dqs_tx_qdr_pi_1_m0_r0_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_1_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_1_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG)
               dq_dqs_tx_qdr_pi_1_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_1_m0_r1_cfg = dq_dqs_tx_qdr_pi_1_m0_r1_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_1_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_1_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG)
               dq_dqs_tx_qdr_pi_1_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_1_m1_r0_cfg = dq_dqs_tx_qdr_pi_1_m1_r0_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_qdr_pi_1_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_pi_1_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG)
               dq_dqs_tx_qdr_pi_1_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_pi_1_m1_r1_cfg = dq_dqs_tx_qdr_pi_1_m1_r1_cfg_q & `DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_0_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_0_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG)
               dq_dqs_tx_ddr_pi_0_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_0_m0_r0_cfg = dq_dqs_tx_ddr_pi_0_m0_r0_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_0_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_0_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG)
               dq_dqs_tx_ddr_pi_0_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_0_m0_r1_cfg = dq_dqs_tx_ddr_pi_0_m0_r1_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_0_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_0_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG)
               dq_dqs_tx_ddr_pi_0_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_0_m1_r0_cfg = dq_dqs_tx_ddr_pi_0_m1_r0_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_0_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_0_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG)
               dq_dqs_tx_ddr_pi_0_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_0_m1_r1_cfg = dq_dqs_tx_ddr_pi_0_m1_r1_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_1_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_1_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG)
               dq_dqs_tx_ddr_pi_1_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_1_m0_r0_cfg = dq_dqs_tx_ddr_pi_1_m0_r0_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_1_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_1_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG)
               dq_dqs_tx_ddr_pi_1_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_1_m0_r1_cfg = dq_dqs_tx_ddr_pi_1_m0_r1_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_1_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_1_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG)
               dq_dqs_tx_ddr_pi_1_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_1_m1_r0_cfg = dq_dqs_tx_ddr_pi_1_m1_r0_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_ddr_pi_1_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_pi_1_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG)
               dq_dqs_tx_ddr_pi_1_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_pi_1_m1_r1_cfg = dq_dqs_tx_ddr_pi_1_m1_r1_cfg_q & `DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_pi_rt_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_pi_rt_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG)
               dq_dqs_tx_pi_rt_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_pi_rt_m0_r0_cfg = dq_dqs_tx_pi_rt_m0_r0_cfg_q & `DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_pi_rt_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_pi_rt_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG)
               dq_dqs_tx_pi_rt_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_pi_rt_m0_r1_cfg = dq_dqs_tx_pi_rt_m0_r1_cfg_q & `DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_pi_rt_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_pi_rt_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG)
               dq_dqs_tx_pi_rt_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_pi_rt_m1_r0_cfg = dq_dqs_tx_pi_rt_m1_r0_cfg_q & `DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_pi_rt_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_pi_rt_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG)
               dq_dqs_tx_pi_rt_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_pi_rt_m1_r1_cfg = dq_dqs_tx_pi_rt_m1_r1_cfg_q & `DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_sdr_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_pi_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG)
               dq_dqs_tx_sdr_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_pi_m0_r0_cfg = dq_dqs_tx_sdr_pi_m0_r0_cfg_q & `DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_sdr_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_pi_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG)
               dq_dqs_tx_sdr_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_pi_m0_r1_cfg = dq_dqs_tx_sdr_pi_m0_r1_cfg_q & `DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_sdr_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_pi_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG)
               dq_dqs_tx_sdr_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_pi_m1_r0_cfg = dq_dqs_tx_sdr_pi_m1_r0_cfg_q & `DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_sdr_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_pi_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG)
               dq_dqs_tx_sdr_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_pi_m1_r1_cfg = dq_dqs_tx_sdr_pi_m1_r1_cfg_q & `DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_dfi_pi_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_dfi_pi_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG)
               dq_dqs_tx_dfi_pi_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_dfi_pi_m0_r0_cfg = dq_dqs_tx_dfi_pi_m0_r0_cfg_q & `DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_dfi_pi_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_dfi_pi_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG)
               dq_dqs_tx_dfi_pi_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_dfi_pi_m0_r1_cfg = dq_dqs_tx_dfi_pi_m0_r1_cfg_q & `DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_dfi_pi_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_dfi_pi_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG)
               dq_dqs_tx_dfi_pi_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_dfi_pi_m1_r0_cfg = dq_dqs_tx_dfi_pi_m1_r0_cfg_q & `DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_dfi_pi_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_dfi_pi_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG)
               dq_dqs_tx_dfi_pi_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_dfi_pi_m1_r1_cfg = dq_dqs_tx_dfi_pi_m1_r1_cfg_q & `DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_rt_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_rt_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_RT_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_RT_M0_R0_CFG)
               dq_dqs_tx_rt_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_rt_m0_r0_cfg = dq_dqs_tx_rt_m0_r0_cfg_q & `DDR_DQ_DQS_TX_RT_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_rt_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_rt_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_RT_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_RT_M0_R1_CFG)
               dq_dqs_tx_rt_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_rt_m0_r1_cfg = dq_dqs_tx_rt_m0_r1_cfg_q & `DDR_DQ_DQS_TX_RT_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_rt_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_rt_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_RT_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_RT_M1_R0_CFG)
               dq_dqs_tx_rt_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_rt_m1_r0_cfg = dq_dqs_tx_rt_m1_r0_cfg_q & `DDR_DQ_DQS_TX_RT_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_rt_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_rt_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_RT_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_RT_M1_R1_CFG)
               dq_dqs_tx_rt_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_rt_m1_r1_cfg = dq_dqs_tx_rt_m1_r1_cfg_q & `DDR_DQ_DQS_TX_RT_M1_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0)
               dq_dqs_tx_sdr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_0 = dq_dqs_tx_sdr_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1)
               dq_dqs_tx_sdr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_1 = dq_dqs_tx_sdr_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2)
               dq_dqs_tx_sdr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_2 = dq_dqs_tx_sdr_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3)
               dq_dqs_tx_sdr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_3 = dq_dqs_tx_sdr_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4)
               dq_dqs_tx_sdr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_4 = dq_dqs_tx_sdr_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5)
               dq_dqs_tx_sdr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_5 = dq_dqs_tx_sdr_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6)
               dq_dqs_tx_sdr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_6 = dq_dqs_tx_sdr_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7)
               dq_dqs_tx_sdr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_7 = dq_dqs_tx_sdr_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8)
               dq_dqs_tx_sdr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r0_cfg_8 = dq_dqs_tx_sdr_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0)
               dq_dqs_tx_sdr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_0 = dq_dqs_tx_sdr_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1)
               dq_dqs_tx_sdr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_1 = dq_dqs_tx_sdr_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2)
               dq_dqs_tx_sdr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_2 = dq_dqs_tx_sdr_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3)
               dq_dqs_tx_sdr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_3 = dq_dqs_tx_sdr_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4)
               dq_dqs_tx_sdr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_4 = dq_dqs_tx_sdr_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5)
               dq_dqs_tx_sdr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_5 = dq_dqs_tx_sdr_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6)
               dq_dqs_tx_sdr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_6 = dq_dqs_tx_sdr_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7)
               dq_dqs_tx_sdr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_7 = dq_dqs_tx_sdr_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8)
               dq_dqs_tx_sdr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m0_r1_cfg_8 = dq_dqs_tx_sdr_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0)
               dq_dqs_tx_sdr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_0 = dq_dqs_tx_sdr_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1)
               dq_dqs_tx_sdr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_1 = dq_dqs_tx_sdr_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2)
               dq_dqs_tx_sdr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_2 = dq_dqs_tx_sdr_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3)
               dq_dqs_tx_sdr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_3 = dq_dqs_tx_sdr_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4)
               dq_dqs_tx_sdr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_4 = dq_dqs_tx_sdr_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5)
               dq_dqs_tx_sdr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_5 = dq_dqs_tx_sdr_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6)
               dq_dqs_tx_sdr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_6 = dq_dqs_tx_sdr_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7)
               dq_dqs_tx_sdr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_7 = dq_dqs_tx_sdr_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8)
               dq_dqs_tx_sdr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r0_cfg_8 = dq_dqs_tx_sdr_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0)
               dq_dqs_tx_sdr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_0 = dq_dqs_tx_sdr_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1)
               dq_dqs_tx_sdr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_1 = dq_dqs_tx_sdr_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2)
               dq_dqs_tx_sdr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_2 = dq_dqs_tx_sdr_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3)
               dq_dqs_tx_sdr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_3 = dq_dqs_tx_sdr_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4)
               dq_dqs_tx_sdr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_4 = dq_dqs_tx_sdr_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5)
               dq_dqs_tx_sdr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_5 = dq_dqs_tx_sdr_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6)
               dq_dqs_tx_sdr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_6 = dq_dqs_tx_sdr_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7)
               dq_dqs_tx_sdr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_7 = dq_dqs_tx_sdr_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8)
               dq_dqs_tx_sdr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_m1_r1_cfg_8 = dq_dqs_tx_sdr_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8)
               dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8 = dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8)
               dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8 = dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8)
               dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8 = dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8)
               dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8 = dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8)
               dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8 = dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8)
               dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8 = dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8)
               dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8 = dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8)
               dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8 = dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0)
               dq_dqs_tx_ddr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_0 = dq_dqs_tx_ddr_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1)
               dq_dqs_tx_ddr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_1 = dq_dqs_tx_ddr_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2)
               dq_dqs_tx_ddr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_2 = dq_dqs_tx_ddr_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3)
               dq_dqs_tx_ddr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_3 = dq_dqs_tx_ddr_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4)
               dq_dqs_tx_ddr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_4 = dq_dqs_tx_ddr_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5)
               dq_dqs_tx_ddr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_5 = dq_dqs_tx_ddr_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6)
               dq_dqs_tx_ddr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_6 = dq_dqs_tx_ddr_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7)
               dq_dqs_tx_ddr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_7 = dq_dqs_tx_ddr_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8)
               dq_dqs_tx_ddr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r0_cfg_8 = dq_dqs_tx_ddr_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0)
               dq_dqs_tx_ddr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_0 = dq_dqs_tx_ddr_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1)
               dq_dqs_tx_ddr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_1 = dq_dqs_tx_ddr_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2)
               dq_dqs_tx_ddr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_2 = dq_dqs_tx_ddr_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3)
               dq_dqs_tx_ddr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_3 = dq_dqs_tx_ddr_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4)
               dq_dqs_tx_ddr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_4 = dq_dqs_tx_ddr_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5)
               dq_dqs_tx_ddr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_5 = dq_dqs_tx_ddr_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6)
               dq_dqs_tx_ddr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_6 = dq_dqs_tx_ddr_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7)
               dq_dqs_tx_ddr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_7 = dq_dqs_tx_ddr_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8)
               dq_dqs_tx_ddr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m0_r1_cfg_8 = dq_dqs_tx_ddr_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0)
               dq_dqs_tx_ddr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_0 = dq_dqs_tx_ddr_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1)
               dq_dqs_tx_ddr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_1 = dq_dqs_tx_ddr_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2)
               dq_dqs_tx_ddr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_2 = dq_dqs_tx_ddr_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3)
               dq_dqs_tx_ddr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_3 = dq_dqs_tx_ddr_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4)
               dq_dqs_tx_ddr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_4 = dq_dqs_tx_ddr_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5)
               dq_dqs_tx_ddr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_5 = dq_dqs_tx_ddr_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6)
               dq_dqs_tx_ddr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_6 = dq_dqs_tx_ddr_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7)
               dq_dqs_tx_ddr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_7 = dq_dqs_tx_ddr_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8)
               dq_dqs_tx_ddr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r0_cfg_8 = dq_dqs_tx_ddr_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0)
               dq_dqs_tx_ddr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_0 = dq_dqs_tx_ddr_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1)
               dq_dqs_tx_ddr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_1 = dq_dqs_tx_ddr_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2)
               dq_dqs_tx_ddr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_2 = dq_dqs_tx_ddr_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3)
               dq_dqs_tx_ddr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_3 = dq_dqs_tx_ddr_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4)
               dq_dqs_tx_ddr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_4 = dq_dqs_tx_ddr_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5)
               dq_dqs_tx_ddr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_5 = dq_dqs_tx_ddr_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6)
               dq_dqs_tx_ddr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_6 = dq_dqs_tx_ddr_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7)
               dq_dqs_tx_ddr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_7 = dq_dqs_tx_ddr_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8)
               dq_dqs_tx_ddr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_m1_r1_cfg_8 = dq_dqs_tx_ddr_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8)
               dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8 = dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8)
               dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8 = dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8)
               dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8 = dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8)
               dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8 = dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0)
               dq_dqs_tx_qdr_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_0 = dq_dqs_tx_qdr_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1)
               dq_dqs_tx_qdr_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_1 = dq_dqs_tx_qdr_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2)
               dq_dqs_tx_qdr_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_2 = dq_dqs_tx_qdr_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3)
               dq_dqs_tx_qdr_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_3 = dq_dqs_tx_qdr_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4)
               dq_dqs_tx_qdr_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_4 = dq_dqs_tx_qdr_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5)
               dq_dqs_tx_qdr_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_5 = dq_dqs_tx_qdr_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6)
               dq_dqs_tx_qdr_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_6 = dq_dqs_tx_qdr_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7)
               dq_dqs_tx_qdr_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_7 = dq_dqs_tx_qdr_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8)
               dq_dqs_tx_qdr_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r0_cfg_8 = dq_dqs_tx_qdr_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0)
               dq_dqs_tx_qdr_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_0 = dq_dqs_tx_qdr_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1)
               dq_dqs_tx_qdr_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_1 = dq_dqs_tx_qdr_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2)
               dq_dqs_tx_qdr_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_2 = dq_dqs_tx_qdr_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3)
               dq_dqs_tx_qdr_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_3 = dq_dqs_tx_qdr_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4)
               dq_dqs_tx_qdr_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_4 = dq_dqs_tx_qdr_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5)
               dq_dqs_tx_qdr_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_5 = dq_dqs_tx_qdr_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6)
               dq_dqs_tx_qdr_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_6 = dq_dqs_tx_qdr_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7)
               dq_dqs_tx_qdr_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_7 = dq_dqs_tx_qdr_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8)
               dq_dqs_tx_qdr_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m0_r1_cfg_8 = dq_dqs_tx_qdr_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0)
               dq_dqs_tx_qdr_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_0 = dq_dqs_tx_qdr_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1)
               dq_dqs_tx_qdr_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_1 = dq_dqs_tx_qdr_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2)
               dq_dqs_tx_qdr_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_2 = dq_dqs_tx_qdr_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3)
               dq_dqs_tx_qdr_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_3 = dq_dqs_tx_qdr_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4)
               dq_dqs_tx_qdr_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_4 = dq_dqs_tx_qdr_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5)
               dq_dqs_tx_qdr_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_5 = dq_dqs_tx_qdr_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6)
               dq_dqs_tx_qdr_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_6 = dq_dqs_tx_qdr_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7)
               dq_dqs_tx_qdr_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_7 = dq_dqs_tx_qdr_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8)
               dq_dqs_tx_qdr_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r0_cfg_8 = dq_dqs_tx_qdr_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0)
               dq_dqs_tx_qdr_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_0 = dq_dqs_tx_qdr_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1)
               dq_dqs_tx_qdr_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_1 = dq_dqs_tx_qdr_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2)
               dq_dqs_tx_qdr_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_2 = dq_dqs_tx_qdr_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3)
               dq_dqs_tx_qdr_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_3 = dq_dqs_tx_qdr_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4)
               dq_dqs_tx_qdr_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_4 = dq_dqs_tx_qdr_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5)
               dq_dqs_tx_qdr_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_5 = dq_dqs_tx_qdr_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6)
               dq_dqs_tx_qdr_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_6 = dq_dqs_tx_qdr_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7)
               dq_dqs_tx_qdr_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_7 = dq_dqs_tx_qdr_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8)
               dq_dqs_tx_qdr_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_m1_r1_cfg_8 = dq_dqs_tx_qdr_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8)
               dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8 = dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8)
               dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8 = dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8)
               dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8 = dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7_MSK;

   logic [31:0] dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8_q <= `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8)
               dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8_q <= i_wdata;

   assign o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8 = dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8_q & `DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8_MSK;

   logic [31:0] dq_dqs_tx_lpde_m0_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m0_r0_cfg_0_q <= `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0)
               dq_dqs_tx_lpde_m0_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m0_r0_cfg_0 = dq_dqs_tx_lpde_m0_r0_cfg_0_q & `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_lpde_m0_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m0_r0_cfg_1_q <= `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1)
               dq_dqs_tx_lpde_m0_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m0_r0_cfg_1 = dq_dqs_tx_lpde_m0_r0_cfg_1_q & `DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_lpde_m0_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m0_r1_cfg_0_q <= `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0)
               dq_dqs_tx_lpde_m0_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m0_r1_cfg_0 = dq_dqs_tx_lpde_m0_r1_cfg_0_q & `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_lpde_m0_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m0_r1_cfg_1_q <= `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1)
               dq_dqs_tx_lpde_m0_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m0_r1_cfg_1 = dq_dqs_tx_lpde_m0_r1_cfg_1_q & `DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_lpde_m1_r0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m1_r0_cfg_0_q <= `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0)
               dq_dqs_tx_lpde_m1_r0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m1_r0_cfg_0 = dq_dqs_tx_lpde_m1_r0_cfg_0_q & `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_lpde_m1_r0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m1_r0_cfg_1_q <= `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1)
               dq_dqs_tx_lpde_m1_r0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m1_r0_cfg_1 = dq_dqs_tx_lpde_m1_r0_cfg_1_q & `DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_lpde_m1_r1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m1_r1_cfg_0_q <= `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0)
               dq_dqs_tx_lpde_m1_r1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m1_r1_cfg_0 = dq_dqs_tx_lpde_m1_r1_cfg_0_q & `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_lpde_m1_r1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_lpde_m1_r1_cfg_1_q <= `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1)
               dq_dqs_tx_lpde_m1_r1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_lpde_m1_r1_cfg_1 = dq_dqs_tx_lpde_m1_r1_cfg_1_q & `DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_io_m0_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_m0_cfg_0_q <= `DDR_DQ_DQS_TX_IO_M0_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_0)
               dq_dqs_tx_io_m0_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_io_m0_cfg_0 = dq_dqs_tx_io_m0_cfg_0_q & `DDR_DQ_DQS_TX_IO_M0_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_io_m0_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_m0_cfg_1_q <= `DDR_DQ_DQS_TX_IO_M0_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_1)
               dq_dqs_tx_io_m0_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_io_m0_cfg_1 = dq_dqs_tx_io_m0_cfg_1_q & `DDR_DQ_DQS_TX_IO_M0_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_io_m1_cfg_0_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_m1_cfg_0_q <= `DDR_DQ_DQS_TX_IO_M1_CFG_0_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_0)
               dq_dqs_tx_io_m1_cfg_0_q <= i_wdata;

   assign o_dq_dqs_tx_io_m1_cfg_0 = dq_dqs_tx_io_m1_cfg_0_q & `DDR_DQ_DQS_TX_IO_M1_CFG_0_MSK;

   logic [31:0] dq_dqs_tx_io_m1_cfg_1_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_m1_cfg_1_q <= `DDR_DQ_DQS_TX_IO_M1_CFG_1_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_1)
               dq_dqs_tx_io_m1_cfg_1_q <= i_wdata;

   assign o_dq_dqs_tx_io_m1_cfg_1 = dq_dqs_tx_io_m1_cfg_1_q & `DDR_DQ_DQS_TX_IO_M1_CFG_1_MSK;

   logic [31:0] dq_dqs_tx_io_cmn_m0_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_cmn_m0_r0_cfg_q <= `DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG)
               dq_dqs_tx_io_cmn_m0_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_io_cmn_m0_r0_cfg = dq_dqs_tx_io_cmn_m0_r0_cfg_q & `DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_io_cmn_m0_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_cmn_m0_r1_cfg_q <= `DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG)
               dq_dqs_tx_io_cmn_m0_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_io_cmn_m0_r1_cfg = dq_dqs_tx_io_cmn_m0_r1_cfg_q & `DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG_MSK;

   logic [31:0] dq_dqs_tx_io_cmn_m1_r0_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_cmn_m1_r0_cfg_q <= `DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG)
               dq_dqs_tx_io_cmn_m1_r0_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_io_cmn_m1_r0_cfg = dq_dqs_tx_io_cmn_m1_r0_cfg_q & `DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG_MSK;

   logic [31:0] dq_dqs_tx_io_cmn_m1_r1_cfg_q;
   always_ff @( posedge i_hclk, posedge i_hreset)
      if (i_hreset)
         dq_dqs_tx_io_cmn_m1_r1_cfg_q <= `DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG_POR;
      else
         if (i_write)
            if (decode == DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG)
               dq_dqs_tx_io_cmn_m1_r1_cfg_q <= i_wdata;

   assign o_dq_dqs_tx_io_cmn_m1_r1_cfg = dq_dqs_tx_io_cmn_m1_r1_cfg_q & `DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG_MSK;

   always_comb
      if (i_read)
         case (decode)
            DECODE_DDR_DQ_TOP_CFG : o_rdata = o_dq_top_cfg;
            DECODE_DDR_DQ_TOP_STA : o_rdata = dq_top_sta_q;
            DECODE_DDR_DQ_DQ_RX_BSCAN_STA : o_rdata = dq_dq_rx_bscan_sta_q;
            DECODE_DDR_DQ_DQ_RX_M0_CFG : o_rdata = o_dq_dq_rx_m0_cfg;
            DECODE_DDR_DQ_DQ_RX_M1_CFG : o_rdata = o_dq_dq_rx_m1_cfg;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_0 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_1 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_2 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_3 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_4 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_5 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_6 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_7 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R0_CFG_8 : o_rdata = o_dq_dq_rx_io_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_0 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_1 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_2 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_3 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_4 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_5 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_6 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_7 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_IO_M0_R1_CFG_8 : o_rdata = o_dq_dq_rx_io_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_0 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_1 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_2 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_3 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_4 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_5 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_6 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_7 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R0_CFG_8 : o_rdata = o_dq_dq_rx_io_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_0 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_1 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_2 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_3 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_4 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_5 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_6 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_7 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_IO_M1_R1_CFG_8 : o_rdata = o_dq_dq_rx_io_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_IO_STA : o_rdata = dq_dq_rx_io_sta_q;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_0 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_1 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_2 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_3 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_4 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_5 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_6 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_7 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R0_CFG_8 : o_rdata = o_dq_dq_rx_sa_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_0 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_1 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_2 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_3 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_4 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_5 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_6 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_7 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_M0_R1_CFG_8 : o_rdata = o_dq_dq_rx_sa_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_0 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_1 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_2 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_3 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_4 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_5 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_6 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_7 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R0_CFG_8 : o_rdata = o_dq_dq_rx_sa_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_0 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_1 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_2 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_3 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_4 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_5 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_6 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_7 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_M1_R1_CFG_8 : o_rdata = o_dq_dq_rx_sa_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8 : o_rdata = o_dq_dq_rx_sa_dly_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8 : o_rdata = o_dq_dq_rx_sa_dly_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8 : o_rdata = o_dq_dq_rx_sa_dly_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8 : o_rdata = o_dq_dq_rx_sa_dly_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_RX_SA_STA_0 : o_rdata = dq_dq_rx_sa_sta_0_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_1 : o_rdata = dq_dq_rx_sa_sta_1_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_2 : o_rdata = dq_dq_rx_sa_sta_2_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_3 : o_rdata = dq_dq_rx_sa_sta_3_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_4 : o_rdata = dq_dq_rx_sa_sta_4_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_5 : o_rdata = dq_dq_rx_sa_sta_5_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_6 : o_rdata = dq_dq_rx_sa_sta_6_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_7 : o_rdata = dq_dq_rx_sa_sta_7_q;
            DECODE_DDR_DQ_DQ_RX_SA_STA_8 : o_rdata = dq_dq_rx_sa_sta_8_q;
            DECODE_DDR_DQ_DQ_TX_BSCAN_CFG : o_rdata = o_dq_dq_tx_bscan_cfg;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8 : o_rdata = o_dq_dq_tx_egress_ana_m0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8 : o_rdata = o_dq_dq_tx_egress_ana_m1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8 : o_rdata = o_dq_dq_tx_egress_dig_m0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8 : o_rdata = o_dq_dq_tx_egress_dig_m1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R0_CFG : o_rdata = o_dq_dq_tx_odr_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_ODR_PI_M0_R1_CFG : o_rdata = o_dq_dq_tx_odr_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R0_CFG : o_rdata = o_dq_dq_tx_odr_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_ODR_PI_M1_R1_CFG : o_rdata = o_dq_dq_tx_odr_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG : o_rdata = o_dq_dq_tx_qdr_pi_0_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG : o_rdata = o_dq_dq_tx_qdr_pi_0_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG : o_rdata = o_dq_dq_tx_qdr_pi_0_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG : o_rdata = o_dq_dq_tx_qdr_pi_0_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG : o_rdata = o_dq_dq_tx_qdr_pi_1_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG : o_rdata = o_dq_dq_tx_qdr_pi_1_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG : o_rdata = o_dq_dq_tx_qdr_pi_1_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG : o_rdata = o_dq_dq_tx_qdr_pi_1_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG : o_rdata = o_dq_dq_tx_ddr_pi_0_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG : o_rdata = o_dq_dq_tx_ddr_pi_0_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG : o_rdata = o_dq_dq_tx_ddr_pi_0_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG : o_rdata = o_dq_dq_tx_ddr_pi_0_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG : o_rdata = o_dq_dq_tx_ddr_pi_1_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG : o_rdata = o_dq_dq_tx_ddr_pi_1_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG : o_rdata = o_dq_dq_tx_ddr_pi_1_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG : o_rdata = o_dq_dq_tx_ddr_pi_1_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG : o_rdata = o_dq_dq_tx_pi_rt_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG : o_rdata = o_dq_dq_tx_pi_rt_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG : o_rdata = o_dq_dq_tx_pi_rt_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG : o_rdata = o_dq_dq_tx_pi_rt_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_RT_M0_R0_CFG : o_rdata = o_dq_dq_tx_rt_m0_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_RT_M0_R1_CFG : o_rdata = o_dq_dq_tx_rt_m0_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_RT_M1_R0_CFG : o_rdata = o_dq_dq_tx_rt_m1_r0_cfg;
            DECODE_DDR_DQ_DQ_TX_RT_M1_R1_CFG : o_rdata = o_dq_dq_tx_rt_m1_r1_cfg;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_sdr_fc_dly_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_ddr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_ddr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_ddr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_ddr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_ddr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_ddr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_qdr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_qdr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_qdr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_qdr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_qdr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_qdr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8 : o_rdata = o_dq_dq_tx_lpde_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8 : o_rdata = o_dq_dq_tx_lpde_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8 : o_rdata = o_dq_dq_tx_lpde_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8 : o_rdata = o_dq_dq_tx_lpde_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_0 : o_rdata = o_dq_dq_tx_io_m0_cfg_0;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_1 : o_rdata = o_dq_dq_tx_io_m0_cfg_1;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_2 : o_rdata = o_dq_dq_tx_io_m0_cfg_2;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_3 : o_rdata = o_dq_dq_tx_io_m0_cfg_3;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_4 : o_rdata = o_dq_dq_tx_io_m0_cfg_4;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_5 : o_rdata = o_dq_dq_tx_io_m0_cfg_5;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_6 : o_rdata = o_dq_dq_tx_io_m0_cfg_6;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_7 : o_rdata = o_dq_dq_tx_io_m0_cfg_7;
            DECODE_DDR_DQ_DQ_TX_IO_M0_CFG_8 : o_rdata = o_dq_dq_tx_io_m0_cfg_8;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_0 : o_rdata = o_dq_dq_tx_io_m1_cfg_0;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_1 : o_rdata = o_dq_dq_tx_io_m1_cfg_1;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_2 : o_rdata = o_dq_dq_tx_io_m1_cfg_2;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_3 : o_rdata = o_dq_dq_tx_io_m1_cfg_3;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_4 : o_rdata = o_dq_dq_tx_io_m1_cfg_4;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_5 : o_rdata = o_dq_dq_tx_io_m1_cfg_5;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_6 : o_rdata = o_dq_dq_tx_io_m1_cfg_6;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_7 : o_rdata = o_dq_dq_tx_io_m1_cfg_7;
            DECODE_DDR_DQ_DQ_TX_IO_M1_CFG_8 : o_rdata = o_dq_dq_tx_io_m1_cfg_8;
            DECODE_DDR_DQ_DQS_RX_M0_CFG : o_rdata = o_dq_dqs_rx_m0_cfg;
            DECODE_DDR_DQ_DQS_RX_M1_CFG : o_rdata = o_dq_dqs_rx_m1_cfg;
            DECODE_DDR_DQ_DQS_RX_BSCAN_STA : o_rdata = dq_dqs_rx_bscan_sta_q;
            DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG : o_rdata = o_dq_dqs_rx_sdr_lpde_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG : o_rdata = o_dq_dqs_rx_sdr_lpde_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG : o_rdata = o_dq_dqs_rx_sdr_lpde_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG : o_rdata = o_dq_dqs_rx_sdr_lpde_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG : o_rdata = o_dq_dqs_rx_ren_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG : o_rdata = o_dq_dqs_rx_ren_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG : o_rdata = o_dq_dqs_rx_ren_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG : o_rdata = o_dq_dqs_rx_ren_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG : o_rdata = o_dq_dqs_rx_rcs_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG : o_rdata = o_dq_dqs_rx_rcs_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG : o_rdata = o_dq_dqs_rx_rcs_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG : o_rdata = o_dq_dqs_rx_rcs_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_0_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_0_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_0_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_0_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_1_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_1_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_1_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG : o_rdata = o_dq_dqs_rx_rdqs_pi_1_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_PI_STA : o_rdata = dq_dqs_rx_pi_sta_q;
            DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_0 : o_rdata = o_dq_dqs_rx_io_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_RX_IO_M0_R0_CFG_1 : o_rdata = o_dq_dqs_rx_io_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_0 : o_rdata = o_dq_dqs_rx_io_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_RX_IO_M0_R1_CFG_1 : o_rdata = o_dq_dqs_rx_io_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_0 : o_rdata = o_dq_dqs_rx_io_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_RX_IO_M1_R0_CFG_1 : o_rdata = o_dq_dqs_rx_io_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_0 : o_rdata = o_dq_dqs_rx_io_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_RX_IO_M1_R1_CFG_1 : o_rdata = o_dq_dqs_rx_io_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG : o_rdata = o_dq_dqs_rx_io_cmn_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG : o_rdata = o_dq_dqs_rx_io_cmn_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG : o_rdata = o_dq_dqs_rx_io_cmn_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG : o_rdata = o_dq_dqs_rx_io_cmn_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_RX_IO_STA : o_rdata = dq_dqs_rx_io_sta_q;
            DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_0 : o_rdata = o_dq_dqs_rx_sa_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_RX_SA_M0_R0_CFG_1 : o_rdata = o_dq_dqs_rx_sa_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_0 : o_rdata = o_dq_dqs_rx_sa_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_RX_SA_M0_R1_CFG_1 : o_rdata = o_dq_dqs_rx_sa_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_0 : o_rdata = o_dq_dqs_rx_sa_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_RX_SA_M1_R0_CFG_1 : o_rdata = o_dq_dqs_rx_sa_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_0 : o_rdata = o_dq_dqs_rx_sa_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_RX_SA_M1_R1_CFG_1 : o_rdata = o_dq_dqs_rx_sa_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_RX_SA_CMN_CFG : o_rdata = o_dq_dqs_rx_sa_cmn_cfg;
            DECODE_DDR_DQ_DQS_TX_M0_CFG : o_rdata = o_dq_dqs_tx_m0_cfg;
            DECODE_DDR_DQ_DQS_TX_M1_CFG : o_rdata = o_dq_dqs_tx_m1_cfg;
            DECODE_DDR_DQ_DQS_TX_BSCAN_CTRL_CFG : o_rdata = o_dq_dqs_tx_bscan_ctrl_cfg;
            DECODE_DDR_DQ_DQS_TX_BSCAN_CFG : o_rdata = o_dq_dqs_tx_bscan_cfg;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8 : o_rdata = o_dq_dqs_tx_egress_ana_m0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8 : o_rdata = o_dq_dqs_tx_egress_ana_m1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8 : o_rdata = o_dq_dqs_tx_egress_dig_m0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8 : o_rdata = o_dq_dqs_tx_egress_dig_m1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R0_CFG : o_rdata = o_dq_dqs_tx_odr_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_ODR_PI_M0_R1_CFG : o_rdata = o_dq_dqs_tx_odr_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R0_CFG : o_rdata = o_dq_dqs_tx_odr_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_ODR_PI_M1_R1_CFG : o_rdata = o_dq_dqs_tx_odr_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_0_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_0_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_0_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_0_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_1_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_1_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_1_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG : o_rdata = o_dq_dqs_tx_qdr_pi_1_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_0_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_0_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_0_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_0_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_1_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_1_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_1_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG : o_rdata = o_dq_dqs_tx_ddr_pi_1_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG : o_rdata = o_dq_dqs_tx_pi_rt_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG : o_rdata = o_dq_dqs_tx_pi_rt_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG : o_rdata = o_dq_dqs_tx_pi_rt_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG : o_rdata = o_dq_dqs_tx_pi_rt_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG : o_rdata = o_dq_dqs_tx_sdr_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG : o_rdata = o_dq_dqs_tx_sdr_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG : o_rdata = o_dq_dqs_tx_sdr_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG : o_rdata = o_dq_dqs_tx_sdr_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG : o_rdata = o_dq_dqs_tx_dfi_pi_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG : o_rdata = o_dq_dqs_tx_dfi_pi_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG : o_rdata = o_dq_dqs_tx_dfi_pi_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG : o_rdata = o_dq_dqs_tx_dfi_pi_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_RT_M0_R0_CFG : o_rdata = o_dq_dqs_tx_rt_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_RT_M0_R1_CFG : o_rdata = o_dq_dqs_tx_rt_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_RT_M1_R0_CFG : o_rdata = o_dq_dqs_tx_rt_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_RT_M1_R1_CFG : o_rdata = o_dq_dqs_tx_rt_m1_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_sdr_fc_dly_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_ddr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m0_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r0_cfg_8;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_2;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_3;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_4;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_5;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_6;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_7;
            DECODE_DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 : o_rdata = o_dq_dqs_tx_qdr_x_sel_m1_r1_cfg_8;
            DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0 : o_rdata = o_dq_dqs_tx_lpde_m0_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1 : o_rdata = o_dq_dqs_tx_lpde_m0_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0 : o_rdata = o_dq_dqs_tx_lpde_m0_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1 : o_rdata = o_dq_dqs_tx_lpde_m0_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0 : o_rdata = o_dq_dqs_tx_lpde_m1_r0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1 : o_rdata = o_dq_dqs_tx_lpde_m1_r0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0 : o_rdata = o_dq_dqs_tx_lpde_m1_r1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1 : o_rdata = o_dq_dqs_tx_lpde_m1_r1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_0 : o_rdata = o_dq_dqs_tx_io_m0_cfg_0;
            DECODE_DDR_DQ_DQS_TX_IO_M0_CFG_1 : o_rdata = o_dq_dqs_tx_io_m0_cfg_1;
            DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_0 : o_rdata = o_dq_dqs_tx_io_m1_cfg_0;
            DECODE_DDR_DQ_DQS_TX_IO_M1_CFG_1 : o_rdata = o_dq_dqs_tx_io_m1_cfg_1;
            DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG : o_rdata = o_dq_dqs_tx_io_cmn_m0_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG : o_rdata = o_dq_dqs_tx_io_cmn_m0_r1_cfg;
            DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG : o_rdata = o_dq_dqs_tx_io_cmn_m1_r0_cfg;
            DECODE_DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG : o_rdata = o_dq_dqs_tx_io_cmn_m1_r1_cfg;
            default : o_rdata = '0;
         endcase
      else
         o_rdata = '0;

endmodule
