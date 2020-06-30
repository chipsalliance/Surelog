//////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2017 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2018.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       Configuration Simulation Model
// /___/   /\     Filename    : SIM_CONFIGE3.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//     10/31/12 - Initial version
//     09/09/13 - Fixed output IDCODE (CR 727695).
//     10/23/13 - Fixed IDCODE when ICAP_WIDTH = X16 (CR 737079).
//     02/14/14 - Fixed Non-Continous data loading problem (CR 690809).
//     05/28/14 - New simulation library message format.
// End Revision
////////////////////////////////////////////////////////////////////////////////

`timescale  1 ps / 1 ps

`celldefine

module SIM_CONFIGE3 #( 
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter DEVICE_ID = 32'h0,
  parameter ICAP_SUPPORT = "FALSE",
  parameter ICAP_WIDTH = "X8"
) (
  output AVAIL,
  output CSOB,
  output PRDONE,
  output PRERROR,
  inout  DONE,
  input  CCLK,
  input  CSB,
  inout  [31:0] D,
  inout  INITB,
  input  [2:0] M,
  input  PROGB,
  input  RDWRB
);

  localparam FRAME_RBT_OUT_FILENAME = "frame_data_e2_rbt_out.txt";
  localparam cfg_Tprog = 250000;   // min PROG must be low
  localparam cfg_Tpl =   100000;  // max program latency us.
  localparam STARTUP_PH0 = 3'b000;
  localparam STARTUP_PH1 = 3'b001;
  localparam STARTUP_PH2 = 3'b010;
  localparam STARTUP_PH3 = 3'b011;
  localparam STARTUP_PH4 = 3'b100;
  localparam STARTUP_PH5 = 3'b101;
  localparam STARTUP_PH6 = 3'b110;
  localparam STARTUP_PH7 = 3'b111;

//  tri0 GSR, GTS, GWE;

  wire GSR;
  wire GTS;
  wire GWE;
  wire cclk_in;
  wire init_b_in;
  wire prog_b_in;
  wire rdwr_b_in;
  reg rdwr_b_in1;
  reg checka_en;
  reg init_b_out;
  reg [3:0] done_o;
  integer frame_data_fd;
  integer farn;
  integer ib;
  integer ib_skp, ci, bi;
  reg frame_data_wen;
  
  tri1 p_up;

  reg por_b;
  wire [2:0] m_in;
  wire [31:0] d_in;
  wire [31:0] d_out;
  wire busy_out;
  wire cso_b_out;
  wire csi_b_in;
  reg  csi_b_ins;
  wire d_out_en;
  wire pll_locked;
  reg  pll_lockwt;
  wire init_b_t;
  wire prog_b_t;
  wire bus_en;
  wire [3:0] desync_flag;
  wire [3:0] crc_rst;
  reg  [3:0] crc_bypass;
  reg icap_on;
  reg icap_clr;
  reg icap_sync;
  reg icap_desynch;
  reg rd_desynch;
  reg rd_desynch_tmp;
  reg icap_init_done;
  reg icap_init_done_dly;
  wire [3:0] desynch_set1;
  reg [1:0] icap_bw;

//  assign DONE = p_up;
//  assign INITB = p_up;
  assign (strong1, weak0) glbl.GSR = GSR;
  assign (strong1, weak0) glbl.GTS = GTS;
  assign glbl.PROGB_GLBL = PROGB;
  assign pll_locked =  (glbl.PLL_LOCKG === 0) ? 0 : 1;
  
  buf buf_cso (CSOB, cso_b_out);
  buf buf_cclk (cclk_in, CCLK);
  buf buf_cs (csi_b_in, CSB);

  buf buf_din[31:0] (d_in, D);
  bufif1 buf_dout[31:0] (D, d_out, d_out_en);
 
  buf buf_init (init_b_in, INITB);
  buf buf_m_0  (m_in[0], M[0]);
  buf buf_m_1  (m_in[1], M[1]);
  buf buf_m_2  (m_in[2], M[2]);
  buf buf_prog (prog_b_in, PROGB);
  buf buf_rw (rdwr_b_in, RDWRB);

  time  prog_pulse_low_edge;
  time  prog_pulse_low;
  reg  mode_sample_flag;
  reg  [3:0] buswid_flag_init;
  reg  [3:0] buswid_flag;
  reg [1:0] buswidth[3:0];
  wire [1:0] buswidth_ibtmp;
  reg [1:0] buswidth_tmp[3:0];
  reg [31:0]  pack_in_reg[3:0];
  reg [31:0]  pack_in_reg_tmp0;
  reg [31:0]  pack_in_reg_tmps0;
  reg [31:0]  pack_in_reg_tmp;
  reg  [4:0] reg_addr[3:0];
  reg  [4:0] reg_addr_tmp;
  reg  [3:0] new_data_in_flag;
  reg  [3:0] wr_flag;
  reg  [3:0] rd_flag;
  reg  [3:0] cmd_wr_flag;
  reg  [3:0] cmd_reg_new_flag;
  reg  [3:0] cmd_rd_flag;
  reg  [3:0] bus_sync_flag;
  reg  [3:0] conti_data_flag;
  integer  wr_cnt[3:0];
  integer  conti_data_cnt[3:0];
  integer  rd_data_cnt[3:0];
  integer  abort_cnt;
  reg  [2:0] st_state0;
  reg  [2:0] st_state1;
  reg  [2:0] st_state2;
  reg  [2:0] st_state3;
  reg  [2:0] st_state0i;
  reg  [2:0] st_state1i;
  reg  [2:0] st_state2i;
  reg  [2:0] st_state3i;
  reg  startup_begin_flag0;
  reg  startup_end_flag0;
  reg  startup_begin_flag1;
  reg  startup_end_flag1;
  reg  startup_begin_flag2;
  reg  startup_end_flag2;
  reg  startup_begin_flag3;
  reg  startup_end_flag3;
  reg  [3:0] crc_ck;
  reg  [3:0] crc_ck_en;
  reg [3:0] crc_err_flag;
  wire [3:0] crc_err_flag_tot;
  reg [3:0] crc_err_flag_reg;
  wire  [3:0] crc_en;
  reg  [31:0] crc_curr[3:0];
  reg  [31:0] crc_curr_tmp;
  wire  [31:0] crc_curr_cktmp;
  reg  [31:0] crc_new;
  reg  [36:0] crc_input;
  reg  [31:0] rbcrc_curr[3:0];
  reg  [31:0] rbcrc_new;
  reg  [36:0] rbcrc_input;
  reg  [3:0] gwe_out;
  reg  [3:0] gts_out;
  reg  [31:0] d_o;
  reg  [31:0] outbus;
  reg  [31:0] outbus_dly;
  reg  [31:0] outbus_dly1;
  reg  busy_o;
  reg [31:0] tmp_val1;
  reg [31:0] tmp_val2;
  reg  [31:0] crc_reg[3:0];
  reg  [31:0] crc_reg_tmp;
  wire  [31:0] crc_reg_cktmp;
  reg  [31:0] far_reg[3:0];
  reg  [31:0] far_addr;
  reg  [31:0] fdri_reg[3:0];
  reg  [31:0] fdro_reg[3:0];
  reg  [4:0] cmd_reg[3:0];
  reg [31:0] ctl0_reg[3:0];
  reg  [31:0] mask_reg[3:0];
  wire [31:0] stat_reg[3:0];
  wire [31:0] stat_reg_tmp0;
  wire [31:0] stat_reg_tmp1;
  wire [31:0] stat_reg_tmp2;
  wire [31:0] stat_reg_tmp3;
  reg  [31:0] lout_reg[3:0];
  reg [31:0] cor0_reg[3:0];
  reg [31:0] cor0_reg_tmp0;
  reg [31:0] cor0_reg_tmp1;
  reg [31:0] cor0_reg_tmp2;
  reg [31:0] cor0_reg_tmp3;
  reg  [31:0] mfwr_reg[3:0];
  reg  [31:0] cbc_reg[3:0];
  reg  [31:0] idcode_reg[3:0];
  reg  [31:0] axss_reg[3:0];
  reg [31:0] cor1_reg[3:0];
  reg [31:0] cor1_reg_tmp0;
  reg [31:0] cor1_reg_tmp1;
  reg [31:0] cor1_reg_tmp2;
  reg [31:0] cor1_reg_tmp3;
  reg  [31:0] csob_reg[3:0];
  reg [31:0] wbstar_reg[3:0];
  reg [31:0] timer_reg[3:0];
  reg [31:0] rbcrc_hw_reg[3:0];
  reg [31:0] rbcrc_sw_reg[3:0];
  reg [31:0] rbcrc_live_reg[3:0];
  reg [31:0] efar_reg[3:0];
  reg [31:0] bootsts_reg[3:0];
  reg  [31:0] ctl1_reg[3:0];
  reg  [31:0] testmode_reg[3:0];
  reg  [31:0] memrd_param_reg[3:0];
  reg  [31:0] dwc_reg[3:0];
  reg  [31:0] trim_reg[3:0];
  reg  [31:0] bout_reg[3:0];
  reg  [31:0] bspi_reg[3:0];
  reg  [2:0] mode_pin_in;
  reg  [2:0] mode_reg;
  reg  [3:0] crc_reset;
  reg  [3:0] gsr_set;
  reg  [3:0] gts_usr_b;
  reg  [3:0] done_pin_drv;
  
  reg  [3:0] shutdown_set;
  reg  [3:0] desynch_set;
  reg  [2:0] done_cycle_reg0;
  reg  [2:0] done_cycle_reg1;
  reg  [2:0] done_cycle_reg2;
  reg  [2:0] done_cycle_reg3;
  reg  [2:0] gts_cycle_reg0;
  reg  [2:0] gts_cycle_reg1;
  reg  [2:0] gts_cycle_reg2;
  reg  [2:0] gts_cycle_reg3;
  reg  [2:0] gwe_cycle_reg0;
  reg  [2:0] gwe_cycle_reg1;
  reg  [2:0] gwe_cycle_reg2;
  reg  [2:0] gwe_cycle_reg3;
  reg  init_pin;
  reg  init_rst;
  reg  [2:0] nx_st_state0;
  reg  [2:0] nx_st_state1;
  reg  [2:0] nx_st_state2;
  reg  [2:0] nx_st_state3;
  reg  [3:0] ghigh_b;
  reg  [3:0] gts_cfg_b;
  reg  [3:0] eos_startup;
  reg [3:0] startup_set;
  reg [1:0] startup_set_pulse0;
  reg [1:0] startup_set_pulse1;
  reg [1:0] startup_set_pulse2;
  reg [1:0] startup_set_pulse3;
  reg abort_out_en;
  reg [31:0] tmp_dword;
  reg [15:0] tmp_word;
  reg [7:0] tmp_byte;
  reg [3:0] id_error_flag;
  wire  id_error_flag_t;
  reg [3:0] iprog_b;
  wire   iprog_b_t;
  reg [3:0] i_init_b_cmd;
  wire i_init_b_cmd_t;
  reg i_init_b;
  reg [7:0] abort_status;
  reg [3:0] persist_en;
  reg [3:0] rst_sync;
  reg [3:0] abort_dis;
  reg [2:0] lock_cycle_reg0;
  reg [2:0] lock_cycle_reg1;
  reg [2:0] lock_cycle_reg2;
  reg [2:0] lock_cycle_reg3;
  reg [3:0] rbcrc_no_pin;
  reg abort_flag_rst;
  reg [3:0] gsr_st_out;
  reg [3:0] gsr_cmd_out;
  reg [3:0] gsr_cmd_out_pulse;
  reg d_o_en;
  wire rst_intl;
  wire  rw_en_tmp1;
  wire  [3:0] rw_en;
  wire [3:0] gsr_out;
  wire [3:0] cfgerr_b_flag;
  reg  [3:0] abort_flag;
  integer downcont_cnt;
  reg rst_en;
  reg prog_b_a;
  reg [3:0] csbo_flag;
  reg [3:0] bout_flag;
  reg [3:0] bout_flags;
  reg [3:0] bout_bf;
  reg [3:0] bout_en;
  reg rd_sw_en;
  integer csbo_cnt[3:0];
  integer   bout_cnt[3:0];
  integer  bout_cnt_tmp;
  reg [4:0] rd_reg_addr[3:0];
  reg done_release;

  wire iprog_b_0;
  wire iprog_b_1;
  wire iprog_b_2;
  wire iprog_b_3;
  wire i_init_b_cmd_0;
  wire i_init_b_cmd_1;
  wire i_init_b_cmd_2;
  wire i_init_b_cmd_3;
  wire rw_en_tmp;
  wire desync_flag_t;
  wire abort_dis_bi;
    
  assign (weak1, strong0) INITB=(mode_sample_flag) ? ~crc_err_flag_tot[ib] : init_b_out;

  assign (weak1, strong0) DONE =  (done_o[0] !== 1'b0) &&
                                  ((bout_en[1] == 0) || (done_o[1] !== 1'b0)) &&
                                  ((bout_en[2] == 0) || (done_o[2] !== 1'b0)) &&
                                  ((bout_en[3] == 0) || (done_o[3] !== 1'b0));
//
//  assign (weak1, strong0) DONE=  (bout_en[1] == 0) || done_o[1];
//  assign (weak1, strong0) DONE=  (bout_en[2] == 0) || done_o[2];
//  assign (weak1, strong0) DONE=  (bout_en[3] == 0) || done_o[3];


  reg PRDONE_out;
  assign PRDONE = PRDONE_out;

  reg fdri_rst_prdone_flag;
  localparam MODULE_NAME = "SIM_CONFIGE3";
   
  always @(fdri_rst_prdone_flag or desync_flag or eos_startup)
      if (fdri_rst_prdone_flag) begin
        PRDONE_out = 1'b0;
      end else if ((&desync_flag) & (&eos_startup)) begin
        PRDONE_out = 1'b1;
      end

  assign PRERROR = (|rw_en) & (|crc_err_flag_tot);

  initial begin
    if (DEVICE_ID == "036A2093" || DEVICE_ID == "03702093")
       bout_en = 4'b0011;
    else if (DEVICE_ID == "036A4093" || DEVICE_ID == "03704093")
       bout_en = 4'b0111;
    else if (DEVICE_ID == "036A6093")
       bout_en = 4'b1111;
    else
       bout_en = 4'b0001;
  end

  

  initial begin
    buswidth_tmp[0] = 2'b00;
    buswidth_tmp[1] = 2'b00;
    buswidth_tmp[2] = 2'b00;
    buswidth_tmp[3] = 2'b00;
    pack_in_reg[0]  = 32'b0;
    pack_in_reg[1]  = 32'b0;
    pack_in_reg[2]  = 32'b0;
    pack_in_reg[3]  = 32'b0;
    pack_in_reg_tmp0  = 32'b0;
    pack_in_reg_tmps0  = 32'b0;
    pack_in_reg_tmp  = 32'b0;
    crc_curr[0] = 32'b0;
    crc_curr[1] = 32'b0;
    crc_curr[2] = 32'b0;
    crc_curr[3] = 32'b0;
    rbcrc_curr[0] = 32'b0;
    rbcrc_curr[1] = 32'b0;
    rbcrc_curr[2] = 32'b0;
    rbcrc_curr[3] = 32'b0;
    ctl0_reg[0] = 32'b000xxxxxxxxxxxxxx000000100000xx1;
    ctl0_reg[1] = 32'b000xxxxxxxxxxxxxx000000100000xx1;
    ctl0_reg[2] = 32'b000xxxxxxxxxxxxxx000000100000xx1;
    ctl0_reg[3] = 32'b000xxxxxxxxxxxxxx000000100000xx1;
    cor0_reg[0] = 32'b00000000000000000011111111101100;
    cor0_reg[1] = 32'b00000000000000000011111111101100;
    cor0_reg[2] = 32'b00000000000000000011111111101100;
    cor0_reg[3] = 32'b00000000000000000011111111101100;
    cor0_reg_tmp0 = cor0_reg[0];
    cor0_reg_tmp1 = cor0_reg[1];
    cor0_reg_tmp2 = cor0_reg[2];
    cor0_reg_tmp3 = cor0_reg[3];
    done_cycle_reg0 = cor0_reg_tmp0[14:12];
    lock_cycle_reg0 = cor0_reg_tmp0[8:6];
    done_cycle_reg1 = cor0_reg_tmp0[14:12];
    lock_cycle_reg1 = cor0_reg_tmp0[8:6];
    done_cycle_reg2 = cor0_reg_tmp0[14:12];
    lock_cycle_reg2 = cor0_reg_tmp0[8:6];
    done_cycle_reg3 = cor0_reg_tmp0[14:12];
    lock_cycle_reg3 = cor0_reg_tmp0[8:6];
    cor1_reg[0] = 32'b0;
    cor1_reg[1] = 32'b0;
    cor1_reg[2] = 32'b0;
    cor1_reg[3] = 32'b0;
    cor1_reg_tmp0 = 32'b0;
    cor1_reg_tmp1 = 32'b0;
    cor1_reg_tmp2 = 32'b0;
    cor1_reg_tmp3 = 32'b0;
    wbstar_reg[0] = 32'b0;
    wbstar_reg[1] = 32'b0;
    wbstar_reg[2] = 32'b0;
    wbstar_reg[3] = 32'b0;
    timer_reg[0] = 32'b0;
    timer_reg[1] = 32'b0;
    timer_reg[2] = 32'b0;
    timer_reg[3] = 32'b0;
    bootsts_reg[0] = 32'b0;
    bootsts_reg[1] = 32'b0;
    bootsts_reg[2] = 32'b0;
    bootsts_reg[3] = 32'b0;
    ctl1_reg[0] = 32'b0;
    ctl1_reg[1] = 32'b0;
    ctl1_reg[2] = 32'b0;
    ctl1_reg[3] = 32'b0;
    testmode_reg[0] = 32'b0;
    testmode_reg[1] = 32'b0;
    testmode_reg[2] = 32'b0;
    testmode_reg[3] = 32'b0;
    memrd_param_reg[0] = 32'b0;
    memrd_param_reg[1] = 32'b0;
    memrd_param_reg[2] = 32'b0;
    memrd_param_reg[3] = 32'b0;
    dwc_reg[0] = 32'b0;
    dwc_reg[1] = 32'b0;
    dwc_reg[2] = 32'b0;
    dwc_reg[3] = 32'b0;
    trim_reg[0] = 32'b0;
    trim_reg[1] = 32'b0;
    trim_reg[2] = 32'b0;
    trim_reg[3] = 32'b0;
    bout_reg[0] = 32'b0;
    bout_reg[1] = 32'b0;
    bout_reg[2] = 32'b0;
    bout_reg[3] = 32'b0;
    bspi_reg[0] = 32'h000B;
    bspi_reg[1] = 32'h000B;
    bspi_reg[2] = 32'h000B;
    bspi_reg[3] = 32'h000B;
    rd_reg_addr[0] = 5'b0;
    rd_reg_addr[1] = 5'b0;
    rd_reg_addr[2] = 5'b0;
    rd_reg_addr[3] = 5'b0;
    wr_cnt[0] = 0;
    wr_cnt[1] = 0;
    wr_cnt[2] = 0;
    wr_cnt[3] = 0;
    bout_cnt[0] = 0;
    bout_cnt[1] = 0;
    bout_cnt[2] = 0;
    bout_cnt[3] = 0;
    done_o = 4'b0;
    checka_en = 1'b0;
    init_b_out = 1'b1;
    farn = 0;
    ib = 0;
    csi_b_ins = 1'b1;
    crc_bypass = 4'b0000;
    icap_clr = 1'b0;
    icap_desynch = 1'b0;
    rd_desynch = 1'b0;
    rd_desynch_tmp = 1'b0;
    icap_init_done = 1'b0;
    icap_init_done_dly = 1'b0;
    prog_pulse_low_edge = 0;
    prog_pulse_low = 0;
    mode_sample_flag = 1'b0;
    buswid_flag_init = 4'b0000;
    buswid_flag = 4'b0000;
    new_data_in_flag  = 4'b0000;
    wr_flag  = 4'b0000;
    rd_flag  = 4'b0000;
    cmd_wr_flag  = 4'b0000;
    cmd_reg_new_flag = 4'b0000;
    cmd_rd_flag  = 4'b0000;
    bus_sync_flag = 4'b0000;
    conti_data_flag = 4'b0000;
    st_state0 = STARTUP_PH0;
    st_state1 = STARTUP_PH0;
    st_state2 = STARTUP_PH0;
    st_state3 = STARTUP_PH0;
    st_state0i = STARTUP_PH0;
    st_state1i = STARTUP_PH0;
    st_state2i = STARTUP_PH0;
    st_state3i = STARTUP_PH0;
    startup_begin_flag0 = 1'b0;
    startup_end_flag0 = 1'b0;
    startup_begin_flag1 = 1'b0;
    startup_end_flag1 = 1'b0;
    startup_begin_flag2 = 1'b0;
    startup_end_flag2 = 1'b0;
    startup_begin_flag3 = 1'b0;
    startup_end_flag3 = 1'b0;
    crc_ck = 4'b0000;
    crc_ck_en = 4'b1111;
    crc_err_flag = 4'b0000;
    crc_err_flag_reg = 4'b0000;
    gwe_out = 4'b0000;
    gts_out = 4'b1111;
    d_o = 32'h0;
    outbus = 32'h0;
    outbus_dly = 32'h0;
    outbus_dly1 = 32'h0;
    busy_o = 1'b0;
    mode_pin_in = 3'b000;
    crc_reset = 4'b0000;
    gsr_set = 4'b0000;
    gts_usr_b = 4'b1111; // was 4'b111
    done_pin_drv = 4'b0000;
    shutdown_set = 4'b0000;
    desynch_set = 4'b0000;
    done_cycle_reg0 = 3'b011;
    done_cycle_reg1 = 3'b011;
    done_cycle_reg2 = 3'b011;
    done_cycle_reg3 = 3'b011;
    gts_cycle_reg0 = 3'b101;
    gts_cycle_reg1 = 3'b101;
    gts_cycle_reg2 = 3'b101;
    gts_cycle_reg3 = 3'b101;
    gwe_cycle_reg0 = 3'b100;
    gwe_cycle_reg1 = 3'b100;
    gwe_cycle_reg2 = 3'b100;
    gwe_cycle_reg3 = 3'b100;
    init_rst = 1'b0;
    nx_st_state0  = 3'b000;
    nx_st_state1  = 3'b000;
    nx_st_state2  = 3'b000;
    nx_st_state3  = 3'b000;
    ghigh_b = 4'b0000;
    gts_cfg_b = 4'b0000;
    eos_startup = 4'b0000;
    startup_set = 4'b0000;
    startup_set_pulse0 = 2'b00;
    startup_set_pulse1 = 2'b00;
    startup_set_pulse2 = 2'b00;
    startup_set_pulse3 = 2'b00;
    abort_out_en = 1'b0;
    id_error_flag = 4'b0000;
    iprog_b = 4'b1111;
    i_init_b_cmd = 4'b1111;
    i_init_b = 1'b0;
    abort_status = 8'b00000000;
    persist_en = 1'b0;
    rst_sync = 1'b0;
    abort_dis = 1'b0;
    lock_cycle_reg0 = 3'b000;
    lock_cycle_reg1 = 3'b000;
    lock_cycle_reg2 = 3'b000;
    lock_cycle_reg3 = 3'b000;
    rbcrc_no_pin = 4'b0000;
    abort_flag_rst = 1'b0;
    gsr_st_out = 4'b1111; 
    gsr_cmd_out = 4'b0000;
    gsr_cmd_out_pulse = 4'b0000;
    d_o_en = 1'b0;
    abort_flag = 4'b0000;
    downcont_cnt = 0;
    rst_en = 1'b0;
    prog_b_a = 1'b1;
    csbo_flag = 4'b0000;
    bout_flag = 4'b0000;
    bout_flags = 4'b0000;
    bout_bf = 4'b0000;
    rd_sw_en = 1'b0;
    done_release = 1'b0;
    PRDONE_out = 1'b0;
    fdri_rst_prdone_flag = 1'b0;
  end


  initial begin

    case (ICAP_SUPPORT)
        "FALSE" : icap_on = 0;
        "TRUE" : icap_on = 1;
        default : icap_on = 0;
    endcase

    if (DEVICE_ID == 32'h0 && icap_on == 0) begin
      $display("Error: [Unisim %s-1] DEVICE_ID attribute is not set. Instance: %m", MODULE_NAME);
     end

     if (ICAP_SUPPORT == "TRUE") begin
       case (ICAP_WIDTH)
        "X8" : icap_bw = 2'b01;
        "X16" : icap_bw = 2'b10;
        "X32" : icap_bw = 2'b11;
        default : icap_bw = 2'b01;
       endcase 

       frame_data_fd = $fopen(FRAME_RBT_OUT_FILENAME, "w");
       if  (frame_data_fd != 0) begin
            frame_data_wen = 1;
            $fwriteh(frame_data_fd, "frame_address   frame_data  readback_crc_value\n");
       end
     end 
     else begin
        icap_bw = 2'b00;
        frame_data_wen = 0;
     end

      icap_sync = 0;
      
   end


   assign GSR = gsr_out[0];
   assign GTS = gts_out[0];
   assign GWE = gwe_out[0];
   assign busy_out = busy_o;
   assign cfgerr_b_flag[0] = rw_en[0] & ~crc_err_flag_tot[0];
   assign cfgerr_b_flag[1] = rw_en[1] & ~crc_err_flag_tot[1];
   assign cfgerr_b_flag[2] = rw_en[2] & ~crc_err_flag_tot[2];
   assign cfgerr_b_flag[3] = rw_en[3] & ~crc_err_flag_tot[3];
   assign crc_err_flag_tot[0] = id_error_flag[0] | crc_err_flag_reg[0];
   assign crc_err_flag_tot[1] = id_error_flag[1] | crc_err_flag_reg[1];
   assign crc_err_flag_tot[2] = id_error_flag[2] | crc_err_flag_reg[2];
   assign crc_err_flag_tot[3] = id_error_flag[3] | crc_err_flag_reg[3];
   assign d_out[7:0] = (abort_out_en ) ? abort_status : outbus_dly[7:0];
   assign d_out[31:8] = (abort_out_en ) ? 24'b0 : outbus_dly[31:8];
   assign d_out_en = d_o_en;
   assign cso_b_out = (csbo_flag[0] == 1) ? 0 : 1;
   assign crc_en =   (icap_init_done) ? 4'b0 : 4'b1111;


   always @(posedge cclk_in) begin
     outbus_dly <= outbus_dly1;
     outbus_dly1 <= outbus;
   end

   always @(posedge cclk_in or csi_b_in)
     if (csi_b_in == 1)
         csi_b_ins <= csi_b_in;
     else begin
        if (cclk_in != 1)
          csi_b_ins <= csi_b_in;
        else
          @(negedge cclk_in)
           csi_b_ins <= csi_b_in;
     end

   always @(abort_out_en or csi_b_in or rdwr_b_in && rd_flag[ib] )
    if (abort_out_en == 1)
       d_o_en = 1;
    else
       d_o_en = rdwr_b_in & ~csi_b_in & rd_flag[ib];


  assign init_b_t = init_b_in & i_init_b_cmd_t;

  always @( negedge prog_b_in) begin
         rst_en = 0;
         rst_en <= #cfg_Tprog 1;
  end

  assign iprog_b_0 = iprog_b[0];
  assign iprog_b_1 = (bout_en[1] == 1) ? iprog_b[1] : 1;
  assign iprog_b_2 = (bout_en[2] == 1) ? iprog_b[2] : 1;
  assign iprog_b_3 = (bout_en[3] == 1) ? iprog_b[3] : 1;

  assign iprog_b_t = iprog_b_3 & iprog_b_2 & iprog_b_1 & iprog_b_0;

  assign i_init_b_cmd_0 = i_init_b_cmd[0];
  assign i_init_b_cmd_1 =  (bout_en[1] == 1) ? i_init_b_cmd[1] : 1;
  assign i_init_b_cmd_2 =  (bout_en[2] == 1) ? i_init_b_cmd[2] : 1;
  assign i_init_b_cmd_3 =  (bout_en[3] == 1) ? i_init_b_cmd[3] : 1;

  assign i_init_b_cmd_t =  i_init_b_cmd_0 & i_init_b_cmd_1 & i_init_b_cmd_2
                            & i_init_b_cmd_3;

  always @( rst_en or init_rst or prog_b_in or iprog_b_t )
  if (icap_on == 0) begin
   if (init_rst == 1)
       init_b_out <= 0;
   else begin
     if ((prog_b_in == 0 ) && (rst_en == 1) || (iprog_b_t == 0))
         init_b_out <= 0;
     else if ((prog_b_in == 1 ) && (rst_en == 1) || (iprog_b_t == 1))
         init_b_out <= #(cfg_Tpl) 1;
   end
  end

  assign id_error_flag_t = &id_error_flag;

  always @(posedge id_error_flag_t) begin
      init_rst <= 1;
      init_rst <= #cfg_Tprog 0;
  end
  
  always @( rst_en or prog_b_in or prog_pulse_low)
    if (rst_en == 1) begin
       if (prog_pulse_low==cfg_Tprog) begin
           prog_b_a = 0;
           prog_b_a <= #500 1;
       end
       else
          prog_b_a = prog_b_in;
    end
    else 
          prog_b_a = 1;

  initial begin
    por_b = 0;
    por_b = #400000 1;
  end 

  assign prog_b_t = prog_b_a  & iprog_b_t & por_b;

  assign rst_intl = (prog_b_t==0 ) ? 0 : 1;

  always @( init_b_t or  prog_b_t) 
    if (prog_b_t == 0)
         mode_sample_flag <= 0;
    else if (init_b_t && mode_sample_flag == 0) begin
       if (prog_b_t == 1)  begin
          mode_pin_in <= m_in;
          if (m_in !== 3'b110) begin
             mode_sample_flag <=  0;
             if ( icap_on == 0) 
               $display("Error: [Unisim %s-2] Input M is %h. Only Slave SelectMAP mode M=110 is supported. Instance %m.", MODULE_NAME, m_in);
          end
          else
             mode_sample_flag <= #1 1;
       end     
     end

  always @(posedge init_b_t ) 
       if (prog_b_t != 1)  begin
            if ($time != 0 && icap_on == 0)
       $display("Error: [Unisim %s-3] PROGB is not high when INITB goes high at time %t. Instance %m.", MODULE_NAME, $time);
    end

  always @(m_in)
    if (mode_sample_flag == 1 && persist_en[0] == 1 && icap_on == 0)
       $display("Error: [Unisim %s-4] Mode pine M[2:0] changed after rising edge of INITB at time %t. Instance %m.", MODULE_NAME, $time);
  
  always @(posedge prog_b_in or negedge prog_b_in)
    if (prog_b_in == 0) 
        prog_pulse_low_edge <= $time;
    else if (prog_b_in == 1 && $time > 0) begin
       prog_pulse_low = $time - prog_pulse_low_edge;
       if (prog_pulse_low < cfg_Tprog  && icap_on == 0)
        $display("Error: [Unisim %s-5] Low time of PROGB is less than required minimum Tprogram time %d at time %t. Instance %m.", MODULE_NAME, cfg_Tprog, $time);
    end

    assign bus_en = (mode_sample_flag == 1 &&  csi_b_in ==0) ? 1 : 0;

    always @(posedge cclk_in or negedge rst_intl )
      if (rst_intl == 0 ) begin
         buswid_flag_init <= 4'b0;
         buswid_flag <= 4'b0;
         buswidth_tmp[0] <= 2'b00;
         buswidth_tmp[1] <= 2'b00;
         buswidth_tmp[2] <= 2'b00;
         buswidth_tmp[3] <= 2'b00;
      end
      else
        if (buswid_flag[ib] == 0) begin
           if (bus_en == 1 && rdwr_b_in == 0)  begin
                 tmp_byte = bit_revers8(d_in[7:0]);
                  if (buswid_flag_init[ib] == 0) begin
                     if (tmp_byte == 8'hBB)
                         buswid_flag_init[ib] <= 1;
                  end
                  else begin
                     if (tmp_byte == 8'h11) begin  // x8
                         buswid_flag[ib] <= 1; 
                         buswidth_tmp[ib] <= 2'b01;
                     end
                     else if (tmp_byte == 8'h22) begin  // x16
                         buswid_flag[ib] <= 1; 
                         buswidth_tmp[ib] <= 2'b10;
                     end
                     else if (tmp_byte == 8'h44) begin   // x32
                         buswid_flag[ib] <= 1; 
                         buswidth_tmp[ib] <= 2'b11;
                     end
                     else begin
                         buswid_flag[ib] <= 0; 
                         buswidth_tmp[ib] <= 2'b00;
                         buswid_flag_init[ib] <= 0;
                         if (icap_on == 0)
                         $display("Error: [Unisim %s-6] BUS Width Auto Dection did not find 0x11 or 0x22 or 0x44 on D[7:0] followed 0xBB at time %t. Instance %m.", MODULE_NAME, $time);
                         else 
                         $display("Error: [Unisim %s-7] BUS Width Auto Dection did not find 0x11 or 0x22 or 0x44 on dix[7:0] followed 0xBB on ICAPE3 instance at time %t. Instance %m.", MODULE_NAME, $time);
                         
                     end
                 end
            end
     end
 
    assign buswidth_ibtmp = (icap_on == 1 && icap_init_done == 1) ? icap_bw[1:0] : buswidth_tmp[ib];

    always @(buswidth_ibtmp)
      buswidth[ib] = buswidth_ibtmp;

    assign rw_en_tmp = (bus_en == 1 ) ?  1 : 0;

    assign rw_en[0] = ( buswid_flag[0] == 1)  ? rw_en_tmp : 0;
    assign rw_en[1] = ( buswid_flag[1] == 1)  ? rw_en_tmp : 0;
    assign rw_en[2] = ( buswid_flag[2] == 1)  ? rw_en_tmp : 0;
    assign rw_en[3] = ( buswid_flag[3] == 1)  ? rw_en_tmp : 0;
    

    assign desynch_set1[0] = desynch_set[0] | icap_desynch | rd_desynch;
    assign desynch_set1[1] = desynch_set[1] | icap_desynch | rd_desynch;
    assign desynch_set1[2] = desynch_set[2] | icap_desynch | rd_desynch;
    assign desynch_set1[3] = desynch_set[3] | icap_desynch | rd_desynch;
    assign desync_flag[0] = ~rst_intl | desynch_set1[0] | crc_err_flag[0] | id_error_flag[0];
    assign desync_flag[1] = ~rst_intl | desynch_set1[1] | crc_err_flag[1] | id_error_flag[1];
    assign desync_flag[2] = ~rst_intl | desynch_set1[2] | crc_err_flag[2] | id_error_flag[2];
    assign desync_flag[3] = ~rst_intl | desynch_set1[3] | crc_err_flag[3] | id_error_flag[3];
    
    always @(posedge eos_startup[0]) 
      if (icap_on == 1) begin
        $fclose(frame_data_fd);
        icap_init_done <= 1;
        @(posedge cclk_in); 
        @(posedge cclk_in)
         if (icap_init_done_dly == 0) 
            icap_desynch <= 1;
        @(posedge cclk_in);
        @(posedge cclk_in) begin
          icap_desynch <= 0;
          icap_init_done_dly <= 1;
        end
        @(posedge cclk_in);
        @(posedge cclk_in);
        @(posedge cclk_in);
      end
      else begin
        icap_clr <= 0;
        icap_desynch <= 0;
      end

    always @(posedge cclk_in or negedge rdwr_b_in)
     if (rdwr_b_in == 0)
       rd_sw_en <= 0;
     else begin
      if (csi_b_in == 1 && rdwr_b_in ==1)
          rd_sw_en <= 1;
     end

    assign desync_flag_t = |desync_flag;

    always @(posedge cclk_in or posedge desync_flag_t or negedge csi_b_in) begin
      if (desync_flag[ib] == 1) begin
          pack_in_reg_tmp0 = 32'b0;
          pack_in_reg_tmps0 = 32'b0;
      end
      if (desync_flag[0] == 1 ) begin
          new_data_in_flag[0] = 0;
          bus_sync_flag[0] = 0;
          wr_cnt[0] = 0;
          wr_flag[0] = 0;
          rd_flag[0] = 0;
      end
      if (desync_flag[1] == 1 ) begin
          new_data_in_flag[1] = 0;
          bus_sync_flag[1] = 0;
          wr_cnt[1] = 0;
          wr_flag[1] = 0;
          rd_flag[1] = 0;
      end
      if (desync_flag[2] == 1 ) begin
          new_data_in_flag[2] = 0;
          bus_sync_flag[2] = 0;
          wr_cnt[2] = 0;
          wr_flag[2] = 0;
          rd_flag[2] = 0;
      end
      if (desync_flag[3] == 1 ) begin
          new_data_in_flag[3] = 0;
          bus_sync_flag[3] = 0;
          wr_cnt[3] = 0;
          wr_flag[3] = 0;
          rd_flag[3] = 0;
      end
      if (icap_init_done == 1 && csi_b_in == 1 && rdwr_b_in == 0) begin
          new_data_in_flag = 4'b0;
          wr_cnt[0] = 0;
          wr_cnt[1] = 0;
          wr_cnt[2] = 0;
          wr_cnt[3] = 0;
          pack_in_reg_tmp0 = 32'b0;
          pack_in_reg_tmps0 = 32'b0;
      end
      else begin
       if (icap_clr == 1) begin
          new_data_in_flag <= 4'b0;
          wr_cnt[0] <= 0;
          wr_cnt[1] <= 0;
          wr_cnt[2] <= 0;
          wr_cnt[3] <= 0;
          wr_flag <= 4'b0;
          rd_flag <= 4'b0;
          pack_in_reg_tmp0 = 32'b0;
          pack_in_reg_tmps0 = 32'b0;
       end
       else if (rw_en[ib] == 1  && desync_flag[ib] == 0) begin
         if (rdwr_b_in == 0) begin
           wr_flag[ib] <= 1;
           rd_flag[ib] <= 0;
           if (buswidth[ib] == 2'b01 || (icap_sync == 1 && bus_sync_flag[ib] == 0)) begin
               tmp_byte = bit_revers8(d_in[7:0]);
               if (bus_sync_flag[ib] == 0) begin
                   pack_in_reg_tmp0 = pack_in_reg[ib];
                  if (pack_in_reg_tmp0[23:16] == 8'hAA && pack_in_reg_tmp0[15:8] == 8'h99 
                      && pack_in_reg_tmp0[7:0] == 8'h55 && tmp_byte == 8'h66) begin
                          bus_sync_flag[ib] <= 1;
                          new_data_in_flag[ib] <= 0;
                          wr_cnt[ib] <= 0;
                   end
                   else begin
                      pack_in_reg_tmp0[31:24] = pack_in_reg_tmp0[23:16];
                      pack_in_reg_tmp0[23:16] = pack_in_reg_tmp0[15:8];
                      pack_in_reg_tmp0[15:8] = pack_in_reg_tmp0[7:0];
                      pack_in_reg_tmp0[7:0] = tmp_byte;
                      pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                   end
               end
               else begin
                 if (wr_cnt[ib] == 0) begin
                    pack_in_reg_tmp0 = pack_in_reg[ib];
                    pack_in_reg_tmp0[31:24] = tmp_byte;
                    pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                     new_data_in_flag[ib] <= 0;
                     wr_cnt[ib] <=  1;
                 end
                 else if (wr_cnt[ib] == 1) begin
                    pack_in_reg_tmp0 = pack_in_reg[ib];
                    pack_in_reg_tmp0[23:16] = tmp_byte;
                    pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                     new_data_in_flag[ib] <= 0;
                     wr_cnt[ib] <= 2;
                 end
                 else if (wr_cnt[ib] == 2) begin
                    pack_in_reg_tmp0 = pack_in_reg[ib];
                    pack_in_reg_tmp0[15:8] = tmp_byte;
                    pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                     new_data_in_flag[ib] <= 0;
                     wr_cnt[ib] <= 3;
                 end
                 else if (wr_cnt[ib] == 3) begin
                    pack_in_reg_tmp0 = pack_in_reg[ib];
                    pack_in_reg_tmp0[7:0] = tmp_byte;
                    pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                     new_data_in_flag[ib] <= 1;
                     wr_cnt[ib] <= 0;
                 end
             end
           end
           else if (buswidth[ib] == 2'b10) begin
             tmp_word = {bit_revers8(d_in[15:8]), bit_revers8(d_in[7:0])};
             if (bus_sync_flag[ib] == 0) begin
                 pack_in_reg_tmp0 = pack_in_reg[ib];
                if (pack_in_reg_tmp0[15:0] == 16'hAA99 && tmp_word ==16'h5566) begin
                     wr_cnt[ib] <= 0;
                     bus_sync_flag[ib] <= 1;
                     new_data_in_flag[ib] <= 0;
                end
                else begin
                   pack_in_reg_tmp0[31:16] = pack_in_reg_tmp0[15:0];
                   pack_in_reg_tmp0[15:0] = tmp_word;
                   pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                   new_data_in_flag[ib] <= 0;
                   wr_cnt[ib] <= 0;
                end
             end
             else begin
               pack_in_reg_tmp0 = pack_in_reg[ib];
               if (wr_cnt[ib] == 0) begin
                   pack_in_reg_tmp0[31:16] = tmp_word;
                   pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                   new_data_in_flag[ib] <= 0;
                   wr_cnt[ib] <= 1;
               end
               else if (wr_cnt[ib] == 1) begin
                   pack_in_reg_tmp0[15:0] = tmp_word;
                   pack_in_reg_tmps0 <= pack_in_reg_tmp0;
                   new_data_in_flag[ib] <= 1;
                   wr_cnt[ib] <= 0;
               end
             end
           end
           else if (buswidth[ib] == 2'b11 ) begin
             tmp_dword = {bit_revers8(d_in[31:24]), bit_revers8(d_in[23:16]), bit_revers8(d_in[15:8]),
                          bit_revers8(d_in[7:0])};
             pack_in_reg_tmp0 <= tmp_dword;
             pack_in_reg_tmps0 <= tmp_dword;
             if (bus_sync_flag[ib] == 0) begin
                if (tmp_dword == 32'hAA995566) begin
                     bus_sync_flag[ib] <= 1;
                     new_data_in_flag[ib] <= 0;
                end
             end
             else begin
                pack_in_reg_tmp0 <= tmp_dword;
                pack_in_reg_tmps0 <= tmp_dword;
                new_data_in_flag[ib] <= 1;
             end
           end
       end
       else begin
            wr_flag[ib] <= 0;
            new_data_in_flag[ib] <= 0;
            if (rd_sw_en ==1)
               rd_flag[ib] <= 1;
       end
     end
     else begin
            wr_flag[ib] <= 0;
            rd_flag[ib] <= 0;
            new_data_in_flag[ib] <= 0;
     end
   end
  end


   always @(pack_in_reg_tmps0 or desync_flag or icap_clr)
   begin
     if (desync_flag[0] == 1 || icap_clr == 1)
         pack_in_reg[0] = 32'b0;
     if (desync_flag[1] == 1 || icap_clr == 1)
         pack_in_reg[1] = 32'b0;
     if (desync_flag[2] == 1 || icap_clr == 1)
         pack_in_reg[2] = 32'b0;
     if (desync_flag[3] == 1 || icap_clr == 1)
         pack_in_reg[3] = 32'b0;

     if (ib == 0  && desync_flag[0] == 0 && icap_clr == 0) begin
        pack_in_reg[0] = pack_in_reg_tmps0;
     end
     else if (ib == 1 && desync_flag[1] == 0 && icap_clr == 0)
        pack_in_reg[1] = pack_in_reg_tmps0;
     else if (ib == 2  && desync_flag[2] == 0 && icap_clr == 0)
        pack_in_reg[2] = pack_in_reg_tmps0;
     else if (ib == 3  && desync_flag[3] == 0 && icap_clr == 0)
        pack_in_reg[3] = pack_in_reg_tmps0;
   end
           

    task rst_pack_dec;
       input ib_d;
    begin
         conti_data_flag[ib_d] <= 0;
         conti_data_cnt[ib_d] <= 0;
         cmd_wr_flag[ib_d] <= 0;
         cmd_rd_flag[ib_d] <= 0;
         id_error_flag[ib_d] <= 0;
         crc_curr[ib_d] <= 32'b0;
         crc_ck[ib_d] <= 0;
         csbo_cnt[ib_d] <= 0;
         csbo_flag[ib_d] <= 0;
         downcont_cnt <= 0;
         rd_data_cnt[ib_d] <= 0;
    end 
    endtask
      
    
    always @(negedge cclk_in or negedge rst_intl)
      if (rst_intl == 0) begin
         rst_pack_dec(0);
         rst_pack_dec(1);
         rst_pack_dec(2);
         rst_pack_dec(3);
         bout_flag <= 4'b0;
         bout_cnt[0] <= 0;
         bout_cnt[1] <= 0;
         bout_cnt[2] <= 0;
         bout_cnt[3] <= 0;
      end
      else begin
        if (icap_clr == 1) begin
         rst_pack_dec(0);
         rst_pack_dec(1);
         rst_pack_dec(2);
         rst_pack_dec(3);
         bout_flag <= 4'b0;
         bout_cnt[0] <= 0;
         bout_cnt[1] <= 0;
         bout_cnt[2] <= 0;
         bout_cnt[3] <= 0;
        end
        if (crc_reset[ib] == 1 ) begin
            crc_reg[ib] <= 32'b0;
            crc_ck[ib] <= 0;
            crc_curr[ib] <= 32'b0;
        end
        if (crc_ck[ib] == 1) begin
             crc_curr[ib] <= 32'b0;
             crc_ck[ib]  <= 0;
        end

        if (desynch_set1[0] == 1 || crc_err_flag[0] == 1) begin
           bout_flag[0] <= 0;
           bout_cnt[0] <= 0;
           rst_pack_dec(0);
        end
        if (desynch_set1[1] == 1 || crc_err_flag[1] == 1) begin
           bout_flag[1] <= 0;
           bout_cnt[1] <= 0;
           rst_pack_dec(1);
        end
        if (desynch_set1[2] == 1 || crc_err_flag[2] == 1) begin
           bout_flag[2] <= 0;
           bout_cnt[2] <= 0;
           rst_pack_dec(2);
        end
        if (desynch_set1[3] == 1 || crc_err_flag[3] == 1) begin
           bout_flag[3] <= 0;
           bout_cnt[3] <= 0;
           rst_pack_dec(3);
        end
        if (new_data_in_flag[ib] == 1 && wr_flag[ib] == 1 && csi_b_ins == 0
            && desynch_set1[ib] == 0 && crc_err_flag[ib] == 0 && icap_clr == 0) begin
               pack_in_reg_tmp = pack_in_reg[ib];
           if (conti_data_flag[ib] == 1 ) begin
               reg_addr_tmp = reg_addr[ib];
               case (reg_addr_tmp)
               5'b00000 : begin 
                             crc_reg[ib] <= pack_in_reg[ib];
                             crc_reg_tmp <= pack_in_reg[ib];
                             crc_ck[ib] <= 1;
                          end 
               5'b00001 : far_reg[ib] <= {6'b0, pack_in_reg_tmp[25:0]};

               5'b00010 : begin 
                          fdri_reg[ib] <= pack_in_reg[ib];
                          fdri_rst_prdone_flag <= ~fdri_rst_prdone_flag;
                          end
               5'b00100 : cmd_reg[ib] <= pack_in_reg_tmp[4:0];
               5'b00101 : ctl0_reg[ib] <= (pack_in_reg[ib] & mask_reg[ib]) | (ctl0_reg[ib] & ~mask_reg[ib]);
               5'b00110 : mask_reg[ib] <= pack_in_reg[ib];
               5'b01000 : lout_reg[ib] <= pack_in_reg[ib];
               5'b01001 : cor0_reg[ib] <= pack_in_reg[ib];
               5'b01010 : mfwr_reg[ib] <= pack_in_reg[ib];
               5'b01011 : cbc_reg[ib] <= pack_in_reg[ib];
               5'b01100 : begin
                          idcode_reg[ib] <= pack_in_reg[ib];
                          if (pack_in_reg_tmp[27:0] != DEVICE_ID[27:0]) begin
                             id_error_flag[ib] <= 1;
                             if (icap_on == 0)
                               $display("Error: [Unisim %s-8] Written value to IDCODE register is %h which does not match with DEVICE ID %h on %s at time %t. Instance %m", MODULE_NAME, pack_in_reg[ib], DEVICE_ID, MODULE_NAME, $time);
                             else
                               $display("Error: [Unisim %s-9] Written value to IDCODE register is %h which does not match with DEVICE ID %h on ICAPE3 at time %t. Instance %m", MODULE_NAME, pack_in_reg[ib], DEVICE_ID, $time);
                          end 
                          else
                             id_error_flag[ib] <= 0;
                          end
               5'b01101 : axss_reg[ib] <= pack_in_reg[ib];
               5'b01110 : cor1_reg[ib] <= pack_in_reg[ib];
               5'b01111 : csob_reg[ib] <= pack_in_reg[ib];
               5'b10000 : wbstar_reg[ib] <= pack_in_reg[ib];
               5'b10001 : timer_reg[ib] <= pack_in_reg[ib];
               5'b10011 : rbcrc_sw_reg[ib] <= pack_in_reg[ib];
               5'b10111 : testmode_reg[ib] <= pack_in_reg[ib];
               5'b11000 : ctl1_reg[ib] <= (pack_in_reg[ib] & mask_reg[ib]) | (ctl1_reg[ib] & ~mask_reg[ib]);
               5'b11001 : memrd_param_reg[ib] <= {4'b0,  pack_in_reg_tmp[27:0]};
               5'b11010 : dwc_reg[ib] <= {4'b0,  pack_in_reg_tmp[27:0]};
               5'b11011 : trim_reg[ib] <= pack_in_reg[ib];
               5'b11110 : bout_reg[ib] <= pack_in_reg[ib];
               5'b11111 : bspi_reg[ib] <= pack_in_reg[ib];
               endcase
   
             if (reg_addr[ib] != 5'b00000)
               crc_ck[ib] <= 0;

             if (reg_addr_tmp == 5'b00100)
                  cmd_reg_new_flag[ib] <= 1;
             else
                 cmd_reg_new_flag[ib] <= 0;

             if (crc_en[ib] == 1) begin 
               if (reg_addr[ib] == 5'h04 && pack_in_reg_tmp[4:0] == 5'b00111)
                   crc_curr[ib] = 32'b0;
               else begin
                  if ( reg_addr[ib] != 5'h0f && reg_addr[ib] != 5'h12 && reg_addr[ib] != 5'h14 
                   && reg_addr[ib] != 5'h15 && reg_addr[ib] != 5'h16 && reg_addr[ib] != 5'h00) begin
                     crc_input = {reg_addr[ib], pack_in_reg_tmp}; 
                     crc_curr_tmp = crc_curr[ib];
                     crc_new = bcc_next(crc_curr_tmp, crc_input);
                     crc_curr[ib] <= crc_new;
                   end
               end
             end

             if (conti_data_cnt[ib] <= 1) begin
                  conti_data_cnt[ib] <= 0;
              end
             else 
                conti_data_cnt[ib] <= conti_data_cnt[ib] - 1;
        end
        else if (conti_data_flag[ib] == 0 ) begin
            if ( downcont_cnt >= 1) begin
                   if (crc_en[ib] == 1) begin
                     crc_input[36:0] =  {5'b00010, pack_in_reg[ib]}; 
                     crc_new = bcc_next(crc_curr[ib], crc_input);
                     crc_curr[ib] <= crc_new;
                   end
                  if (ib == 0) begin
                   if (farn <= 80)
                      farn <= farn + 1;
                   else begin
                      far_addr <= far_addr + 1;
                      farn <= 0;
                   end
                   if (frame_data_wen == 1 && icap_init_done == 0) begin
                     rbcrc_input[36:0] =  {5'b00011, pack_in_reg[ib]}; 
                     rbcrc_new[31:0] = bcc_next(rbcrc_curr[ib], rbcrc_input);
                     rbcrc_curr[ib] <= rbcrc_new;
                     $fwriteh(frame_data_fd, far_addr);
                     $fwriteh(frame_data_fd, "\t");
                     $fwriteh(frame_data_fd, pack_in_reg[ib]);
                     $fwriteh(frame_data_fd, "\t");
                     $fwriteh(frame_data_fd, rbcrc_new); 
                     $fwriteh(frame_data_fd, "\n");
                   end
                  end
             end

             if (pack_in_reg_tmp[31:29] == 3'b010 ) begin
               bout_cnt_tmp = bout_cnt[ib];
               if (reg_addr[ib] == 5'b00010 && downcont_cnt == 0  ) begin
                   cmd_rd_flag[ib] <= 0;
                   cmd_wr_flag[ib] <= 0;
                   conti_data_flag[ib] <= 0;
                   conti_data_cnt[ib] <= 0;
                   downcont_cnt <= pack_in_reg_tmp[26:0];
                   far_addr <=  far_reg[ib];
                end
                else if (reg_addr_tmp == 5'b11110 && bout_cnt_tmp == 0) begin
                   cmd_rd_flag[ib] <= 0;
                   cmd_wr_flag[ib] <= 0;
                   conti_data_flag[ib] <= 0;
                   conti_data_cnt[ib] <= 0;
                   bout_flag[ib] <= 1;
                   bout_cnt[ib] <= pack_in_reg_tmp[26:0];
                end
                else if (reg_addr[ib] == 5'b01000 && csbo_cnt[ib] == 0) begin
                   cmd_rd_flag[ib] <= 0;
                   cmd_wr_flag[ib] <= 0;
                   conti_data_flag[ib] <= 0;
                   conti_data_cnt[ib] <= 0;
                   csbo_flag[ib] <= 1;
                   csbo_cnt[ib] <= pack_in_reg_tmp[26:0];
                end 
             end
             else if (pack_in_reg_tmp[31:29] == 3'b001) begin // type 1 package
                if (pack_in_reg_tmp[28:27] == 2'b01 && downcont_cnt == 0) begin
                    if (pack_in_reg_tmp[10:0] != 11'b0) begin
                       cmd_rd_flag[ib] <= 1;
                       cmd_wr_flag[ib] <= 0;
                       rd_data_cnt[ib] <= 4;
                       conti_data_cnt[ib] <= 0;
                       conti_data_flag[ib] <= 0;
                       rd_reg_addr[ib] <= pack_in_reg_tmp[17:13];
                    end
                end
                else if (pack_in_reg_tmp[28:27] == 2'b10 && downcont_cnt == 0) begin
                   if (pack_in_reg_tmp[17:13] == 5'b01000) begin  // lout reg
                           lout_reg[ib] <= pack_in_reg_tmp;
                           conti_data_flag[ib] = 0;
                           reg_addr[ib] <= pack_in_reg_tmp[17:13];
                           reg_addr_tmp <= pack_in_reg_tmp[17:13];
                           cmd_wr_flag[ib] <= 1;
                           conti_data_cnt[ib] <= 5'b0;
                    end
                   else if (pack_in_reg_tmp[17:13] == 5'b11110) begin  // bout reg
                           bout_reg[ib] <= pack_in_reg_tmp;
                           bout_flags[ib] <= 1;
                           conti_data_flag[ib] = 0;
                           reg_addr[ib] <= pack_in_reg_tmp[17:13];
                           reg_addr_tmp <= pack_in_reg_tmp[17:13];
                           cmd_wr_flag[ib] <= 1;
                           conti_data_cnt[ib]<= 5'b0;
                   end
                   else  begin
                      if (pack_in_reg_tmp[10:0] != 10'b0) begin
                       cmd_rd_flag[ib] <= 0;
                       cmd_wr_flag[ib] <= 1;
                       conti_data_flag[ib] <= 1;
                       conti_data_cnt[ib] <= pack_in_reg_tmp[10:0];
                       reg_addr[ib] <= pack_in_reg_tmp[17:13];
                       reg_addr_tmp <= pack_in_reg_tmp[17:13];
                      end
                      else begin
                       cmd_rd_flag[ib] <= 0;
                       cmd_wr_flag[ib] <= 1;
                       conti_data_flag[ib] <= 0;
                       conti_data_cnt[ib] <= 0;
                       reg_addr[ib] <= pack_in_reg_tmp[17:13];
                       reg_addr_tmp <= pack_in_reg_tmp[17:13];
                      end
                    end
                end
                else begin
                    cmd_wr_flag[ib] <= 0;
                    conti_data_flag[ib] <= 0;
                    conti_data_cnt[ib] <= 0;
                end
             end
          end    // if (conti_data_flag == 0 ) 
          if (csbo_cnt[ib] != 0 ) begin
             if (csbo_flag[ib] == 1)
              csbo_cnt[ib] <= csbo_cnt[ib] - 1;
          end
          else
              csbo_flag[ib] <= 0;
              
          if (bout_cnt[0] != 0  && bout_flag[0] == 1) begin
             if (bout_cnt[0]  == 1) begin
                bout_cnt[0] <= 0;
                bout_flag[0] <= 0;
             end
             else
              bout_cnt[0] <= bout_cnt[0] - 1;
          end

          if (bout_cnt[1] != 0  && bout_flag[1] == 1) begin
             if (bout_cnt[1]  == 1) begin
                bout_cnt[1] <= 0;
                bout_flag[1] <= 0;
             end
             else
              bout_cnt[1] <= bout_cnt[1] - 1;
          end

          if (bout_cnt[2] != 0 && bout_flag[2] == 1) begin
              bout_cnt[2] <= bout_cnt[2] - 1;
             if (bout_cnt[2]  == 1) begin
                bout_cnt[2] <= 0;
                bout_flag[2] <= 0;
             end
             else
                bout_cnt[2] <= bout_cnt[2] - 1;
          end

          if (bout_cnt[3] != 0 && bout_flag[3] == 1 ) begin
             if (bout_cnt[3]  == 1) begin
                bout_cnt[3] <= 0;
                bout_flag[3] <= 0;
             end
             else
              bout_cnt[3] <= bout_cnt[3] - 1;
          end

          if (conti_data_cnt[ib] == 5'b00001 ) 
                conti_data_flag[ib] <= 0;

          if (crc_ck[ib] == 1 || icap_init_done == 1)
            crc_ck[ib] <= 0;
      end

      if (rw_en[ib] == 1 && csi_b_ins == 0) begin
         if (rd_data_cnt[ib] == 1 && rd_flag[ib] == 1) 
            rd_data_cnt[ib] <= 0;
         else if (rd_data_cnt[ib] == 0 && rd_flag[ib] == 1) begin
               cmd_rd_flag[ib] <= 0;
         end
         else if (cmd_rd_flag[ib] ==1  && rd_flag[ib] == 1)
             rd_data_cnt[ib] <= rd_data_cnt[ib] - 1;

          if (downcont_cnt >= 1 && conti_data_flag[ib] == 0 && new_data_in_flag[ib] == 1 && wr_flag[ib] == 1)
              downcont_cnt <= downcont_cnt - 1;
      end

     
      if (cmd_reg_new_flag[ib] == 1 )
          cmd_reg_new_flag[ib] <= 0;
   
    end


   always @(bout_flag)
     if (bout_flag[3] == 1) begin
       ib = 3;
       ib_skp = 1;
     end
     else if (bout_flag[2] == 1) begin
       ib = 3;
       ib_skp = 0;
     end
     else if (bout_flag[1] == 1) begin
       ib = 2;
       ib_skp = 0;
     end
     else if (bout_flag[0] == 1) begin
       ib = 1;
       ib_skp = 0;
     end
     else begin
       ib = 0;
       ib_skp = 0;
     end 
       

   always @(posedge cclk_in or negedge rst_intl)
    if (rst_intl == 0) begin
         outbus <= 32'b0;
     end
    else begin
        if (cmd_rd_flag[ib] == 1 && rdwr_b_in == 1 && csi_b_in == 0) begin
               case (rd_reg_addr[ib])
               5'b00000 : if (buswidth[ib] == 2'b01) 
                             rdbk_byte(crc_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(crc_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11) 
                             rdbk_2wd(crc_reg[ib], rd_data_cnt[ib]);
               5'b00001 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(far_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(far_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(far_reg[ib], rd_data_cnt[ib]);
               5'b00011 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(fdro_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(fdro_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(fdro_reg[ib], rd_data_cnt[ib]);
               5'b00100 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(cmd_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(cmd_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(cmd_reg[ib], rd_data_cnt[ib]);
               5'b00101 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(ctl0_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(ctl0_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(ctl0_reg[ib], rd_data_cnt[ib]);
               5'b00110 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(mask_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(mask_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(mask_reg[ib], rd_data_cnt[ib]);
               5'b00111 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(stat_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(stat_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11) 
                             rdbk_2wd(stat_reg[ib], rd_data_cnt[ib]);
               5'b01001 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(cor0_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(cor0_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(cor0_reg[ib], rd_data_cnt[ib]);
               5'b01100 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(DEVICE_ID, rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(DEVICE_ID, rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(DEVICE_ID, rd_data_cnt[ib]);
               5'b01101 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(axss_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(axss_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(axss_reg[ib], rd_data_cnt[ib]);
               5'b01110 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(cor1_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(cor1_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(cor1_reg[ib], rd_data_cnt[ib]);
               5'b10000 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(wbstar_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(wbstar_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(wbstar_reg[ib], rd_data_cnt[ib]);
               5'b10001 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(timer_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(timer_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(timer_reg[ib], rd_data_cnt[ib]);
               5'b10010 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(rbcrc_hw_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(rbcrc_hw_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(rbcrc_hw_reg[ib], rd_data_cnt[ib]);
               5'b10011 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(rbcrc_sw_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(rbcrc_sw_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(rbcrc_sw_reg[ib], rd_data_cnt[ib]);
               5'b10100 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(rbcrc_live_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(rbcrc_live_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(rbcrc_live_reg[ib], rd_data_cnt[ib]);
               5'b10101 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(efar_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(efar_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(efar_reg[ib], rd_data_cnt[ib]);
               5'b10110 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(bootsts_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(bootsts_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(bootsts_reg[ib], rd_data_cnt[ib]);
               5'b11000 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(ctl1_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(ctl1_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(ctl1_reg[ib], rd_data_cnt[ib]);
               5'b11001 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(memrd_param_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(memrd_param_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(memrd_param_reg[ib], rd_data_cnt[ib]);
               5'b11010 : if (buswidth[ib] == 2'b01)
                             rdbk_byte( dwc_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd( dwc_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(dwc_reg[ib], rd_data_cnt[ib]);
               5'b11011 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(trim_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(trim_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(trim_reg[ib], rd_data_cnt[ib]);
               5'b11111 : if (buswidth[ib] == 2'b01)
                             rdbk_byte(bspi_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b10)
                             rdbk_wd(bspi_reg[ib], rd_data_cnt[ib]);
                          else if (buswidth[ib] == 2'b11)
                             rdbk_2wd(bspi_reg[ib], rd_data_cnt[ib]);
               endcase
               if (ib != 0) begin
                  if (rd_data_cnt[ib] == 1)
                    rd_desynch_tmp <= 1;
               end        
       end
       else begin
             outbus <= 32'b0;
             rd_desynch <= rd_desynch_tmp;
             rd_desynch_tmp <= 0;
       end
   end

    assign crc_rst[0] = crc_reset[0] | ~rst_intl;
    assign crc_rst[1] = crc_reset[1] | ~rst_intl;
    assign crc_rst[2] = crc_reset[2] | ~rst_intl;
    assign crc_rst[3] = crc_reset[3] | ~rst_intl;

    assign crc_curr_cktmp =  crc_curr[0];
    assign crc_reg_cktmp = crc_reg[0];

    

    always @(posedge cclk_in or posedge crc_rst[0] )
     if (crc_rst[0] == 1) begin
         crc_err_flag[0] <= 0;
         crc_ck_en[0] <= 1;
     end
     else
       if (crc_ck[0] == 1 && crc_ck_en[0] == 1 ) begin
            if (crc_curr[0] != crc_reg[0]) 
                crc_err_flag[0] <= 1;
            else
                 crc_err_flag[0] <= 0;

            crc_ck_en[0] <= 0;
       end
       else begin
           crc_err_flag[0] <= 0;
           crc_ck_en[0] <= 1;
       end 

    always @(posedge cclk_in or posedge crc_rst[1] )
     if (crc_rst[1] == 1) begin
         crc_err_flag[1] <= 0;
         crc_ck_en[1] <= 1;
     end
     else
       if (crc_ck[1] == 1 && crc_ck_en[1]  == 1 ) begin
            if (crc_curr[1] != crc_reg[1]) 
                crc_err_flag[1] <= 1;
            else
                 crc_err_flag[1] <= 0;

            crc_ck_en[1] <= 0;
       end
       else begin
           crc_err_flag[1] <= 0;
           crc_ck_en[1] <= 1;

       end

    always @(posedge cclk_in or posedge crc_rst[2] )
     if (crc_rst[2] == 1) begin
         crc_err_flag[2] <= 0;
         crc_ck_en[2] <= 1;
     end
     else
       if (crc_ck[2] == 1 && crc_ck_en[2] == 1) begin
            if (crc_curr[2] != crc_reg[2]) 
                crc_err_flag[2] <= 1;
            else
                 crc_err_flag[2] <= 0;

            crc_ck_en[2] <= 0;
       end
       else begin
           crc_err_flag[2] <= 0;
           crc_ck_en[2] <= 1;
       end

    always @(posedge cclk_in or posedge crc_rst[3] )
     if (crc_rst[3] == 1) begin
         crc_err_flag[3] <= 0;
         crc_ck_en[3] <= 1;
     end
     else
       if (crc_ck[3] == 1 && crc_ck_en[3] == 1) begin
            if (crc_curr[3] != crc_reg[3]) 
                crc_err_flag[3] <= 1;
            else
                 crc_err_flag[3] <= 0;

            crc_ck_en[3] <= 0;
       end
       else begin
           crc_err_flag[3] <= 0;
           crc_ck_en[3] <= 1;
       end

    always @(posedge crc_err_flag[0] or negedge rst_intl or posedge bus_sync_flag[0])
     if (rst_intl == 0)
         crc_err_flag_reg[0] <= 0;
     else if (crc_err_flag[0] == 1)
         crc_err_flag_reg[0] <= 1;
     else
         crc_err_flag_reg[0] <= 0;

    always @(posedge crc_err_flag[1] or negedge rst_intl or posedge bus_sync_flag[1])
     if (rst_intl == 0)
         crc_err_flag_reg[1] <= 0;
     else if (crc_err_flag[1] == 1)
         crc_err_flag_reg[1] <= 1;
     else
         crc_err_flag_reg[1] <= 0;

    always @(posedge crc_err_flag[2] or negedge rst_intl or posedge bus_sync_flag[2])
     if (rst_intl == 0)
         crc_err_flag_reg[2] <= 0;
     else if (crc_err_flag[2] == 1)
         crc_err_flag_reg[2] <= 1;
     else
         crc_err_flag_reg[2] <= 0;

    always @(posedge crc_err_flag[3] or negedge rst_intl or posedge bus_sync_flag[3])
     if (rst_intl == 0)
         crc_err_flag_reg[3] <= 0;
     else if (crc_err_flag[3] == 1)
         crc_err_flag_reg[3] <= 1;
     else
         crc_err_flag_reg[3] <= 0;

    always @(posedge cclk_in or negedge rst_intl)
    if (rst_intl == 0) begin
         startup_set <= 4'b0;
         crc_reset  <= 4'b0;
         gsr_cmd_out <= 4'b0;
         shutdown_set <= 4'b0;
         desynch_set <= 4'b0;
         ghigh_b <= 4'b0;
    end
    else 
    for (ci = 0; ci <=3; ci = ci+1) begin
     if (cmd_reg_new_flag[ci] == 1) begin
      if (cmd_reg[ci] == 5'b00011) 
          ghigh_b[ci] <= 1;
      else if (cmd_reg[ci] == 5'b01000)
           ghigh_b[ci] <= 0;

      if (cmd_reg[ci] == 5'b00101)
           startup_set[ci] <= 1;
      else
           startup_set[ci] <= 0;

      if (cmd_reg[ci] == 5'b00111) 
           crc_reset[ci] <= 1;
      else
           crc_reset[ci] <= 0;

      if (cmd_reg[ci] == 5'b01010) 
           gsr_cmd_out[ci] <= 1;
      else
           gsr_cmd_out[ci] <= 0;

      if (cmd_reg[ci] == 5'b01011)
           shutdown_set[ci] <= 1;
      else 
           shutdown_set[ci] <= 0;

      if (cmd_reg[ci] == 5'b01101) 
           desynch_set[ci] <= 1;
      else
           desynch_set[ci] <= 0;

      if (cmd_reg[ci] == 5'b01111) begin
          iprog_b[ci] <= 0;
          i_init_b_cmd[ci] <= 0;
          iprog_b[ci] <= #cfg_Tprog 1;
          i_init_b_cmd[ci] <=#(cfg_Tprog + cfg_Tpl) 1;
       end
     end
     else begin
             startup_set[ci] <= 0;
              crc_reset[ci] <= 0;
              gsr_cmd_out[ci] <= 0;
              shutdown_set[ci] <= 0;
              desynch_set[ci] <= 0;
      end
    end

   always @(posedge startup_set[0] or posedge desynch_set[0] or posedge rw_en[0]  )
    if (rw_en[0] == 1 || desynch_set[0] == 1)
     begin
      if (startup_set_pulse0 == 2'b00 && startup_set[0] ==1) begin
         if (icap_on == 0)
           startup_set_pulse0 <= 2'b01;
         else begin
           startup_set_pulse0 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse0 <= 2'b00;
         end
       end
       else if (desynch_set[0] == 1 && startup_set_pulse0 == 2'b01) begin
           startup_set_pulse0 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse0 <= 2'b00;
      end
    end

   always @(posedge startup_set[1] or posedge desynch_set[1] or posedge rw_en[1] )
    if (rw_en[1] == 1 || desynch_set[1] == 1)
     begin
      if (startup_set_pulse1 == 2'b00 && startup_set[1] ==1) begin
         if (icap_on == 0)
           startup_set_pulse1 <= 2'b01;
         else begin
           startup_set_pulse1 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse1 <= 2'b00;
         end
       end
       else if (desynch_set[1] == 1 && startup_set_pulse1 == 2'b01) begin
           startup_set_pulse1 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse1 <= 2'b00;
      end
    end

   always @(posedge startup_set[2] or posedge desynch_set[2] or posedge rw_en[2])
    if (rw_en[2] == 1 || desynch_set[2] == 1)
     begin
      if (startup_set_pulse2 == 2'b00 && startup_set[2] ==1) begin
         if (icap_on == 0)
           startup_set_pulse2 <= 2'b01;
         else begin
           startup_set_pulse2 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse2 <= 2'b00;
         end
       end
       else if (desynch_set[2] == 1 && startup_set_pulse2 == 2'b01) begin
           startup_set_pulse2 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse2 <= 2'b00;
      end
    end

   always @(posedge startup_set[3] or posedge desynch_set[3] or posedge rw_en[3])
    if (rw_en[3] == 1 || desynch_set[3] == 1)
     begin
      if (startup_set_pulse3 == 2'b00 && startup_set[3] ==1) begin
         if (icap_on == 0)
           startup_set_pulse3 <= 2'b01;
         else begin
           startup_set_pulse3 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse3 <= 2'b00;
         end
       end
       else if (desynch_set[3] == 1 && startup_set_pulse3 == 2'b01) begin
           startup_set_pulse3 <= 2'b11;
           @(posedge cclk_in )
             startup_set_pulse3 <= 2'b00;
      end
    end

   always @(posedge gsr_cmd_out[0] or negedge  rw_en[0])
    if (rw_en[0] == 0)
       gsr_cmd_out_pulse[0] <=  0;
    else
     begin
       gsr_cmd_out_pulse[0] <= 1;
        @(posedge cclk_in );
          @(posedge cclk_in )
           gsr_cmd_out_pulse[0] <=  0;
    end

   always @(posedge gsr_cmd_out[1] or negedge  rw_en[1])
    if (rw_en[1] == 0)
       gsr_cmd_out_pulse[1] <=  0;
    else
     begin
       gsr_cmd_out_pulse[1] <= 1;
        @(posedge cclk_in );
          @(posedge cclk_in )
           gsr_cmd_out_pulse[1] <=  0;
    end

   always @(posedge gsr_cmd_out[2] or negedge  rw_en[2])
    if (rw_en[2] == 0)
        gsr_cmd_out_pulse[2] <=  0;
    else
     begin
       gsr_cmd_out_pulse[2] <= 1;
        @(posedge cclk_in );
          @(posedge cclk_in )
           gsr_cmd_out_pulse[2] <=  0;
    end

   always @(posedge gsr_cmd_out[3] or negedge  rw_en[3])
    if (rw_en[3] == 0)
       gsr_cmd_out_pulse[3] <=  0;
    else
     begin
       gsr_cmd_out_pulse[3] <= 1;
        @(posedge cclk_in );
          @(posedge cclk_in )
           gsr_cmd_out_pulse[3] <=  0;
    end

    reg [31:0] ctl0_reg_tmp0, ctl0_reg_tmp1, ctl0_reg_tmp2, ctl0_reg_tmp3;

    always @(ctl0_reg[0]) begin
      ctl0_reg_tmp0 = ctl0_reg[0];
      if (ctl0_reg_tmp0[9] == 1)
         abort_dis[0] = 1;
      else
         abort_dis[0] = 0;
      if (ctl0_reg_tmp0[3] == 1)
         persist_en[0] = 1;
      else
         persist_en[0] = 0;
      if (ctl0_reg_tmp0[0] == 1)
         gts_usr_b[0] = 1;
      else
         gts_usr_b[0] = 0;
    end

    always @(ctl0_reg[1]) begin
      ctl0_reg_tmp1 = ctl0_reg[1];
      if (ctl0_reg_tmp1[9] == 1)
         abort_dis[1] = 1;
      else
         abort_dis[1] = 0;
      if (ctl0_reg_tmp1[3] == 1)
         persist_en[1] = 1;
      else
         persist_en[1] = 0;
      if (ctl0_reg_tmp1[0] == 1)
         gts_usr_b[1] = 1;
      else
         gts_usr_b[1] = 0;
    end

    always @(ctl0_reg[2]) begin
      ctl0_reg_tmp2 = ctl0_reg[2];
      if (ctl0_reg_tmp2[9] == 1)
         abort_dis[2] = 1;
      else
         abort_dis[2] = 0;
      if (ctl0_reg_tmp2[3] == 1)
         persist_en[2] = 1;
      else
         persist_en[2] = 0;
      if (ctl0_reg_tmp0[2] == 1)
         gts_usr_b[2] = 1;
      else
         gts_usr_b[2] = 0;
    end

    always @(ctl0_reg[3]) begin
      ctl0_reg_tmp3 = ctl0_reg[3];
      if (ctl0_reg_tmp3[9] == 1)
         abort_dis[3] = 1;
      else
         abort_dis[3] = 0;
      if (ctl0_reg_tmp3[3] == 1)
         persist_en[3] = 1;
      else
         persist_en[3] = 0;
      if (ctl0_reg_tmp3[0] == 1)
         gts_usr_b[3] = 1;
      else
         gts_usr_b[3] = 0;
    end

    always @(cor0_reg[0])
    begin
      cor0_reg_tmp0 = cor0_reg[0];
      done_cycle_reg0 = cor0_reg_tmp0[14:12];
      lock_cycle_reg0 = cor0_reg_tmp0[8:6];
      gts_cycle_reg0 = cor0_reg_tmp0[5:3];
      gwe_cycle_reg0 = cor0_reg_tmp0[2:0];

     if (cor0_reg_tmp0[24] == 1'b1)
         done_pin_drv[0] = 1;
      else
         done_pin_drv[0] = 0;

      if (cor0_reg_tmp0[28] == 1'b1)
         crc_bypass[0] = 1;
      else
         crc_bypass[0] = 0;
    end

    always @(cor0_reg[1])
    begin
      cor0_reg_tmp1 = cor0_reg[1];
      done_cycle_reg1 = cor0_reg_tmp1[14:12];
      lock_cycle_reg1 = cor0_reg_tmp1[8:6];
      gts_cycle_reg1 = cor0_reg_tmp1[5:3];
      gwe_cycle_reg1 = cor0_reg_tmp1[2:0];

     if (cor0_reg_tmp1[24] == 1'b1)
         done_pin_drv[1] = 1;
      else
         done_pin_drv[1] = 0;

      if (cor0_reg_tmp1[28] == 1'b1)
         crc_bypass[1] = 1;
      else
         crc_bypass[1] = 0;
    end

    always @(cor0_reg[2])
    begin
      cor0_reg_tmp2 = cor0_reg[2];
      done_cycle_reg2 = cor0_reg_tmp2[14:12];
      lock_cycle_reg2 = cor0_reg_tmp2[8:6];
      gts_cycle_reg2 = cor0_reg_tmp2[5:3];
      gwe_cycle_reg2 = cor0_reg_tmp2[2:0];

     if (cor0_reg_tmp2[24] == 1'b1)
         done_pin_drv[2] = 1;
      else
         done_pin_drv[2] = 0;

      if (cor0_reg_tmp2[28] == 1'b1)
         crc_bypass[2] = 1;
      else
         crc_bypass[2] = 0;
    end

    always @(cor0_reg[3])
    begin
      cor0_reg_tmp3 = cor0_reg[3];
      done_cycle_reg3 = cor0_reg_tmp3[14:12];
      lock_cycle_reg3 = cor0_reg_tmp3[8:6];
      gts_cycle_reg3 = cor0_reg_tmp3[5:3];
      gwe_cycle_reg3 = cor0_reg_tmp3[2:0];

     if (cor0_reg_tmp3[24] == 1'b1)
         done_pin_drv[3] = 1;
      else
         done_pin_drv[3] = 0;

      if (cor0_reg_tmp3[28] == 1'b1)
         crc_bypass[3] = 1;
      else
         crc_bypass[3] = 0;
    end

    always @(cor1_reg[0]) begin
       cor1_reg_tmp0 = cor1_reg[0];
       rbcrc_no_pin[0] = cor1_reg_tmp0[8];
    end

    always @(cor1_reg[1]) begin
       cor1_reg_tmp1 = cor1_reg[1];
       rbcrc_no_pin[1] = cor1_reg_tmp1[8];
    end

    always @(cor1_reg[2]) begin
       cor1_reg_tmp2 = cor1_reg[2];
       rbcrc_no_pin[2] = cor1_reg_tmp2[8];
    end

    always @(cor1_reg[3]) begin
       cor1_reg_tmp3 = cor1_reg[3];
       rbcrc_no_pin[3] = cor1_reg_tmp3[8];
    end

    assign stat_reg_tmp0[31:27] = 5'b00000; 
    assign stat_reg_tmp1[31:27] = 5'b00000; 
    assign stat_reg_tmp2[31:27] = 5'b00000; 
    assign stat_reg_tmp3[31:27] = 5'b00000; 
    assign stat_reg_tmp0[24:21] = 4'bxxx0;
    assign stat_reg_tmp1[24:21] = 4'bxxx0;
    assign stat_reg_tmp2[24:21] = 4'bxxx0;
    assign stat_reg_tmp3[24:21] = 4'bxxx0;
    assign stat_reg_tmp0[17:16] = 2'b0;
    assign stat_reg_tmp1[17:16] = 2'b0;
    assign stat_reg_tmp2[17:16] = 2'b0;
    assign stat_reg_tmp3[17:16] = 2'b0;
    assign stat_reg_tmp0[14] = DONE;
    assign stat_reg_tmp1[14] = DONE;
    assign stat_reg_tmp2[14] = DONE;
    assign stat_reg_tmp3[14] = DONE;
    assign stat_reg_tmp0[13] = (done_o[0] !== 0) ? 1 : 0;
    assign stat_reg_tmp1[13] = (done_o[1] !== 0) ? 1 : 0;
    assign stat_reg_tmp2[13] = (done_o[2] !== 0) ? 1 : 0;
    assign stat_reg_tmp3[13] = (done_o[3] !== 0) ? 1 : 0;
    assign stat_reg_tmp0[12] = INITB;
    assign stat_reg_tmp1[12] = INITB;
    assign stat_reg_tmp2[12] = INITB;
    assign stat_reg_tmp3[12] = INITB;
    assign stat_reg_tmp0[11] = mode_sample_flag;
    assign stat_reg_tmp1[11] = mode_sample_flag;
    assign stat_reg_tmp2[11] = mode_sample_flag;
    assign stat_reg_tmp3[11] = mode_sample_flag;
    assign stat_reg_tmp0[10:8] = mode_pin_in;
    assign stat_reg_tmp1[10:8] = mode_pin_in;
    assign stat_reg_tmp2[10:8] = mode_pin_in;
    assign stat_reg_tmp3[10:8] = mode_pin_in;
    assign stat_reg_tmp0[3] = 1'b1;
    assign stat_reg_tmp1[3] = 1'b1;
    assign stat_reg_tmp2[3] = 1'b1;
    assign stat_reg_tmp3[3] = 1'b1;
    assign stat_reg_tmp0[2] = pll_locked;
    assign stat_reg_tmp1[2] = pll_locked;
    assign stat_reg_tmp2[2] = pll_locked;
    assign stat_reg_tmp3[2] = pll_locked;
    assign stat_reg_tmp0[1] = 1'b0;
    assign stat_reg_tmp1[1] = 1'b0;
    assign stat_reg_tmp2[1] = 1'b0;
    assign stat_reg_tmp3[1] = 1'b0;

    assign stat_reg_tmp0[26:25] = buswidth[0];
    assign stat_reg_tmp0[20:18] = st_state0;
    assign stat_reg_tmp0[15] = id_error_flag[0];
    assign stat_reg_tmp0[7] = ghigh_b[0];
    assign stat_reg_tmp0[6] = gwe_out[0];
    assign stat_reg_tmp0[5] = gts_cfg_b[0];
    assign stat_reg_tmp0[4] = eos_startup[0];
    assign stat_reg_tmp0[0] = crc_err_flag_reg[0]; 

    assign stat_reg_tmp1[26:25] = buswidth[1];
    assign stat_reg_tmp1[20:18] = st_state1;
    assign stat_reg_tmp1[15] = id_error_flag[1];
    assign stat_reg_tmp1[7] = ghigh_b[1];
    assign stat_reg_tmp1[6] = gwe_out[1];
    assign stat_reg_tmp1[5] = gts_cfg_b[1];
    assign stat_reg_tmp1[4] = eos_startup[1];
    assign stat_reg_tmp1[0] = crc_err_flag_reg[1]; 

    assign stat_reg_tmp2[26:25] = buswidth[2];
    assign stat_reg_tmp2[20:18] = st_state2;
    assign stat_reg_tmp2[15] = id_error_flag[2];
    assign stat_reg_tmp2[7] = ghigh_b[2];
    assign stat_reg_tmp2[6] = gwe_out[2];
    assign stat_reg_tmp2[5] = gts_cfg_b[2];
    assign stat_reg_tmp2[4] = eos_startup[2];
    assign stat_reg_tmp2[0] = crc_err_flag_reg[2]; 

    assign stat_reg_tmp3[26:25] = buswidth[3];
    assign stat_reg_tmp3[20:18] = st_state3;
    assign stat_reg_tmp3[15] = id_error_flag[3];
    assign stat_reg_tmp3[7] = ghigh_b[3];
    assign stat_reg_tmp3[6] = gwe_out[3];
    assign stat_reg_tmp3[5] = gts_cfg_b[3];
    assign stat_reg_tmp3[4] = eos_startup[3];
    assign stat_reg_tmp3[0] = crc_err_flag_reg[3]; 
   
    assign stat_reg[0] = stat_reg_tmp0;
    assign stat_reg[1] = stat_reg_tmp1;
    assign stat_reg[2] = stat_reg_tmp2;
    assign stat_reg[3] = stat_reg_tmp3;

    always @(posedge cclk_in or negedge rst_intl)
      if (rst_intl == 0) begin
        st_state0 <= STARTUP_PH0;
        st_state1 <= STARTUP_PH0;
        st_state2 <= STARTUP_PH0;
        st_state3 <= STARTUP_PH0;
        startup_begin_flag0 <= 0;
        startup_begin_flag1 <= 0;
        startup_begin_flag2 <= 0;
        startup_begin_flag3 <= 0;
        startup_end_flag0 <= 0;
        startup_end_flag1 <= 0;
        startup_end_flag2 <= 0;
        startup_end_flag3 <= 0;
      end
      else begin
          st_state0i = st_state0;
          cur_st_tsk(startup_begin_flag0, startup_end_flag0, st_state0,
                     st_state0i, nx_st_state0,lock_cycle_reg0);  

          st_state1i = st_state1;
          cur_st_tsk(startup_begin_flag1, startup_end_flag1, st_state1,
                     st_state1i, nx_st_state1,lock_cycle_reg1);  

          st_state2i = st_state2;
          cur_st_tsk(startup_begin_flag2, startup_end_flag2, st_state2,
                     st_state2i, nx_st_state2,lock_cycle_reg2);  

          st_state3i = st_state3;
          cur_st_tsk(startup_begin_flag3, startup_end_flag3, st_state3,
                     st_state3i, nx_st_state3,lock_cycle_reg3);  
      end

  task cur_st_tsk;
    output stup_bflag;
    output stup_eflag;
    output [2:0] cst_o;
    input [2:0] cst_in;
    input [2:0] nst_in;
    input [2:0] lock_cycle_in;
  begin  
           if (nst_in == STARTUP_PH1) begin
              stup_bflag = 1;
              stup_eflag = 0;
           end
           else if (cst_in == STARTUP_PH7) begin
              stup_eflag = 1;
              stup_bflag = 0;
           end
           if ((lock_cycle_in == 3'b111) || (pll_locked == 1) || (pll_locked == 0 && cst_in != lock_cycle_in)) begin
                cst_o = nst_in;
           end
           else
              cst_o = cst_in;
     end
   endtask

    always @(st_state0 or startup_set_pulse0 or DONE ) begin
        nx_st_tsk(nx_st_state0,st_state0, startup_set_pulse0, done_cycle_reg0);
    end 

    always @(st_state1 or startup_set_pulse1 or DONE ) begin
        nx_st_tsk(nx_st_state1,st_state1, startup_set_pulse1, done_cycle_reg1);
    end 

    always @(st_state2 or startup_set_pulse2 or DONE ) begin
        nx_st_tsk(nx_st_state2,st_state2, startup_set_pulse2, done_cycle_reg2);
    end 

    always @(st_state3 or startup_set_pulse3 or DONE ) begin
        nx_st_tsk(nx_st_state3,st_state3, startup_set_pulse3, done_cycle_reg3);
    end 

  task nx_st_tsk;
    output [2:0] nx_st;
    input [2:0] cur_st;
    input [1:0] stup_pulse;
    input [2:0] done_cycle_in;
  begin
    if (((cur_st == done_cycle_in) && (DONE !== 0)) || (cur_st != done_cycle_in))
      case (cur_st)
      STARTUP_PH0 : if (stup_pulse == 2'b11 ) 
                       nx_st = STARTUP_PH1;
                    else
                       nx_st = STARTUP_PH0;
      STARTUP_PH1 : nx_st = STARTUP_PH2;

      STARTUP_PH2 : nx_st = STARTUP_PH3;

      STARTUP_PH3 : nx_st = STARTUP_PH4;

      STARTUP_PH4 : nx_st = STARTUP_PH5;

      STARTUP_PH5 : nx_st = STARTUP_PH6;

      STARTUP_PH6 : nx_st = STARTUP_PH7;

      STARTUP_PH7 : nx_st = STARTUP_PH0;
      endcase
    end
    endtask

    always @(posedge cclk_in or negedge rst_intl )
      if (rst_intl == 0) begin
          gwe_out <= 4'b0;
          gts_out <= 4'b1111;
          eos_startup <= 4'b0;
          gsr_st_out <= 4'b1111;
          done_o <=  4'b0;
      end
      else  begin
        if (nx_st_state0 == done_cycle_reg0 || st_state0 == done_cycle_reg0) begin
            if (DONE !== 0 || done_pin_drv[0] === 1) 
                  done_o[0] <= 1'b1;
             else 
                 done_o[0] <= 1'bz;
        end
         
        if (nx_st_state1 == done_cycle_reg1 || st_state1 == done_cycle_reg1) begin
            if (DONE !== 0 || done_pin_drv[1] == 1) 
                  done_o[1] <= 1'b1;
             else 
                 done_o[1] <= 1'bz;
        end
         
        if (nx_st_state2 == done_cycle_reg2 || st_state2 == done_cycle_reg2) begin
            if (DONE !== 0 || done_pin_drv[2] == 1) 
                  done_o[2] <= 1'b1;
             else 
                 done_o[2] <= 1'bz;
        end
         
        if (nx_st_state3 == done_cycle_reg3 || st_state3 == done_cycle_reg3) begin
            if (DONE !== 0 || done_pin_drv[3] == 1) 
                  done_o[3] <= 1'b1;
             else 
                 done_o[3] <= 1'bz;
        end
         
         if (st_state0 == gwe_cycle_reg0)  
             gwe_out[0] <= 1;
         if (st_state1 == gwe_cycle_reg1)  
             gwe_out[1] <= 1;
         if (st_state2 == gwe_cycle_reg2)  
             gwe_out[2] <= 1;
         if (st_state3 == gwe_cycle_reg3)  
             gwe_out[3] <= 1;
        
         if (st_state0 == gts_cycle_reg0 )  
             gts_out[0] <= 0;
         if (st_state1 == gts_cycle_reg1 )  
             gts_out[1] <= 0;
         if (st_state2 == gts_cycle_reg2 )  
             gts_out[2] <= 0;
         if (st_state3 == gts_cycle_reg3 )  
             gts_out[3] <= 0;
            
         if (st_state0 == STARTUP_PH6 )
             gsr_st_out[0] <= 0;
         if (st_state1 == STARTUP_PH6 )
             gsr_st_out[1] <= 0;
         if (st_state2 == STARTUP_PH6 )
             gsr_st_out[2] <= 0;
         if (st_state3 == STARTUP_PH6 )
             gsr_st_out[3] <= 0;

         if (st_state0 == STARTUP_PH7 ) 
            eos_startup[0] <= 1;
         if (st_state1 == STARTUP_PH7 ) 
            eos_startup[1] <= 1;
         if (st_state2 == STARTUP_PH7 ) 
            eos_startup[2] <= 1;
         if (st_state3 == STARTUP_PH7 ) 
            eos_startup[3] <= 1;
      end
      
     assign gsr_out[0] = gsr_st_out[0] | gsr_cmd_out[0];
     assign gsr_out[1] = gsr_st_out[1] | gsr_cmd_out[1];
     assign gsr_out[2] = gsr_st_out[2] | gsr_cmd_out[2];
     assign gsr_out[3] = gsr_st_out[3] | gsr_cmd_out[3];
     
     assign abort_dis_bi = abort_dis[ib];

    always @(posedge cclk_in  or negedge rst_intl or 
                posedge abort_flag_rst or posedge csi_b_in)
      if (rst_intl == 0 || abort_flag_rst == 1 || csi_b_in == 1) begin
          abort_flag[ib] <= 0;
          checka_en <= 0;
          rdwr_b_in1 <= rdwr_b_in;
      end
      else  begin
        if (  abort_dis_bi == 0 && csi_b_in == 0) begin
             if ((rdwr_b_in1 != rdwr_b_in) && checka_en != 0) begin
               abort_flag[ib] <= 1;
               if (icap_on == 0)
     $display("Warning: [Unisim %s-10]Warning : RDWRB changes when CSB low, which causes Configuration abort at time %t. Instance %m", MODULE_NAME, $time);
             end
        end
        else
           abort_flag[ib] <= 0;

        rdwr_b_in1 <= rdwr_b_in;
        checka_en <= 1;
      end

    always @(posedge abort_flag[ib])
      begin
         abort_out_en <= 1;
         abort_status <= {cfgerr_b_flag[ib], bus_sync_flag[ib], 1'b0, 1'b1, 4'b1111};
         @(posedge cclk_in)
            abort_status <= {cfgerr_b_flag[ib], 1'b1, 1'b0, 1'b0, 4'b1111};
         @(posedge cclk_in)
            abort_status <= {cfgerr_b_flag[ib], 1'b0, 1'b0, 1'b0, 4'b1111};
         @(posedge cclk_in)
            abort_status <= {cfgerr_b_flag[ib], 1'b0, 1'b0, 1'b1, 4'b1111};
         @(posedge cclk_in) begin
            abort_out_en <= 0;
            abort_flag_rst <= 1;
         end
         @(posedge cclk_in) 
            abort_flag_rst <= 0;
    end
         

function [31:0] bcc_next;
  input [31:0] bcc;
  input [36:0] in;
reg [31:0] x;
reg [36:0] m;
begin
 m = in;
 x = in[31:0] ^ bcc;

 bcc_next[31] = m[32]^m[36]^x[31]^x[30]^x[29]^x[28]^x[27]^x[24]^x[20]^x[19]^x[18]^x[15]^x[13]^x[11]^x[10]^x[9]^x[8]^x[6]^x[5]^x[1]^x[0];

 bcc_next[30] = m[35]^x[31]^x[30]^x[29]^x[28]^x[27]^x[26]^x[23]^x[19]^x[18]^x[17]^x[14]^x[12]^x[10]^x[9]^x[8]^x[7]^x[5]^x[4]^x[0];

 bcc_next[29] = m[34]^x[30]^x[29]^x[28]^x[27]^x[26]^x[25]^x[22]^x[18]^x[17]^x[16]^x[13]^x[11]^x[9]^x[8]^x[7]^x[6]^x[4]^x[3];

 bcc_next[28] = m[33]^x[29]^x[28]^x[27]^x[26]^x[25]^x[24]^x[21]^x[17]^x[16]^x[15]^x[12]^x[10]^x[8]^x[7]^x[6]^x[5]^x[3]^x[2];

 bcc_next[27] = m[32]^x[28]^x[27]^x[26]^x[25]^x[24]^x[23]^x[20]^x[16]^x[15]^x[14]^x[11]^x[9]^x[7]^x[6]^x[5]^x[4]^x[2]^x[1];

 bcc_next[26] = x[31]^x[27]^x[26]^x[25]^x[24]^x[23]^x[22]^x[19]^x[15]^x[14]^x[13]^x[10]^x[8]^x[6]^x[5]^x[4]^x[3]^x[1]^x[0];

 bcc_next[25] = m[32]^m[36]^x[31]^x[29]^x[28]^x[27]^x[26]^x[25]^x[23]^x[22]^x[21]^x[20]^x[19]^x[15]^x[14]^x[12]^x[11]^x[10]^x[8]^x[7]^x[6]^x[4]^x[3]^x[2]^x[1];

 bcc_next[24] = m[35]^x[31]^x[30]^x[28]^x[27]^x[26]^x[25]^x[24]^x[22]^x[21]^x[20]^x[19]^x[18]^x[14]^x[13]^x[11]^x[10]^x[9]^x[7]^x[6]^x[5]^x[3]^x[2]^x[1]^x[0];

 bcc_next[23] = m[32]^m[34]^m[36]^x[31]^x[28]^x[26]^x[25]^x[23]^x[21]^x[17]^x[15]^x[12]^x[11]^x[4]^x[2];

 bcc_next[22] = m[32]^m[33]^m[35]^m[36]^x[29]^x[28]^x[25]^x[22]^x[19]^x[18]^x[16]^x[15]^x[14]^x[13]^x[9]^x[8]^x[6]^x[5]^x[3]^x[0];

 bcc_next[21] = m[34]^m[35]^m[36]^x[30]^x[29]^x[21]^x[20]^x[19]^x[17]^x[14]^x[12]^x[11]^x[10]^x[9]^x[7]^x[6]^x[4]^x[2]^x[1]^x[0];

 bcc_next[20] = m[32]^m[33]^m[34]^m[35]^m[36]^x[31]^x[30]^x[27]^x[24]^x[16]^x[15]^x[3];

 bcc_next[19] = m[32]^m[33]^m[34]^m[35]^x[31]^x[30]^x[29]^x[26]^x[23]^x[15]^x[14]^x[2];

 bcc_next[18] = m[33]^m[34]^m[36]^x[27]^x[25]^x[24]^x[22]^x[20]^x[19]^x[18]^x[15]^x[14]^x[11]^x[10]^x[9]^x[8]^x[6]^x[5]^x[0];

 bcc_next[17] = m[33]^m[35]^m[36]^x[31]^x[30]^x[29]^x[28]^x[27]^x[26]^x[23]^x[21]^x[20]^x[17]^x[15]^x[14]^x[11]^x[7]^x[6]^x[4]^x[1]^x[0];

 bcc_next[16] = m[32]^m[34]^m[35]^x[30]^x[29]^x[28]^x[27]^x[26]^x[25]^x[22]^x[20]^x[19]^x[16]^x[14]^x[13]^x[10]^x[6]^x[5]^x[3]^x[0];

 bcc_next[15] = m[33]^m[34]^x[31]^x[29]^x[28]^x[27]^x[26]^x[25]^x[24]^x[21]^x[19]^x[18]^x[15]^x[13]^x[12]^x[9]^x[5]^x[4]^x[2];

 bcc_next[14] = m[32]^m[33]^x[30]^x[28]^x[27]^x[26]^x[25]^x[24]^x[23]^x[20]^x[18]^x[17]^x[14]^x[12]^x[11]^x[8]^x[4]^x[3]^x[1];

 bcc_next[13] = m[36]^x[30]^x[28]^x[26]^x[25]^x[23]^x[22]^x[20]^x[18]^x[17]^x[16]^x[15]^x[9]^x[8]^x[7]^x[6]^x[5]^x[3]^x[2]^x[1];

 bcc_next[12] = m[32]^m[35]^m[36]^x[31]^x[30]^x[28]^x[25]^x[22]^x[21]^x[20]^x[18]^x[17]^x[16]^x[14]^x[13]^x[11]^x[10]^x[9]^x[7]^x[4]^x[2];

 bcc_next[11] = m[32]^m[34]^m[35]^m[36]^x[28]^x[21]^x[18]^x[17]^x[16]^x[12]^x[11]^x[5]^x[3]^x[0];

 bcc_next[10] = m[33]^m[34]^m[35]^x[31]^x[27]^x[20]^x[17]^x[16]^x[15]^x[11]^x[10]^x[4]^x[2];

 bcc_next[9] = m[33]^m[34]^m[36]^x[31]^x[29]^x[28]^x[27]^x[26]^x[24]^x[20]^x[18]^x[16]^x[14]^x[13]^x[11]^x[8]^x[6]^x[5]^x[3]^x[0];

 bcc_next[8] = m[33]^m[35]^m[36]^x[31]^x[29]^x[26]^x[25]^x[24]^x[23]^x[20]^x[18]^x[17]^x[12]^x[11]^x[9]^x[8]^x[7]^x[6]^x[4]^x[2]^x[1]^x[0];

 bcc_next[7] = m[32]^m[34]^m[35]^x[30]^x[28]^x[25]^x[24]^x[23]^x[22]^x[19]^x[17]^x[16]^x[11]^x[10]^x[8]^x[7]^x[6]^x[5]^x[3]^x[1]^x[0];

 bcc_next[6] = m[32]^m[33]^m[34]^m[36]^x[30]^x[28]^x[23]^x[22]^x[21]^x[20]^x[19]^x[16]^x[13]^x[11]^x[8]^x[7]^x[4]^x[2]^x[1];

 bcc_next[5] = m[33]^m[35]^m[36]^x[30]^x[28]^x[24]^x[22]^x[21]^x[13]^x[12]^x[11]^x[9]^x[8]^x[7]^x[5]^x[3];

 bcc_next[4] = m[34]^m[35]^m[36]^x[31]^x[30]^x[28]^x[24]^x[23]^x[21]^x[19]^x[18]^x[15]^x[13]^x[12]^x[9]^x[7]^x[5]^x[4]^x[2]^x[1]^x[0];

 bcc_next[3] = m[32]^m[33]^m[34]^m[35]^m[36]^x[31]^x[28]^x[24]^x[23]^x[22]^x[19]^x[17]^x[15]^x[14]^x[13]^x[12]^x[10]^x[9]^x[5]^x[4]^x[3];

 bcc_next[2] = m[32]^m[33]^m[34]^m[35]^x[31]^x[30]^x[27]^x[23]^x[22]^x[21]^x[18]^x[16]^x[14]^x[13]^x[12]^x[11]^x[9]^x[8]^x[4]^x[3]^x[2];

 bcc_next[1] = m[32]^m[33]^m[34]^x[31]^x[30]^x[29]^x[26]^x[22]^x[21]^x[20]^x[17]^x[15]^x[13]^x[12]^x[11]^x[10]^x[8]^x[7]^x[3]^x[2]^x[1];

 bcc_next[0] = m[32]^m[33]^x[31]^x[30]^x[29]^x[28]^x[25]^x[21]^x[20]^x[19]^x[16]^x[14]^x[12]^x[11]^x[10]^x[9]^x[7]^x[6]^x[2]^x[1]^x[0];

end
endfunction

function [7:0] bit_revers8;
  input [7:0] din8;
  begin
      bit_revers8[0] = din8[7];
      bit_revers8[1] = din8[6];
      bit_revers8[2] = din8[5];
      bit_revers8[3] = din8[4];
      bit_revers8[4] = din8[3];
      bit_revers8[5] = din8[2];
      bit_revers8[6] = din8[1];
      bit_revers8[7] = din8[0];
  end
endfunction

task rdbk_byte;
  input [31:0] rdbk_reg;
  input integer rd_dcnt;
  begin
    outbus[31:8] <= 24'b0;
   if (rd_dcnt==1)
         outbus[7:0] <= bit_revers8(rdbk_reg[7:0]);
   else if (rd_dcnt==2)
         outbus[7:0] <= bit_revers8(rdbk_reg[15:8]);
   else if (rd_dcnt==3)
         outbus[7:0] <= bit_revers8(rdbk_reg[23:16]);
   else if (rd_dcnt==4)
         outbus[7:0] <= bit_revers8(rdbk_reg[31:24]);
  end
endtask 

task rdbk_wd;
  input [31:0] rdbk_reg;
  input integer rd_dcnt;
  begin
     outbus[31:16] <= 16'b0;
     if (rd_dcnt==1)
         outbus[15:0] <= 16'b0;
     else if (rd_dcnt==2)
         outbus[15:0] <= 16'b0;
     else if (rd_dcnt==3) begin
         outbus[7:0] <= bit_revers8(rdbk_reg[7:0]);
         outbus[15:8] <= bit_revers8(rdbk_reg[15:8]);
     end
     else if (rd_dcnt==4) begin
         outbus[7:0] <= bit_revers8(rdbk_reg[23:16]);
         outbus[15:8] <= bit_revers8(rdbk_reg[31:24]);
     end
  end
endtask
    
task rdbk_2wd;
  input [31:0] rdbk_reg;
  input integer rd_dcnt;
  begin
     if (rd_dcnt==1)
         outbus <= 32'b0;
     else if (rd_dcnt==2)
         outbus <= 32'b0;
     else if (rd_dcnt==3)
         outbus <= 32'b0;
     else if (rd_dcnt==4) begin
         outbus[7:0] <= bit_revers8(rdbk_reg[7:0]);
         outbus[15:8] <= bit_revers8(rdbk_reg[15:8]);
         outbus[23:16] <= bit_revers8(rdbk_reg[23:16]);
         outbus[31:24] <= bit_revers8(rdbk_reg[31:24]);
     end
  end
endtask

endmodule

`endcelldefine
