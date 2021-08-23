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
//------------------------------------------------------
// Test Cases
//------------------------------------------------------

int x;
integer ddrfreq_MHz;
//------------------------------------------------------
// Test Cases
//------------------------------------------------------
task initialize_mem;
    begin
        `ifdef RAMFILEPATH
            $display("INFO: Initializing ITCM.\n");
            // MCU ITCM
            `MCU_ITCM_HIER.tcm_sram[0].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b0_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[1].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b1_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[2].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b2_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[3].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b3_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[4].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b4_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[5].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b5_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[6].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b6_byte03_byte00.ram"});
            `MCU_ITCM_HIER.tcm_sram[7].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "itcm_2048x4_tcm0_b7_byte03_byte00.ram"});

            $display("INFO: Initializing ITCM.\n");
            // MCU DTCM
            `MCU_DTCM_HIER.tcm_sram[0].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b0_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[1].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b1_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[2].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b2_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[3].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b3_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[4].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b4_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[5].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b5_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[6].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b6_byte03_byte00.ram"});
            `MCU_DTCM_HIER.tcm_sram[7].tcm_32bit.tcm_sram.loadmem ({`RAMFILEPATH, "dtcm_2048x4_tcm0_b7_byte03_byte00.ram"});
        `endif

        $display("INFO: Mem Initialization task done .\n");
    end
endtask

task ddr_boot ;
    output int err;
    integer indx;
    logic zqcal_val;
    static integer max_pcal=63;
    static integer max_ncal=31;
    logic [3:0] pi_gear;
begin
      ddrfreq_MHz = vcoFreq1 ;
      $display("INFO DT Boot : Freq set in DT tasks = %d MHz",ddrfreq_MHz ) ;
      err = 0;
      // ibias enable
      set_ibias_en(1'b1);
      #10ns; wait_hclk (1);
      set_ldo_en(1'b1);
      #10ns; wait_hclk (1);
      // refgen
      set_refgen_en(1'b1);

      // ZQCAL start (current from f2i, above, is enabled)
      set_zqcal_en(1'b1);
      set_zqcal_pd_sel(1'b1);
      set_zqcal_ncal_code('d0);

      //increment NCAL, stop when zqcal_val=0
      for(indx=0;indx<max_ncal+1;indx=indx+1) begin
         set_zqcal_ncal_code(indx);
         #200ns;wait_hclk (1);
         read_zqcal_comp_val(zqcal_val);       //read status of zqcal comparator value
         if(~zqcal_val) indx=max_ncal+1;       //if zqcal=0, exit for loop
      end

      //increment PCAL, stop when zqcal_val=0
      set_zqcal_pd_sel(1'b0);
      for(indx=0;indx<max_pcal+1;indx=indx+1) begin
         set_zqcal_pcal_code(indx);
         #200ns;wait_hclk (1);
         read_zqcal_comp_val(zqcal_val);     //read status of zqcal comparator value
         if(~zqcal_val) indx=max_pcal+1;     //if zqcal=0, exit for loop
      end

      #1us;wait_hclk (1);

      set_pll_fast_run(.pll_vco1_freq_MHz(ddrfreq_MHz), .pll_vco2_freq_MHz(ddrfreq_MHz), .vco_sel(1), .err(err));

      set_vco0_pll_clk_en(1'b1);
      set_mcu_clk_sel(1'b1);
      wait_hclk (4);

      set_pll0_div_clk_rst(1'b0);
      set_gfcm_en(1'b1);
      set_pll0_div_clk_en(1'b1);
      sw_phy_clk_en (1'b1);
      set_dfi_buf_clken(1'b0) ;

      // Enable PIs before CSP SYNC to flush out X propagation
      case(ddrfreq_MHz)
         2134: begin pi_gear = 4'd10 ; end
         3200: begin pi_gear = 4'd15 ; end
         default: begin pi_gear = 4'd10 ; $display ("Error: Unsupported Frequency = %d", ddrfreq_MHz); end
      endcase

      // Setup TX PIs for 90 degree offset
      set_tx_dqs_sdr_rt_pi_cfg (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_tx_match_pi_cfg      (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(pi_gear), .xcpl('0) );
      set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_tx_dq_sdr_rt_pi_cfg  (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_tx_dq_ddr_pi_cfg     (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_tx_dq_qdr_pi_cfg     (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_rx_rdqs_pi_cfg       (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));
      set_rx_ren_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h1));
      set_rx_rcs_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(pi_gear), .xcpl('0), .code(6'h0));

     `ifdef GLS
      // Added for GLS
      dfi_buf_flush_dp();
     `endif

      // CSP Sync to flush X propagation.
      wait_hclk (4);
      sw_csp_byte_sync();
      wait_hclk (4);

     `ifndef GLS
      set_dfi_traffic_ovr_cfg (.sw_mode(1'b0), .sw_en(1'b1));
     `endif
end
endtask

//------------------------------------------------------
// Test Cases
//------------------------------------------------------
  task t_ddr_spice;
    output int err;
    int err_temp;
    int err_cnt;
    int bl;
  begin
      err = 0;
      err_temp = 0;
      err_cnt  = 0;

      `ifdef GLS
      fn = {"wddr_1x32.uvm/gls_wddr_1x32_spice_lb.uvm.sv"};
      `else
      fn = {"wddr_1x32.uvm/wddr_1x32_spice_lb.uvm.sv"};
      `endif

      $display("INFO: Open  file %s ...\n", fn );
      fd = $fopen(fn,"w");

      wait_hclk (1);
      ddr_boot(err) ;
      set_dfi_ca_rddata_en (.en(1'b1));  // Enable CA RDDATA en for CA loopback.

      // Set lpde delay
      // 90p delay through DQ TX LPDE, 98ps Delay through DQS TX LPDE
      set_wrdq_lpde_dly  (.byte_sel(ALL),    .rank_sel(RANK_ALL), .dq(99),  .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h21), .r1_dly(6'h21));
      set_rdsdr_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      set_rdsdr_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      // 20ps delay through DQS RX diff PAD. this is the skew between DQ and DQS to capture DQ in SA.
      set_dq_dqs_drvr_cfg   (.byte_sel(ALL), .dqs_freq_MHz(ddrfreq_MHz), .lb_mode(1), .wck_mode(1'b0), .se_mode(1'b0), .termination(1'b1) ) ;
      set_dq_dqs_rcvr_cfg   (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz(ddrfreq_MHz), .dly_ps('d0));

      // Enable IO loopback
      set_tx_io_cmn_cfg_dt    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b1), .ncal('d14), .pcal('d45));

      //----------------------------------------------------------------------------------
      // Case1: DDR - DP 4to1 - egress QDR2to1
      // ---------------------------------------------------------------------------------
      err_temp = 0;
      err_cnt = 0;

      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );

      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(0),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );// WCK
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );// DQS/Parity

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x02 "Egress mode (one-hot) - 0:SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6:BSCAN";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (99), .mode('h04) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(99), .mode('h04) );

      set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode (DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),         .rgb_mode (DGB_4TO1_HF), .fgb_mode(FGB_4TO4),   .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),        .tgb_mode (DGB_4TO1_HF), .wgb_mode(WGB_1TO1));

      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_4TO4);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h2), .wck_oe_cycles(4'h1), .ie_cycles(4'h2), .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      bl = 64;
      gen_dfi_data_packet(
         .tphy_wrdata     ('h4),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(DDR_4));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 1 DFI 1:2 mode DDR Transaction PASSED.");
      else              $display ("ERROR: Case 1 DFI 1:2 mode DDR Transactions FAILED.");

      $fclose(fd);

       #100ns;
    end
  endtask

  task t_ddr_sanity;
    output int err;
    int err_temp;
    int err_cnt;
    int bl;
  begin
      err = 0;
      err_temp = 0;
      err_cnt  = 0;

      wait_hclk (1);
      ddr_boot(err) ;
      set_dfi_ca_rddata_en (.en(1'b1));  // Enable CA RDDATA en for CA loopback.

      // Set lpde delay
      // 90p delay through DQ TX LPDE, 98ps Delay through DQS TX LPDE
      set_wrdq_lpde_dly  (.byte_sel(ALL),    .rank_sel(RANK_ALL), .dq(99),  .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h21), .r1_dly(6'h21));
      set_rdsdr_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      set_rdsdr_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      // 20ps delay through DQS RX diff PAD. this is the skew between DQ and DQS to capture DQ in SA.
      set_dq_dqs_drvr_cfg   (.byte_sel(ALL), .dqs_freq_MHz(ddrfreq_MHz), .lb_mode(1), .wck_mode(1'b0), .se_mode(1'b0), .termination(1'b1) ) ;
      set_dq_dqs_rcvr_cfg   (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz(ddrfreq_MHz), .dly_ps('d0));

      // Enable IO loopback
      set_tx_io_cmn_cfg_dt    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b1), .ncal('d14), .pcal('d45));

      //----------------------------------------------------------------------------------
      // Case1: SDR 1:1 - egress DDR2to1
      // ---------------------------------------------------------------------------------
      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200) );
      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200) );

      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd0),  .rank_sel(RANK_ALL), .x_sel    ('h7654_3210) );  //WCK
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel    ('h7654_3210) );  //DQS/Parity

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x01 "Egress mode (one-hot) - 0: SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6: BSCAN ";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd0),  .mode('h02) ); // WCK DDR2to1.
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd1),  .mode('h02) ); // DQS DDR2to1.

      set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // for DQ, lopback DQS clock
      set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // for CA, loop back CK clock
      set_tx_gb             (.byte_sel(ALL),    .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));

      bl = 32;
      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_1TO1);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h1),   .wck_oe_cycles(4'h1),   .ie_cycles(4'h2),       .re_cycles(4'h6), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0)); // RE extended to 6 cycles to confirm independent control on RE.
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h3),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(SDR_1));
       err_cnt = err_cnt+err_temp;
       check_dfibuf_eg_data(.byte_sel(CA), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(SDR_1));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 1 SDR Transaction PASSED.");
      else              $display ("ERROR: Case 1 SDR Transactions FAILED.");

      //----------------------------------------------------------------------------------
      // Case2: DDR - DP 2to1 - egress DDR2to1 - freq ratio 1:1
      // ---------------------------------------------------------------------------------
      err_temp = 0;
      err_cnt = 0;

      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x01 "Egress mode (one-hot) - 0: SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6: BSCAN ";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02) );

      set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),        .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_1TO1));

      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_2TO2);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h3),   .wck_oe_cycles(4'h1),   .ie_cycles(4'h2),       .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h4),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(DDR_2));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 2 DDR Transaction PASSED.");
      else              $display ("ERROR: Case 2 DDR Transactions FAILED.");

      //----------------------------------------------------------------------------------
      // Case3: DDR - DP 4to1 - egress QDR2to1
      // ---------------------------------------------------------------------------------
      err_temp = 0;
      err_cnt = 0;

      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );

      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(0),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );// WCK
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120) );// DQS/Parity

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x02 "Egress mode (one-hot) - 0:SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6:BSCAN";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (99), .mode('h04) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(99), .mode('h04) );

      set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode (DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),         .rgb_mode (DGB_4TO1_HF), .fgb_mode(FGB_4TO4),   .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),        .tgb_mode (DGB_4TO1_HF), .wgb_mode(WGB_1TO1));

      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_4TO4);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h2),   .wck_oe_cycles(4'h1),      .ie_cycles(4'h2),       .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h4),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(DDR_4));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 3 DFI 1:2 mode DDR Transaction PASSED.");
      else              $display ("ERROR: Case 3 DFI 1:2 mode DDR Transactions FAILED.");

      //----------------------------------------------------------------------------------
      // Case4: DFI 1:4 mode - DDR - DP 4to1 - egress QDR2to1
      // ---------------------------------------------------------------------------------

       #100ns;
    end
  endtask

  task t_irdqs_sanity;
    output int err;
    int err_temp;
    int err_cnt;
    int bl;
  begin
      //force `TB_HIER.u_ctrl_plane.i_pll_clk = 1'b0 ;
      err = 0;
      err_temp = 0;
      err_cnt  = 0;

      wait_hclk (1);
      ddr_boot(err);
      set_dfi_ca_rddata_en (.en(1'b1));  // Enable CA RDDATA en for CA loopback.

      // Set lpde delay
      // 90p delay through DQ TX LPDE, 98ps Delay through DQS TX LPDE
      set_wrdq_lpde_dly  (.byte_sel(ALL),    .rank_sel(RANK_ALL), .dq(99),  .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h01), .r1_dly(6'h01));
      set_wrdqs_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL), .dqs(99), .gear(2'h2), .r0_dly(6'h21), .r1_dly(6'h21));
      set_rdsdr_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      set_rdsdr_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL),           .gear(2'h2), .r0_dly(6'h1A), .r1_dly(6'h1A));
      // 20ps delay through DQS RX diff PAD. this is the skew between DQ and DQS to capture DQ in SA.
      set_dq_dqs_drvr_cfg   (.byte_sel(ALL), .dqs_freq_MHz(ddrfreq_MHz), .lb_mode(1), .wck_mode(1'b0), .se_mode(1'b0), .termination(1'b1) ) ;
      set_dq_dqs_rcvr_cfg   (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz(ddrfreq_MHz), .dly_ps('d0));

      // Enable IO loopback
      set_tx_io_cmn_cfg_dt    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b1), .ncal('d14), .pcal('d45));

      //----------------------------------------------------------------------------------
      // Case1: SDR 1:1 - egress DDR2to1
      // ---------------------------------------------------------------------------------
      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200) );
      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200) );

      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd0),  .rank_sel(RANK_ALL), .x_sel    ('h7654_3210) );  //WCK
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel    ('h7654_3210) );  //DQS/Parity

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x01 "Egress mode (one-hot) - 0: SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6: BSCAN ";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd0),  .mode('h02) ); // WCK DDR2to1.
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd1),  .mode('h02) ); // DQS DDR2to1.

      set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),    .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));

      bl = 32;
      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_1TO1);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h1),   .wck_oe_cycles(4'h1),   .ie_cycles(4'h2),       .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h3),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(SDR_1));
       err_cnt = err_cnt+err_temp;
       check_dfibuf_eg_data(.byte_sel(CA), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(SDR_1));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 1 SDR Transaction PASSED.");
      else              $display ("ERROR: Case 1 SDR Transactions FAILED.");

      //----------------------------------------------------------------------------------
      // Case2: DDR - DP 2to1 - egress DDR2to1 - freq ratio 1:1
      // ---------------------------------------------------------------------------------
      err_temp = 0;
      err_cnt = 0;

      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x01 "Egress mode (one-hot) - 0: SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6: BSCAN ";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02) );

      set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),        .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_1TO1));

      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_2TO2);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h3),   .wck_oe_cycles(4'h1),   .ie_cycles(4'h2),       .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h4),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(DDR_2));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 2 DDR Transaction PASSED.");
      else              $display ("ERROR: Case 2 DDR Transactions FAILED.");

      //----------------------------------------------------------------------------------
      // Case3: DDR - DP 2to1 - egress DDR2to1 - freq ratio 1:1
      // ---------------------------------------------------------------------------------
      err_temp = 0;
      err_cnt = 0;

      set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_sdr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000) );
      set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210) );

      set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );
      set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000) );
      set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210) );

      //EGRESS_MODE 6:0 DEF=0x01 "Egress mode (one-hot) - 0: SDR, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1, 6: BSCAN ";
      set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02) );
      set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02) );

      // Select IR mode
      set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_2TO1_IR), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // DQS Loop back
      set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // CK  Loop back
      set_tx_gb             (.byte_sel(ALL),    .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_1TO1));

      // IRDQS static delay to meet timing
      set_rx_rdqs_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'd10), .xcpl('0), .code(6'd26));

      //DFI Configuration
      set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
      set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfiwenctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      //set_dfiwckctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_2TO2), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b1));
      set_dfi_rdgb_mode      (DFIRGB_2TO2);
      set_dfi_paden_pext_cfg (.wrd_oe_cycles(4'h1),   .wck_oe_cycles(4'h1),   .ie_cycles(4'h2),       .re_cycles(4'h2), .ren_cycles(4'h0), .wrd_en_cycles(4'h0), .rcs_cycles(4'h0));
      set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h7), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h3));

      gen_dfi_data_packet(
         .tphy_wrdata     ('h4),
         .tphy_wrcslat    ('h0),
         .tphy_wrlat      ('h1),
         .rank_sel        ('h1),
         .cadce_pnum      ('d0),
         .cacs_pnum       ('d0),
         .cacke_pnum      ('d0),
         .caaddr_pnum     ('d0),
         .wckcs_pnum      ('d0),
         .wcken_pnum      ('d0),
         .wckt_pnum       ('d0),
         .wren_pnum       ('d0),
         .par_pnum        ('d0),
         .wrcs_pnum       ('d0),
         .rden_pnum       ('d0),
         .wr_pnum         ('d0),
         .bl              (bl),
         .ts_offset       ('d8),
         .wrd_packet      (ig_wdata_load),
         .rd_exp_packet   (eg_rdata_expected)
      );

      sw_csp_byte_sync();
      set_dfi_buf_mode(1'b1);

      // Reset FIFO pointers due to Xs on the clocks
      //set_fifo_clr;
      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      for (x=0; x <= N; x=x+1) begin
         push_dfi_ig_buf (ig_wdata_load[x]);
      end

      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      for (x=0; x < bl/8; x=x+1) begin
       pop_dfi_eg_buf(eg_rdata_pop[x]) ;
       check_dfibuf_eg_data(.byte_sel(DQ_ALL), .rdata(eg_rdata_pop[x]), .rdata_expected(eg_rdata_expected[x]), .err_cnt(err_temp), .mode(DDR_2));
       err_cnt = err_cnt+err_temp;
      end

      wait_hclk (10);
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      err = err+err_cnt;
      if (err_cnt == 0) $display ("INFO: Case 3 DDR Transaction PASSED.");
      else              $display ("ERROR: Case 3 DDR Transactions FAILED.");

      #100ns;
    end
  endtask

`ifndef GLS
  task t_pll_sanity_closed;
    output int err;

    integer indx;
    logic zqcal_val;
    static integer max_pcal=63;
    static integer max_ncal=31;
    logic [31:0] rdata;
    real pmon_nand_count;
    logic pmon_nand_done;
    real pmon_nor_count;
    logic pmon_nor_done;
    logic pll_core_ready;
    logic [5:0] band_vco0_val;
    logic [5:0] fine_vco0_val;
    logic [5:0] band_vco1_val;
    logic [5:0] fine_vco1_val;
    logic [5:0] band_vco2_val;
    logic [5:0] fine_vco2_val;
    real  vco0_freq;
    real  vco1_freq;
    real  vco2_freq;
    static real  posedge_sig=0;
    static real  posedge_sig_pre=0;
    static real  period_sig=0;
    static real  freq_sig=0;
    integer x;
  begin
      err = 0;

      // igen enable
      set_ibias_en(1'b1);
      #10ns;
      set_ldo_en(1'b1);
      #10ns;
      // refgen
      set_refgen_en(1'b1);

      // ZQCAL start (current from f2i, above, is enabled)
      set_zqcal_en(1'b1);
      set_zqcal_pd_sel(1'b1);
      set_zqcal_ncal_code('d0);

      //increment NCAL, stop when zqcal_val=0
      for(indx=0;indx<max_ncal+1;indx=indx+1) begin
         set_zqcal_ncal_code(indx);
         #200ns;
         read_zqcal_comp_val(zqcal_val);       //read status of zqcal comparator value
         if(~zqcal_val) indx=max_ncal+1;       //if zqcal=0, exit for loop
      end

      //increment PCAL, stop when zqcal_val=0
      set_zqcal_pd_sel(1'b0);
      for(indx=0;indx<max_pcal+1;indx=indx+1) begin
         set_zqcal_pcal_code(indx);
         #200ns;
         read_zqcal_comp_val(zqcal_val);     //read status of zqcal comparator value
         if(~zqcal_val) indx=max_pcal+1;     //if zqcal=0, exit for loop
      end

      //PMON setup
      //enable analog PMONs
      set_pmon_dig_init();
      set_pmon_ana_nand_en(1'b1);
      set_pmon_ana_nor_en(1'b1);

      rst_pmon_dig(1'b1);
      #100ns;
      rst_pmon_dig(1'b0);
      set_pmon_dig_nand_en(1'b1);
      set_pmon_dig_nor_en(1'b1);
      set_ldo_vref_ctrl_val(8'h00);
      ///// END of PMON setup
      #1us;

      set_pll_init ( );
      new_set_pll_init ( );
      reset_pll_core;

      // wait to lock (open loop= 200ns, closed loop=300us)
      wait_time_pll_lock();

      set_gfcm_en(1'b1);
      set_pll0_div_clk_en(1'b1);

      new_poll_ready(pll_core_ready);
      //$display("VCO0 BAND VAL=%h, FINE VAL=%h at %t", band_vco0_val, fine_vco0_val,$realtime);
      $display("INFO: PLL CORE READY=%b", pll_core_ready);

      new_cal_band_fll(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(2134),.fll_refclk_count(64),.vco_sel(1));

      #200us;
      new_read_band_fll_val(.rdata_band(band_vco0_val),.rdata_fine(fine_vco0_val),.vco_sel(0));
      $display("INFO: VCO0 BAND VAL=%h, FINE VAL=%h at %t", band_vco0_val, fine_vco0_val,$realtime);
      new_read_band_fll_val(.rdata_band(band_vco1_val),.rdata_fine(fine_vco1_val),.vco_sel(1));
      $display("INFO: VCO1 BAND VAL=%h, FINE VAL=%h at %t", band_vco1_val, fine_vco1_val,$realtime);

      new_cal_band_fll(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(1067),.fll_refclk_count(64),.vco_sel(2));

      #200us;
      new_read_band_fll_val(.rdata_band(band_vco2_val),.rdata_fine(fine_vco2_val),.vco_sel(2));
      $display("INFO: VCO2 BAND VAL=%h, FINE VAL=%h %t", band_vco2_val, fine_vco2_val,$realtime);

      new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(2133),.vco_sel(1),.band(band_vco1_val),.fine(fine_vco1_val));
      new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(1067),.vco_sel(2),.band(band_vco2_val),.fine(fine_vco2_val));
      //new_set_vco_prep(.ref_clk_MHz(19.2),.vco_clk_MHz(2134),.vco_sel(1),.band('h2B),.fine('h1A));
      //new_set_vco_prep(.ref_clk_MHz(19.2),.vco_clk_MHz(1067),.vco_sel(2),.band('h0C),.fine('h00));
      new_set_vco_switch(.en(1'b1));
      #200us;
      new_cal_band_fll(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(384),.fll_refclk_count(64),.vco_sel(0));

      #200us;
      new_read_band_fll_val(.rdata_band(band_vco1_val),.rdata_fine(fine_vco1_val),.vco_sel(1));
      $display("INFO: VCO1 BAND VAL=%h, FINE VAL=%h at %t", band_vco1_val, fine_vco1_val,$realtime);

      new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(2133),.vco_sel(1),.band(band_vco1_val),.fine(fine_vco1_val));
      #200;

      fork : vco0
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco0_clk)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               posedge_sig_pre = posedge_sig;
               freq_sig = 1e3/period_sig;
            end
            disable vco0;
         end
         begin
            #100ns;
            disable vco0;
         end
      join
      //$display("VCO0 period = %f", period_sig);
      $display("INFO: VCO0 freq = %f", freq_sig);
      if(freq_sig<370 || freq_sig>390) begin
         err=err+1;
         $display("ERROR: pll_sanity_closed VCO0 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO0 frequency is CORRECT");

      fork : vco1
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco1_clk0)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               posedge_sig_pre = posedge_sig;
               freq_sig = 1e3/period_sig;
            end
            disable vco1;
         end
         begin
            #100ns;
            disable vco1;
         end
      join
      //$display("VCO1 period = %f", period_sig);
      $display("INFO: VCO1 freq = %f", freq_sig);
      if(freq_sig<2000 || freq_sig>2160) begin
         err=err+1;
         $display("ERROR: pll_sanity_closed VCO1 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO1 frequency is CORRECT");

      fork : vco2
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco2_clk0)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               freq_sig = 1e3/period_sig;
               posedge_sig_pre = posedge_sig;
            end
            disable vco2;
         end
         begin
            #100ns;
            disable vco2;
         end
      join
      //$display("VCO2 period = %f", period_sig);
      $display("INFO: VCO2 freq = %f", freq_sig);
      if(freq_sig<1060 || freq_sig>1080) begin
         err=err+1;
         $display("ERROR: pll_sanity_closed VCO2 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO2 frequency is CORRECT");

     //PMON read values
      read_pmon_dig_nand_done(pmon_nand_done);
      read_pmon_dig_nand_val(pmon_nand_count);
      read_pmon_dig_nor_done(pmon_nor_done);
      read_pmon_dig_nor_val(pmon_nor_count);

      //if(pmon_nand_done!==1'b1)

      $display("INFO: PMON_NAND_COUNT=%f", pmon_nand_count/256.0);
      $display("INFO: PMON_NOR_COUNT=%f", pmon_nor_count/256.0);

      $display("INFO: PMON test PASS!");
      $display("INFO: PLL test completed!!!!!!!!");
    end
  endtask

  task t_pll_sanity_open;
    output int err;
    logic [31:0] rdata;
    logic pll_core_ready;
    logic [5:0] band_vco0_val;
    logic [5:0] fine_vco0_val;
    static logic [5:0] band_vco1_val='h10;
    static logic [5:0] fine_vco1_val='h00;
    static logic [5:0] band_vco2_val='h04;
    static logic [5:0] fine_vco2_val='h00;
    real  vco0_freq;
    real  vco1_freq;
    real  vco2_freq;
    static real  posedge_sig=0;
    static real  posedge_sig_pre=0;
    static real  period_sig=0;
    static real  freq_sig=0;
    integer x;
    integer pll_vco1_freq_MHz;
    integer pll_vco2_freq_MHz;
  begin
      err = 0;

      // setup and run PLL
      pll_vco1_freq_MHz=2134;
      pll_vco2_freq_MHz=1067;
      set_pll_fast_run(.pll_vco1_freq_MHz(pll_vco1_freq_MHz), .pll_vco2_freq_MHz(pll_vco2_freq_MHz), .vco_sel(2), .err(err));

      //Check VCO frequencies #delays
      vco0_freq = `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.IVCO0.VCO.freq/1e6;
      vco1_freq = `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.IVCO1.VCO.freq/1e6;
      vco2_freq = `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.IVCO2.VCO.freq/1e6;
      //   $display("VCO0: pll_sanity_open VCO0 frequency  received=%f",vco0_freq);
      if(vco0_freq<380 || vco0_freq>390) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO0 frequency incorrect, received=%f",vco0_freq);
      end
      if(vco1_freq<pll_vco1_freq_MHz-15 || vco1_freq>pll_vco1_freq_MHz+15) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO1 frequency incorrect, received=%f",vco1_freq);
      end
      if(vco2_freq<pll_vco2_freq_MHz-15 || vco2_freq>pll_vco2_freq_MHz+15) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO2 frequency incorrect, received=%f",vco2_freq);
      end

      //Check VCO frequencies measuring the delays at PLL boundary
      fork : vco0
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco0_clk)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               posedge_sig_pre = posedge_sig;
               freq_sig = 1e3/period_sig;
            end
            disable vco0;
         end
         begin
            #100ns;
            disable vco0;
         end
      join
      //$display("VCO0 period = %f", period_sig);
      $display("INFO: VCO0 freq = %f", freq_sig);
      if(freq_sig<380 || freq_sig>390) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO0 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO0 frequency is CORRECT");

      fork : vco1
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco1_clk0)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               posedge_sig_pre = posedge_sig;
               freq_sig = 1e3/period_sig;
            end
            disable vco1;
         end
         begin
            #100ns;
            disable vco1;
         end
      join
      //$display("VCO1 period = %f", period_sig);
      $display("INFO: VCO1 freq = %f", freq_sig);
      if(freq_sig<pll_vco1_freq_MHz-15 || freq_sig>pll_vco1_freq_MHz+15) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO1 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO1 frequency is CORRECT");

      fork : vco2
         begin
            for(x=0;x<10;x=x+1) begin
               @(posedge `TB_HIER.u_cmn.CMN.u_cmn_wrapper.u_wphy_rpll_mvp_4g.vco2_clk0)
               posedge_sig = $realtime;
               period_sig = posedge_sig - posedge_sig_pre;
               freq_sig = 1e3/period_sig;
               posedge_sig_pre = posedge_sig;
            end
            disable vco2;
         end
         begin
            #100ns;
            disable vco2;
         end
      join
      //$display("VCO2 period = %f", period_sig);
      $display("INFO: VCO2 freq = %f", freq_sig);
      if(freq_sig<pll_vco2_freq_MHz-15 || freq_sig>pll_vco2_freq_MHz+15) begin
         err=err+1;
         $display("ERROR: pll_sanity_open VCO2 frequency measured incorrect, received=%f",freq_sig);
      end
      else
         $display("INFO: VCO2 frequency is CORRECT");

      //enable glitch-free mux
      set_gfcm_en(1'b1);
      //set_pll0_div_clk_en(1'b1);

      #1us;

      $display("INFO: PLL Open Loop test completed!!!!!!!!");
    end
  endtask
`endif

task t_mcu_sanity;
    output int err;

    integer indx;
    logic zqcal_val;
    static integer max_pcal=63;
    static integer max_ncal=31;
    begin
        err = 0;

        #500ns;

        initialize_mem ;
        #1us;

        // ibias enable
        set_ibias_en(1'b1);
        #10ns;
        set_ldo_en(1'b1);
        #10ns;
        // refgen
        set_refgen_en(1'b1);

        reset_pll_core;
        set_pll_init ( );
        // set bands for all VCOs
        set_band_vco_lp_value (.vco_freq_MHz(422));
        set_band_vco_hp_value (.vco_freq_MHz(2112),.vco_sel(1));
        set_band_vco_hp_value (.vco_freq_MHz(1075),.vco_sel(2));

        // enable feedback and set fbdiv for VCO1
        set_fbdiv_vco_value (.vco_freq_MHz(2112),.vco_sel(1));

        // enable all VCOs
        set_vcos_en (1'b1);

        // wait to lock
        #200ns

        set_vco0_pll_clk_en(1'b1);
        set_mcu_clk_sel(1'b1);
        wait_hclk (4);

        set_pll0_div_clk_rst(1'b0);
        set_gfcm_en(1'b1);
        set_pll0_div_clk_en(1'b1);
        sw_phy_clk_en (1'b1);

        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
        fork
            begin
                #1000us ;
                $display($realtime, " ",  $time , " FATAL: Simulation Timeout.");
                $finish;
            end
            begin
                check_irq();
            end
            begin
                check_mcu_exec_status(err);
            end
        join_any
        disable fork;

        end
    endtask

task t_mcu_boot;
    output int err;

    integer indx;
    logic zqcal_val;
    static integer max_pcal=63;
    static integer max_ncal=31;
    begin
        err = 0;

        #500ns;

        initialize_mem ;

        #1us;
        config_vips(200,1);

        set_ldo_en(1'b1);
        #10ns;
        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
        fork
            begin
                check_irq();
            end
            begin
                check_mcu_exec_status(err);
            end
        join_any
        disable fork;

        end
endtask

task t_mcu_host;
    output int err;

    integer indx;
    logic zqcal_val;
    logic [31:0] id;
    logic [31:0] data;
    static integer max_pcal=63;
    static integer max_ncal=31;
    begin
        err = 0;

        #500ns;

        initialize_mem ;

        #1us;
        set_ldo_en(1'b1);
        #10ns;
        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
        fork
            begin
                // Wait for message Boot is done
                phy2host_receive_msg( id, data);
                $display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);

                host2phy_sw_freqswitch(1);
                phy2host_receive_msg( id, data);
                $display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);
                wait_hclk (100);

                host2phy_sw_freqswitch(2);
                phy2host_receive_msg( id, data);
                $display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);
                wait_hclk (100);

                host2phy_sw_freqswitch(4);
                phy2host_receive_msg( id, data);
                $display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);
                wait_hclk (100);

                host2phy_sw_freqswitch(9);
                phy2host_receive_msg( id, data);
                $display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);
                wait_hclk (100);

                host2phy_stopsim(0);
            end
            begin
                check_irq();
            end
            begin
                check_mcu_exec_status(err);
            end
            begin
                #10000us ;
                $display($realtime, " ",  $time , " FATAL: Simulation Timeout.");
                $finish;
            end
        join_any
        disable fork;

            //phy2host_receive_msg( id, data);
            //$display ("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data);
        end
endtask

  task t_dfi_status_sanity;
     output int err;
     logic ovr, req, ack;
  begin
     err = 0;
     #1us;

      ddr_boot(err);

     // Simple SW override status request
     {ovr, req} = {1'b1, 1'b1};
     set_dfi_status_req(ovr, req);
     do begin
        get_dfi_status_ack(ack);
     end while (!ack);
     {ovr, req} = {1'b1, 1'b0};
     set_dfi_status_req(ovr, req);

     #10ns;

     $display("DFI Sanity test completed!!!!!!!!");
  end
  endtask

  task t_freq_sw_sanity;
     output int err;
     logic ovr, req, ack, switch_done;
     logic [31:0] wdata;
  begin
     err = 0;
     #1us;

     // ibias enable
     set_ibias_en(1'b1);
     #10ns;
     set_ldo_en(1'b1);
     #10ns;
     // refgen
     set_refgen_en(1'b1);

     reset_pll_core;
     set_pll_init ( );
     // set bands for all VCOs
     set_band_vco_lp_value (.vco_freq_MHz(400));
     set_band_vco_hp_value (.vco_freq_MHz(2134),.vco_sel(1));
     set_band_vco_hp_value (.vco_freq_MHz(1067),.vco_sel(2));

     // enable feedback and set fbdiv for VCO1
     set_fbdiv_vco_value (.vco_freq_MHz(2134),.vco_sel(1));

     // enable all VCOs
     set_vcos_en (1'b1);

     // Enable FLL lock detect
     wdata = 32'h00009200;
     wdata[`MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_ENABLE]=1'b1;
     csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_CONTROL1, wdata);
     csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL1, wdata);
     csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_CONTROL1, wdata);

     // Enable lock detect interrupt
     wdata = '0;
     wdata[`MVP_PLL_CORE_STATUS_INT_EN__VCO0_FLL_LOCKED_INT_EN]=1'b1;
     wdata[`MVP_PLL_CORE_STATUS_INT_EN__VCO1_FLL_LOCKED_INT_EN]=1'b1;
     wdata[`MVP_PLL_CORE_STATUS_INT_EN__VCO2_FLL_LOCKED_INT_EN]=1'b1;
     csr_write(DDR_PLL_OFFSET,`MVP_PLL_CORE_STATUS_INT_EN, wdata);

     // wait to lock
     #26us
     //set_gfcm_en(1'b1);
     //set_pll0_div_clk_en(1'b1);
      set_vco0_pll_clk_en(1'b1);
      set_mcu_clk_sel(1'b1);
      wait_hclk (4);

      set_pll0_div_clk_rst(1'b0);
      set_gfcm_en(1'b1);
      set_pll0_div_clk_en(1'b1);
      sw_phy_clk_en (1'b1);

      // Setup TX PIs for 90 degree offset
      set_tx_dqs_sdr_rt_pi_cfg (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_tx_match_pi_cfg      (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(4'h1), .xcpl('0) );
      set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_tx_dq_sdr_rt_pi_cfg  (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_tx_dq_ddr_pi_cfg     (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_tx_dq_qdr_pi_cfg     (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_rx_rdqs_pi_cfg       (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));
      set_rx_ren_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h1));
      set_rx_rcs_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(4'h1), .xcpl('0), .code(6'h0));

      #100ns;

     `CSR_WRF1(DDR_FSW_OFFSET,DDR_FSW_CTRL_CFG, VCO_SEL_OVR, 1'b0);

     // Enable HW Status ACK (i.e. assert INIT_COMPLETE)
     `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_ACK_OVR, 1'b0);
     {ovr, req} = {1'b1, 1'b0};
     set_dfi_status_req(ovr, req);

     // SW PREP done
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b1);

     $display("Freqeuncy Switch 1 ...");
     // Simple SW override status request
     {ovr, req} = {1'b1, 1'b1};
     set_dfi_status_req(ovr, req);
     #100ns;
     do begin
        get_dfi_status_ack(ack);
        get_cmn_switch_done(switch_done);
     end while (!ack || !switch_done);
     {ovr, req} = {1'b1, 1'b0};
     set_dfi_status_req(ovr, req);
        #1us;
        config_vips(200, 1);

     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b0);
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b1);
     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b0);
     `CSR_WRF1(DDR_MCU_CSR_OFFSET, WAV_MCU_IRQ_FAST_CLR_CFG, CLR, 1'b1);
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b1);

     #100ns;
     $display("Freqeuncy Switch 2 ...");
     // Simple SW override status request
     {ovr, req} = {1'b1, 1'b1};
     set_dfi_status_req(ovr, req);
     #100ns;
     do begin
        get_dfi_status_ack(ack);
        get_cmn_switch_done(switch_done);
     end while (!ack || !switch_done);
     {ovr, req} = {1'b1, 1'b0};
     set_dfi_status_req(ovr, req);

     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b0);
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b1);
     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b0);
     `CSR_WRF1(DDR_MCU_CSR_OFFSET, WAV_MCU_IRQ_FAST_CLR_CFG, CLR, 1'b1);
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b1);

     #100ns;
     $display("Freqeuncy Switch 3 ...");
     // Simple SW override status request
     {ovr, req} = {1'b1, 1'b1};
     set_dfi_status_req(ovr, req);
     #100ns;
     do begin
        get_dfi_status_ack(ack);
        get_cmn_switch_done(switch_done);
     end while (!ack || !switch_done);
     {ovr, req} = {1'b1, 1'b0};
     set_dfi_status_req(ovr, req);

     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b0);
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b1);
     #100ns;
     `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b0);
     `CSR_WRF1(DDR_MCU_CSR_OFFSET, WAV_MCU_IRQ_FAST_CLR_CFG, CLR, 1'b1);

     $display("Freqeuncy Switch test completed!!!!!!!!");
     #100ns;
  end
  endtask

  task t_bscan_sanity;
     output int err;
     integer count;
  begin
     i_jtag_tck      = '0;
     i_jtag_trst_n   = '1;
     i_jtag_tms      = '0;
     i_jtag_tdi      = '0;
     err = 0;
     #1us;

     count = 0;
     i_jtag_tdi = 1'b0;

     #5us;
     i_jtag_tdi = 1'b1;

     do begin
        @(posedge i_jtag_tck);
        count=count+1;
     end while (o_jtag_tdo == '0);

     @(posedge i_jtag_tck);
     @(posedge i_jtag_tck);

     i_jtag_tdi = 1'b0;
     @(posedge i_jtag_tck);
     #2us;

     $display("BSCAN chain length = %d", count);
     $display("BSCAN completed!!!!!!!!");
     #100ns;
  end
  endtask

 //end
/*task loopback();
begin
if(lp_set==1)
begin
 $display("loopback begin completed!!!!!!!!");
t_ddr_sanity;
t_irdqs_sanity;
t_pll_sanity_closed;
t_pll_sanity_open;
t_mcu_sanity;
t_mcu_boot;
t_mcu_host;
t_dfi_status_sanity;
t_freq_sw_sanity;
t_bscan_sanity;
 $display("loopback all task completed!!!!!!!!");
end

else if(lp_set==2) begin

end
else if (lp_set==3) begin

end
end
endtask*/
