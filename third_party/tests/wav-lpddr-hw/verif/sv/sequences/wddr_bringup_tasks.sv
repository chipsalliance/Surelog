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

task pll_short;

    output int err;
    integer indx;
    logic zqcal_val;
    static integer max_pcal=63;
    static integer max_ncal=31;
    begin
        // ibias enable
        set_ibias_en(1'b1);
        #12ns;
        set_ldo_en(1'b1);
        #12ns;
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

        #1us;

        reset_pll_core;
        set_pll_init ( );
        // set bands for all VCOs
        set_band_vco_lp_value (.vco_freq_MHz(400));
        set_band_vco_hp_value (.vco_freq_MHz(vcoFreq1),.vco_sel(1));
        set_band_vco_hp_value (.vco_freq_MHz(vcoFreq2),.vco_sel(2));

        // enable feedback and set fbdiv for VCO1
        set_fbdiv_vco_value (.vco_freq_MHz(vcoFreq1),.vco_sel(1));
        config_vips(vcoFreq1,freqRatio);

        // enable all VCOs
        set_vcos_en (1'b1);
        // wait to lock (open loop= 200ns, closed loop=300us)
        wait_time_pll_lock();

        set_vco0_pll_clk_en(1'b1);
        set_mcu_clk_sel(1'b1);
        wait_hclk (4);

        set_pll0_div_clk_rst(1'b0);
        set_gfcm_en(1'b1);
        //  set_csp_cgc_sw_en(1'b1,1'b1);

        set_pll0_div_clk_en(1'b1);
        sw_phy_clk_en (1'b1);
    end
endtask

task pll_full;
    logic [31:0] wdata;
    begin

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
        set_band_vco_hp_value (.vco_freq_MHz(vcoFreq1),.vco_sel(1));
        set_band_vco_hp_value (.vco_freq_MHz(vcoFreq2),.vco_sel(2));

        // enable feedback and set fbdiv for VCO1
        set_fbdiv_vco_value (.vco_freq_MHz(vcoFreq1),.vco_sel(1));
        config_vips(vcoFreq1,freqRatio);

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
        set_vco0_pll_clk_en(1'b1);
        set_mcu_clk_sel(1'b1);
        wait_hclk (4);

        set_pll0_div_clk_rst(1'b0);
        set_gfcm_en(1'b1);
        set_pll0_div_clk_en(1'b1);
        sw_phy_clk_en (1'b1);

        #10ns;
    end
endtask

task config11;

        // Set lpde delay
        // 90p delay through DQ TX LPDE, 98ps Delay through DQS TX LPDE
        set_wrdq_lpde_dly  (.byte_sel(ALL),    .rank_sel(RANK_ALL), .dq(99),.gear(2'h0),  .r0_dly(8'h01), .r1_dly(8'h01));
        set_rdsdr_lpde_dly (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),         .gear(2'h0),        .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdsdr_lpde_dly (.byte_sel(CA),     .rank_sel(RANK_ALL),         .gear(2'h0),        .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdqs_dly       (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('h0),   .r0_cdly('h0), .r1_tdly('h0), .r1_cdly('h0));

        set_wrdqs_lpde_dly (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0),.gear(2'h0), .r0_dly(8'h18), .r1_dly(8'h18));
        set_wrdqs_lpde_dly (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1),.gear(2'h0), .r0_dly(8'h18), .r1_dly(8'h18));

    if(freqSw > 0)
    begin
        // -----------------
        // M1 Configurations
        // -----------------
        set_pi_cfg (.freq_MHz(vcoFreq2), .freq_ratio(1), .msr(1), .dqs_code('0), .dq_code('0), .ca_code('0));

        // Set lpde delay
        // 90p delay through DQ TX LPDE, 98ps Delay through DQS TX LPDE
        set_wrdq_lpde_dly_m1  (.byte_sel(ALL),    .rank_sel(RANK_ALL), .dq(99), .gear(2'h0), .r0_dly(8'h01), .r1_dly(8'h01));
        set_rdsdr_lpde_dly_m1 (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),  .gear(2'h0),  .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdsdr_lpde_dly_m1 (.byte_sel(CA),     .rank_sel(RANK_ALL),  .gear(2'h0),  .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdqs_dly_m1       (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('0),  .r0_cdly('h0), .r1_tdly('0), .r1_cdly('h0));

        set_wrdqs_lpde_dly_m1 (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(2'h0),.r0_dly(8'h18), .r1_dly(8'h18));
        set_wrdqs_lpde_dly_m1 (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1), .gear(2'h0),.r0_dly(8'h18), .r1_dly(8'h18));

        `ifdef LPK
            set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz('d1066), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
        `else
            set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz('d1066), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
        `endif

        set_dq_dqs_rcvr_cfg_m1   (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz('d1066), .dly_ps('d0));

        // dq or ca slices
        // DQ FC dly = 1 and CA = 0 for TDQSS = 1tck
        set_txdq_sdr_fc_dly_m1   (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        set_txdq_sdr_fc_dly_m1   (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdq_rt_pipe_en_m1   (.byte_sel(ALL),                  .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
        set_txdq_sdr_pipe_en_m1  (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_sdr_x_sel_m1    (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3200)); // SDR setting
        set_txdq_sdr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3210)); // DDR setting

        // control slices
        // DQ FC dly = 1 and CA = 0 for TDQSS = 1tck
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_rt_pipe_en_m1  (.byte_sel(ALL),                 .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
        set_txdqs_sdr_pipe_en_m1 (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(CA),     .dqs(8'd0),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));   //CK
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));   //DQS/Parity

        //All slices configured as DDR for 1:1 mode
        set_txdq_ddr_pipe_en_m1  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_ddr_x_sel_m1    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
        set_txdqs_ddr_pipe_en_m1 (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_ddr_x_sel_m1   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

        //set_phy_wrdly_cfg (.freq_MHz(vcoFreq2), .freq_ratio(1), .msr(1), .tdqss(1), .tdqs2dq(500), .dqdqs_fc_ovr('0) );

        //REN, OE, IE, RE
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd3), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));

        if(vcoFreq2 == 806) begin
            //REN, IE, RE, RCS
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        end else begin
            //REN, IE, RE, RCS
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        end

        //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
        set_dq_egress_mode_m1    (.byte_sel(ALL),    .dq (8'd99), .mode('h02));
        set_dqs_egress_mode_m1   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02));

        // DQ
        set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // select DQS
        set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_1TO1));
        set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));

        `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
        `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

        //DFI Configuration
        set_dfi_cfg (.freq_MHz(vcoFreq2), .freq_ratio(1), .msr(1), .wrgb_mode(DFIWGB_2TO2), .rdgb_mode(DFIRGB_2TO2));

    end

    set_pi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(1), .msr(0), .dqs_code('0), .dq_code('0), .ca_code('0));
    `ifdef LPK
        set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz('d1066), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
    `else
        set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz('d1066), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
    `endif

    set_dq_dqs_rcvr_cfg (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz('d1066), .dly_ps('d0));

    // dq or ca slices
    // DQ FC dly = 1 and CA = 0 for TDQSS = 1tck
    set_txdq_sdr_fc_dly   (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
    set_txdq_sdr_fc_dly   (.byte_sel(CA),     .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    set_txdq_rt_pipe_en   (.byte_sel(ALL),                 .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
    set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdq_sdr_x_sel    (.byte_sel(CA),     .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200)); // SDR setting
    set_txdq_sdr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210)); // DDR setting

    // control slices
    // DQ FC dly = 1 and CA = 0 for TDQSS = 1tck
    set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
    set_txdqs_sdr_fc_dly  (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    set_txdqs_rt_pipe_en  (.byte_sel(ALL),                 .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
    set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200));
    set_txdqs_sdr_x_sel   (.byte_sel(CA),     .dqs(8'd0),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));   //CK
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));   //DQS/Parity

    //All slices configured as DDR for 1:1 mode
    set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
    set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

    //set_phy_wrdly_cfg (.freq_MHz(vcoFreq1), .freq_ratio(1), .msr(0), .tdqss(1), .tdqs2dq(500), .dqdqs_fc_ovr('0));

    if ($test$plusargs("WRMIN_DELAY"))
    begin
        `uvm_info(get_type_name(), $sformatf("WRMIN_DELAY settings" ), UVM_LOW);
        // dqs
        set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h1111_1111));

        // dqs PI
        set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
        set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

        // dq
        set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h1111_1111));
    end

    if ($test$plusargs("WRMAX_DELAY"))
    begin
        `uvm_info(get_type_name(), $sformatf("WRMAX_DELAY settings" ), UVM_LOW);
        // dqs
        set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

        // dqs PI
        set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
        set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

        // dq
        set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    end

    if ($test$plusargs("RDMIN_DELAY"))
    begin
        `uvm_info(get_type_name(), $sformatf("RDMIN_DELAY settings" ), UVM_LOW);
        // dqs
        set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

        // dqs PI
        set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
        set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

        // dq
        set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    end

    if ($test$plusargs("RDMAX_DELAY"))
    begin
        `uvm_info(get_type_name(), $sformatf("RDMAX_DELAY settings" ), UVM_LOW);
        // dqs
        set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

        // dqs PI
        set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
        set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

        // dq
        set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    end

    //REN, OE, IE, RE
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd3), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .x_sel   ('h7654_3210));

    if(vcoFreq1 == 230) begin
    // tdqsck = 2.5ns need 1/2 tck shift
    set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .pipe_en ('h0000_0002));
    set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .pipe_en ('h0000_0002));
    //set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .pipe_en ('h0000_0002));
    //set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .pipe_en ('h0000_0002));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .x_sel   ('h7654_0001));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .x_sel   ('h7654_0001));
    //set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .x_sel   ('h7654_0001));
    //set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .x_sel   ('h7654_0000));
    end

    if(vcoFreq1 == 806) begin
        //Add 1 cycle delay for tdqsck = 1.5ns
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
    end
    else begin
        //REN, IE, RE, RCS
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    end

    //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
    set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h02));
    set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h02));

    // DQ
    set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // select DQS
    set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_1TO1));
    set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));

    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

    //DFI Configuration
    set_dfi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(1), .msr(0), .wrgb_mode(DFIWGB_2TO2), .rdgb_mode(DFIRGB_2TO2));

endtask

task config21;
    integer freq ;
    logic [1:0] gear0;
    logic [1:0] gear1;
    begin
         case(vcoFreq1)
             230    : gear0 = 2'h0 ;
             422    : gear0 = 2'h0 ;
             652    : gear0 = 2'h0 ;
             806    : gear0 = 2'h1 ;
             1075   : gear0 = 2'h1 ;
             1612   : gear0 = 2'h1 ;
             2112   : gear0 = 2'h2 ;
             3200   : gear0 = 2'h3 ;
             default: gear0 = 2'h0 ;
         endcase
         case(vcoFreq2)
             230    : gear1 = 2'h0 ;
             422    : gear1 = 2'h0 ;
             652    : gear1 = 2'h0 ;
             806    : gear1 = 2'h1 ;
             1075   : gear1 = 2'h1 ;
             1612   : gear1 = 2'h1 ;
             2112   : gear1 = 2'h2 ;
             3200   : gear1 = 2'h3 ;
             default: gear1 = 2'h0 ;
         endcase
        //`ifdef GLS
        set_wrdqs_lpde_dly    (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear0), .r0_dly(8'hF), .r1_dly(8'hF));
        //`else
        //set_wrdqs_lpde_dly    (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear0), .r0_dly(8'hF), .r1_dly(8'hA));
        //`endif
        set_wrdqs_lpde_dly    (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1), .gear(gear0), .r0_dly(8'hA), .r1_dly(8'hA));
        set_wrdq_lpde_dly    (.byte_sel(ALL),     .rank_sel(RANK_ALL), .dq(99),.gear(gear0),   .r0_dly(8'h01), .r1_dly(8'h01));
        set_rdsdr_lpde_dly    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),         .gear(gear0),   .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdsdr_lpde_dly    (.byte_sel(CA),     .rank_sel(RANK_ALL),         .gear(gear0),   .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdqs_dly          (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('h0),   .r0_cdly('h0), .r1_tdly('h0), .r1_cdly('h0));

        if(freqSw > 0)
        begin
            case(vcoFreq2)
                230    : freq = 230;
                422    : freq = 422;
                652    : freq = 652;
                806    : freq = 806;
                1075   : freq = 1075 ;
                1612   : freq = 1612 ;
                2112   : freq = 2112 ;
                default: freq = 2112 ;
            endcase
            $display ("INFO: CONFIG21 vco_freq2 = freq = %d ",freq);
            // -----------------
            // M1 Configurations
            // -----------------
            //`ifdef GLS
            set_wrdqs_lpde_dly_m1 (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear1), .r0_dly(8'hF), .r1_dly(8'hF));
            //`else
            //set_wrdqs_lpde_dly_m1 (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear1), .r0_dly(8'hF), .r1_dly(8'hA));
            //`endif
            set_wrdqs_lpde_dly_m1 (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1), .gear(gear1), .r0_dly(8'hA), .r1_dly(8'hA));
            set_wrdq_lpde_dly_m1 (.byte_sel(ALL),     .rank_sel(RANK_ALL), .dq(99),.gear(gear1),   .r0_dly(8'h01), .r1_dly(8'h01));
            set_rdsdr_lpde_dly_m1 (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),         .gear(gear1),   .r0_dly(8'h0F), .r1_dly(8'h0F));
            set_rdsdr_lpde_dly_m1 (.byte_sel(CA),     .rank_sel(RANK_ALL),         .gear(gear1),   .r0_dly(8'h0F), .r1_dly(8'h0F));
            set_rdqs_dly_m1       (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('0),  .r0_cdly('h0), .r1_tdly('0), .r1_cdly('h0));

            set_pi_cfg (.freq_MHz(freq), .freq_ratio(2), .msr(1), .dqs_code('0), .dq_code('0), .ca_code('0));
            `ifdef LPK
                if(freq >= 1066 )
                    set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
                else
                    set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;

            `else
                if(freq >= 1066 )
                    set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
                else
                    set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
            `endif

            set_dq_dqs_rcvr_cfg_m1 (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz(freq), .dly_ps('d0));

            // dq or ca slices
            set_txdq_sdr_fc_dly_m1   (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdq_rt_pipe_en_m1   (.byte_sel(ALL),                  .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
            set_txdq_sdr_pipe_en_m1  (.byte_sel(CA) ,    .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
            set_txdq_sdr_x_sel_m1    (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2020)); // SDR setting
            // Add 1tck delay for tdqss
            set_txdq_sdr_pipe_en_m1  (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_000C));
            set_txdq_sdr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_1302)); // DDR setting

            // control slices
            set_txdqs_sdr_fc_dly_m1  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_rt_pipe_en_m1  (.byte_sel(ALL),                 .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
            set_txdqs_sdr_pipe_en_m1 (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(CA),     .dqs(8'd0),  .rank_sel(RANK0),    .x_sel   ('h7654_3120));   //CK
            set_txdqs_sdr_x_sel_m1   (.byte_sel(CA),     .dqs(8'd0),  .rank_sel(RANK1),    .x_sel   ('h7654_3120));   //CK
            //Add 1 tck delay for tdqss
            set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_000C));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_0202));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK0),    .x_sel   ('h7654_1302)); //DQS/Parity
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0),    .x_sel   ('h7654_1302)); // OE
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0),    .x_sel   ('h7654_0202));

            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK1),    .x_sel   ('h7654_1302)); //DQS/Parity
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1),    .x_sel   ('h7654_1302)); // OE
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
            set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1),    .x_sel   ('h7654_0202));

            //All slices configured as
            set_txdq_ddr_pipe_en_m1  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
            set_txdq_ddr_x_sel_m1    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
            set_txdqs_ddr_pipe_en_m1 (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
            set_txdqs_ddr_x_sel_m1   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

            //set_phy_wrdly_cfg (.freq_MHz(freq), .freq_ratio(2), .msr(1), .tdqss(1), .tdqs2dq(500), .dqdqs_fc_ovr('0));

            // Remove 1 tck added for tdqss and Add 1 fc dly for 1.5ns tdqsck
            if(freq >= 2112) begin

                //REN, IE, RE, RCS
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .x_sel   ('h7654_2020));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .x_sel   ('h7654_2020));

                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

                `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);

                // Keep 1 tck added for tdqss on WR path to compensate for 1.5ns tdqsck on REN/IE/RE
            end else if(freq >= 1600) begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

                `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);

            end else if(freq >= 1075) begin
                // Remove 1 tck added for tdqss
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0), .pipe_en ('h0000_0000));

                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .pipe_en ('h0000_0000));

                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0), .x_sel   ('h7654_3120)); // OE
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0), .x_sel   ('h7654_2020));

                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1), .x_sel   ('h7654_3120)); // OE
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .x_sel   ('h7654_2020));

                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
                `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
            end else if(freq >= 800) begin

                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
                `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);

                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
                `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
                // Remove 1 tck added for tdqss
            end else begin
                //REN, IE, RE, RCS
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .pipe_en ('h0000_0000));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .x_sel   ('h7654_2020));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .pipe_en ('h0000_0000));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .x_sel   ('h7654_3120));
                set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .x_sel   ('h7654_2020));

                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
                set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
                `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);

                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

                `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
                `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h0);
            end

            //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
            set_dq_egress_mode_m1    (.byte_sel(ALL),    .dq (8'd99), .mode('h04));
            set_dqs_egress_mode_m1   (.byte_sel(ALL),    .dqs(8'd99), .mode('h04));

            // DQ
            set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
            set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_1TO1));
            set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_1TO1));

            //DFI Configuration
            set_dfi_cfg (.freq_MHz(freq), .freq_ratio(2), .msr(1), .wrgb_mode(DFIWGB_4TO4), .rdgb_mode(DFIRGB_4TO4));

        end

        case(vcoFreq1)
            230    : freq = 230;
            422    : freq = 422;
            652    : freq = 652;
            806    : freq = 806;
            1075   : freq = 1075 ;
            1612   : freq = 1612 ;
            2112   : freq = 2112 ;
            default: freq = 2112 ;
        endcase
        $display ("INFO: CONFIG21 vco_freq1 = freq = %d ",freq);
        set_pi_cfg (.freq_MHz(freq), .freq_ratio(2), .msr(0), .dqs_code('0), .dq_code('0), .ca_code('0));
        `ifdef LPK
            if(freq >= 1066 )
                set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
            else
                set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
        `else
            if(freq >= 1066 )
                set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
            else
                set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz(freq), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b0)) ;
        `endif

        set_dq_dqs_rcvr_cfg (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz(freq), .dly_ps('d0));

        // dq or ca slices
        set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdq_rt_pipe_en   (.byte_sel(ALL),                  .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
        set_txdq_sdr_pipe_en  (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_sdr_x_sel    (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2020)); // SDR setting
        // Add 1tck delay for tdqss
        set_txdq_sdr_pipe_en  (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_000C));
        set_txdq_sdr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_1302)); // DDR setting

        // control slices
        set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_rt_pipe_en  (.byte_sel(ALL),                 .rank_sel(RANK_ALL), .pipe_en ('h0000_01FF));
        set_txdqs_sdr_pipe_en (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_sdr_x_sel   (.byte_sel(CA),     .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
        set_txdqs_sdr_x_sel   (.byte_sel(CA),     .dqs(0),     .rank_sel(RANK0),    .x_sel   ('h7654_3120));// WCK
        set_txdqs_sdr_x_sel   (.byte_sel(CA),     .dqs(0),     .rank_sel(RANK1),    .x_sel   ('h7654_3120));// WCK
        //Add 1 tck delay for tdqss
        set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_000C));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_0202));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK0),    .x_sel   ('h7654_1302)); // RANK0 DQS/Parity
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0),    .x_sel   ('h7654_1302)); // RANK0 OE
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0),    .x_sel   ('h7654_0202));

        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK1),    .x_sel   ('h7654_1302)); //DQS/Parity
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1),    .x_sel   ('h7654_1302)); // OE
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1),    .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1),    .x_sel   ('h7654_0202));

        //All slices configured as DDR for 1:2 mode
        set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
        set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

        //set_phy_wrdly_cfg (.freq_MHz(vcoFreq1), .freq_ratio(2), .msr(0), .tdqss(1), .tdqs2dq(500), .dqdqs_fc_ovr('0));

        if ($test$plusargs("WRMIN_DELAY"))
        begin
            $display ("INFO: CONFIG21 WRMIN_DELAY");
            `uvm_info(get_type_name(), $sformatf("WRMIN_DELAY settings" ), UVM_LOW);
            // dqs
            set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h1111_1111));

            // dqs PI
            set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
            set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

            // dq
            set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        end

        if ($test$plusargs("WRMAX_DELAY"))
        begin
            $display ("INFO: CONFIG21 WRMAX_DELAY");
            `uvm_info(get_type_name(), $sformatf("WRMAX_DELAY settings" ), UVM_LOW);
            // dqs
            set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

            // dqs PI
            set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
            set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

            // dq
            set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        end

        if ($test$plusargs("RDMIN_DELAY"))
        begin
            $display ("INFO: CONFIG21 RDMIN_DELAY");
            `uvm_info(get_type_name(), $sformatf("RDMIN_DELAY settings" ), UVM_LOW);
            // dqs
            set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

            // dqs PI
            set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
            set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

            // dq
            set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        end

        if ($test$plusargs("RDMAX_DELAY"))
        begin
            $display ("INFO: CONFIG21 RDMAX_DELAY");
            `uvm_info(get_type_name(), $sformatf("RDMAX_DELAY settings" ), UVM_LOW);
            // dqs
            set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

            // dqs PI
            set_tx_dqs_ddr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));
            set_tx_dqs_qdr_pi_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(1'b1), .xcpl('0), .code(6'h0));

            // dq
            set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        end

        //set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .pipe_en ('h0000_0000));
        //set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .pipe_en ('h0000_0000));
        //set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .pipe_en ('h0000_0000));
        set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .pipe_en ('h0000_0000));
        //set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .x_sel   ('h7654_3120));
        //set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .x_sel   ('h7654_3120));
        //set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .x_sel   ('h7654_3120));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK1), .x_sel   ('h7654_2020));

        // Remove 1 tck added for tdqss and Add 1 fc dly for 1.5ns tdqsck
        if(freq >= 2112) begin
            $display ("INFO: CONFIG21 freq >= 2112");
            //REN, IE, RE, RCS
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .x_sel   ('h7654_2020));

            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .fc_dly  ('h0000_1111));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .fc_dly  ('h0000_1111));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .fc_dly  ('h0000_1111));
            // RCS same dely for both ranks.
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));
            // Add 2.5 cycle dly for 2.5ns tdqsck
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .fc_dly  ('h0000_2222));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .fc_dly  ('h0000_2222));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .fc_dly  ('h0000_2222));
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);

            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            // Keep 1 tck added for tdqss on WR path to compensate for 1.5ns tdqsck on REN/IE/RE
        end else if(freq >= 1600) begin

            $display ("INFO: CONFIG21 freq >= 1600");
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .fc_dly  ('h0000_0000));
            // RCS same dely for both ranks.
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            // Add 2.5 cycle dly for 2.5ns tdqsck
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .fc_dly  ('h0000_0000));

            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .pipe_en ('h0000_0002));
            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .pipe_en ('h0000_0002));
            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .pipe_en ('h0000_0002));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .x_sel   ('h0000_0001));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .x_sel   ('h0000_0001));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .x_sel   ('h0000_0001));

            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .pipe_en ('h0000_0002));
            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .pipe_en ('h0000_0002));
            set_txdqs_ddr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .pipe_en ('h0000_0002));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .x_sel   ('h0000_0001));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .x_sel   ('h0000_0001));
            set_txdqs_ddr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .x_sel   ('h0000_0001));

            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);

            `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
        // Remove 1 tck added for tdqss
         end else if(freq >= 1075) begin
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0), .pipe_en ('h0000_0000));

            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .pipe_en ('h0000_0000));

            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK0), .x_sel   ('h7654_3120)); // OE
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK0), .x_sel   ('h7654_2020));

            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK1), .x_sel   ('h7654_3120)); // OE
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5),  .rank_sel(RANK1), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8),  .rank_sel(RANK1), .x_sel   ('h7654_2020));

            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);

            `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
            `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
        // Remove 1 tck added for tdqss and Add 1 fc dly for 1.5ns tdqsck
        end else if(freq >= 800) begin
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
            `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);

            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
            `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
        end else begin
            //REN, IE, RE, RCS
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .pipe_en ('h0000_0000));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK0), .x_sel   ('h7654_3120));
            set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd8), .rank_sel(RANK0), .x_sel   ('h7654_2020));
            //REN, IE, RE, RCS
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
            set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd8), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));

            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
            `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);

            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'hBB, 'hBB);
            `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
            `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h0);
        end

        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd2), .rank_sel(RANK1), .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd4), .rank_sel(RANK1), .x_sel   ('h7654_1302));
        set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd5), .rank_sel(RANK1), .x_sel   ('h7654_1302));

        //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
        set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h04));
        set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h04));

        // DQ
        set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
        set_tx_gb             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_1TO1));
        set_tx_gb             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_1TO1));

        //DFI Configuration
        set_dfi_cfg (.freq_MHz(freq), .freq_ratio(2), .msr(0), .wrgb_mode(DFIWGB_4TO4), .rdgb_mode(DFIRGB_4TO4));
    end
endtask

task config41;
    logic [1:0] gear0;
    logic [1:0] gear1;
    begin
         case(vcoFreq1)
             230    : gear0 = 2'h0 ;
             422    : gear0 = 2'h0 ;
             652    : gear0 = 2'h0 ;
             806    : gear0 = 2'h1 ;
             1075   : gear0 = 2'h1 ;
             1612   : gear0 = 2'h1 ;
             2112   : gear0 = 2'h2 ;
             3200   : gear0 = 2'h3 ;
             default: gear0 = 2'h0 ;
         endcase
         case(vcoFreq2)
             230    : gear1 = 2'h0 ;
             422    : gear1 = 2'h0 ;
             652    : gear1 = 2'h0 ;
             806    : gear1 = 2'h1 ;
             1075   : gear1 = 2'h1 ;
             1612   : gear1 = 2'h1 ;
             2112   : gear1 = 2'h2 ;
             3200   : gear1 = 2'h3 ;
             default: gear1 = 2'h0 ;
         endcase
    set_wrdqs_lpde_dly    (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear0), .r0_dly(8'hA),  .r1_dly(8'hA));
    set_wrdqs_lpde_dly    (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1), .gear(gear0), .r0_dly(8'hA),  .r1_dly(8'hA));
    set_wrdq_lpde_dly     (.byte_sel(ALL),     .rank_sel(RANK_ALL), .dq(99), .gear(gear0), .r0_dly(8'h01), .r1_dly(8'h01));
    set_rdsdr_lpde_dly    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),           .gear(gear0), .r0_dly(8'h0F), .r1_dly(8'h0F));
    set_rdsdr_lpde_dly    (.byte_sel(CA),     .rank_sel(RANK_ALL),           .gear(gear0), .r0_dly(8'h0F), .r1_dly(8'h0F));
    set_rdqs_dly          (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('h0),   .r0_cdly('h0), .r1_tdly('h0), .r1_cdly('h0));

    if(freqSw > 0)
    begin
        // -----------------
        // M1 Configurations
        // -----------------
        set_wrdqs_lpde_dly_m1 (.byte_sel(CA),      .rank_sel(RANK_ALL), .dqs(0), .gear(gear1), .r0_dly(8'hA) , .r1_dly(8'hA));
        set_wrdqs_lpde_dly_m1 (.byte_sel(DQ_ALL),  .rank_sel(RANK_ALL), .dqs(1), .gear(gear1), .r0_dly(8'hA) , .r1_dly(8'hA));
        set_wrdq_lpde_dly_m1  (.byte_sel(ALL),     .rank_sel(RANK_ALL), .dq(99), .gear(gear1), .r0_dly(8'h01), .r1_dly(8'h01));
        set_rdsdr_lpde_dly_m1 (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL),           .gear(gear1), .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdsdr_lpde_dly_m1 (.byte_sel(CA),     .rank_sel(RANK_ALL),           .gear(gear1), .r0_dly(8'h0F), .r1_dly(8'h0F));
        set_rdqs_dly_m1       (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .r0_tdly('0),  .r0_cdly('h0), .r1_tdly('0), .r1_cdly('h0));
        set_pi_cfg (.freq_MHz(vcoFreq2), .freq_ratio(4), .msr(1), .dqs_code('0), .dq_code('0), .ca_code('0));
        `ifdef LPK
            set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz('d2133), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
        `else
            set_dq_dqs_drvr_cfg_m1 (.byte_sel(DQ_ALL), .dqs_freq_MHz('d2133), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
        `endif

        set_dq_dqs_rcvr_cfg_m1 (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz('d2133), .dly_ps('d0));

        // dq or ca slices
        set_txdq_sdr_fc_dly_m1   (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdq_sdr_pipe_en_m1  (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_sdr_x_sel_m1    (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2020)); // SDR setting
        set_txdq_sdr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120)); // DDR setting

        // control slices
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
        set_txdqs_sdr_pipe_en_m1 (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(CA),     .dqs(8'd0),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));   //CK
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));   //DQS/Parity

        //REN, OE, IE, RE
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd3), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
        set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK0),    .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK0),    .fc_dly  ('h0000_1111));
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK1),    .fc_dly  ('h0000_2222));

        // Read Enable
        set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));

        //All slices configured as
        set_txdq_ddr_pipe_en_m1  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdq_ddr_x_sel_m1    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
        set_txdqs_ddr_pipe_en_m1 (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
        set_txdqs_ddr_x_sel_m1   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

        //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
        set_dq_egress_mode_m1    (.byte_sel(ALL),    .dq (8'd99), .mode('h04));
        set_dqs_egress_mode_m1   (.byte_sel(ALL),    .dqs(8'd99), .mode('h04));

        // DQ
        //FREQ RATIO 1:4, DP_Freq : 0.8
        set_rx_gb_m1             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO8),    .wck_mode(1'b1)); // select DQS
        set_rx_gb_m1             (.byte_sel(CA),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO8),    .wck_mode(1'b1)); // select DQS, Loop Back
        set_tx_gb_m1             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_8TO4));
        set_tx_gb_m1             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_8TO4));

        // FREQ RATIO 1:4, DP_Freq : 0.8
        set_dfiwrd_wdp_cfg_m1     (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
        set_dfiwrcctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
        set_dfickctrl_wdp_cfg_m1  (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b1));
        set_dfiwctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b0));
        set_dfiwenctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(8'h3), .pre_gb_pipe_en(1'b0));
        set_dfirctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b0));
        set_dfi_rdgb_mode_m1      (DFIRGB_8TO8);

        `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
        `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);

        `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
        `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
        `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG, PRE_FILTER_SEL, 'h1);
        //DFI Configuration
        //set_dfi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(4), .msr(1), .wrgb_mode(DFIWGB_8TO8), .rdgb_mode(DFIRGB_8TO8));
        set_dfi_paden_pext_cfg_m1 (.wrd_en_cycles(4'h4), .wrd_oe_cycles(8'd40), .wck_oe_cycles(4'h5), .ie_cycles(4'h3),  .re_cycles(4'h4), .ren_cycles(4'h2), .rcs_cycles(0));
        set_dfi_clken_pext_cfg_m1 (.wr_clken_cycles(4'h4), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h6));
    end

    set_pi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(4), .msr(0), .dqs_code('0), .dq_code('0), .ca_code('0));
    `ifdef LPK
        set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz('d806), .lb_mode(1'b1), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
    `else
        set_dq_dqs_drvr_cfg (.byte_sel(DQ_ALL), .dqs_freq_MHz('d806), .lb_mode(1'b0), .wck_mode(1'b0),.se_mode(1'b0), .termination(1'b1)) ;
    `endif

    set_dq_dqs_rcvr_cfg (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .dqs_freq_MHz('d806), .dly_ps('d0));

    // dq or ca slices
    set_txdq_sdr_fc_dly   (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    set_txdq_sdr_pipe_en  (.byte_sel(ALL),    .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdq_sdr_x_sel    (.byte_sel(CA),     .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2020)); // SDR setting
    set_txdq_sdr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3120)); // DDR setting

    // control slices
    set_txdqs_sdr_fc_dly  (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .fc_dly  ('h0000_0000));
    set_txdqs_sdr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
    set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(0),     .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));// WCK
    set_txdqs_sdr_x_sel   (.byte_sel(ALL),    .dqs(1),     .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));// DQS/Parity

    //REN, OE, IE, RE
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd3), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
    set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK_ALL), .x_sel   ('h7654_3120));
    set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd4), .rank_sel(RANK0),    .fc_dly  ('h0000_1111));
    set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd5), .rank_sel(RANK0),    .fc_dly  ('h0000_1111));
    set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK1),    .fc_dly  ('h0000_2222));

    // Read Enable
    set_txdqs_sdr_fc_dly  (.byte_sel(DQ_ALL),  .dqs(8'd2), .rank_sel(RANK_ALL), .fc_dly  ('h0000_1111));

    //All slices configured as DDR for 1:2 mode
    set_txdq_ddr_pipe_en  (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdq_ddr_x_sel    (.byte_sel(ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));
    set_txdqs_ddr_pipe_en (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0000));
    set_txdqs_ddr_x_sel   (.byte_sel(ALL),    .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3210));

    //EGRESS_MODE 5:0 DEF=0x01 "Egress mode (one-hot) - 0: BYPASS, 1:DDR_2to1, 2:QDR_2to1, 3: ODR_2to1, 4:QDR_4to1, 5:ODR_4to1";
    set_dq_egress_mode    (.byte_sel(ALL),    .dq (8'd99), .mode('h04));
    set_dqs_egress_mode   (.byte_sel(ALL),    .dqs(8'd99), .mode('h04));

    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);

    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, 'h4F, 'h4F);
    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG, PRE_FILTER_SEL, 'h1);
    // DQ
    //FREQ RATIO 1:4, DP_Freq : 0.8
    set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO8),    .wck_mode(1'b1)); // select DQS
    set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO8),    .wck_mode(1'b1)); // select DQS, Loop Back
    set_tx_gb             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_8TO4));
    set_tx_gb             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_8TO4));

    // FREQ RATIO 1:4, DP_Freq : 0.8
    set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
    set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
    set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b1));
    set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b0));
    set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(8'h3), .pre_gb_pipe_en(1'b0));
    set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_8TO8), .gb_pipe_dly(2'h1), .pre_gb_pipe_en(1'b0));
    set_dfi_rdgb_mode      (DFIRGB_8TO8);

    //DFI Configuration
    // set_dfi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(4), .msr(0), .wrgb_mode(DFIWGB_8TO8), .rdgb_mode(DFIRGB_8TO8));
    set_dfi_paden_pext_cfg (.wrd_en_cycles(4'h4), .wrd_oe_cycles(8'd40), .wck_oe_cycles(4'h5), .ie_cycles(4'h3),       .re_cycles(4'h4), .ren_cycles(4'h2),.rcs_cycles(4'h0));
    set_dfi_clken_pext_cfg (.wr_clken_cycles(4'h4), .rd_clken_cycles(4'hF), .ca_clken_cycles(4'h6));
    end
endtask

task config_end;
   `ifdef GLS
    set_dfi_traffic_ovr_cfg    (.sw_mode(1'b1), .sw_en(1'b1));
    set_dfi_traffic_ovr_cfg_m1 (.sw_mode(1'b1), .sw_en(1'b1));
    dfi_buf_flush_dp();
   `endif

    sw_csp_byte_sync(); // Dont call for sw_freq

    // Reset FIFO pointers due to Xs on the clocks
    set_fifo_clr;
    set_dfi_wdata_clr;
    set_dfi_rdata_clr;
    #100ns;

    set_dfi_status_ack(1'b1, 1'b0);
    #100ns;
    set_dfi_status_req(1'b0, 1'b0);

endtask

task set_pi_cfg;
    input real freq_MHz;
    input integer msr ;
    input integer freq_ratio ;
    input logic [5:0] dqs_code;
    input logic [5:0] dq_code;
    input logic [5:0] ca_code;
    logic [3:0] gear;
    logic [5:0] code = '0 ;
    logic [5:0] dqs_code_int     = '0 ;
    logic [5:0] dq_code_int      = '0 ;
    logic [5:0] ca_code_int      = '0 ;
    logic [5:0] qdr_dqs_code_int = '0 ;
    logic [5:0] qdr_dq_code_int  = '0 ;
    logic [5:0] qdr_ca_code_int  = '0 ;
    logic [5:0] ddr_dqs_code_int = '0 ;
    logic [5:0] ddr_dq_code_int  = '0 ;
    logic [5:0] ddr_ca_code_int  = '0 ;
    logic [5:0] ren_code         = '0 ;
    begin
        case(freq_MHz)
            230    : begin gear = 4'h0; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h8; end
            422    : begin gear = 4'h0; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h8; end
            652    : begin gear = 4'h1; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h2; end
            806    : begin gear = 4'h1; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h2; end
            1075   : begin gear = 4'h3; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
            1344   : begin gear = 4'h4; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
            1612   : begin gear = 4'h6; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'd12; end
            1862   : begin gear = 4'h8; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
            2112   : begin gear = 4'hA; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'd14; end
            2700   : begin gear = 4'hE; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
            3200   : begin gear = 4'hF; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
            default: begin gear = 4'h0; dqs_code_int = dqs_code ;  dq_code_int = dq_code ;  ca_code_int = ca_code ; ren_code = 6'h0; end
        endcase

        qdr_dqs_code_int = (freq_ratio > 1) ? ((freq_MHz == 1612) ? 6'd13 : dqs_code_int) : '0 ;
        qdr_dq_code_int  = (freq_ratio > 1) ? ((freq_MHz == 1612) ? 6'd13 : dq_code_int ) : '0 ;
        qdr_ca_code_int  = (freq_ratio > 1) ? ((freq_MHz == 1612) ? 6'd13 : ca_code_int ) : '0 ;

        ddr_dqs_code_int = (freq_ratio == 1) ? dqs_code_int : '0  ;
        ddr_dq_code_int  = (freq_ratio == 1) ? dq_code_int  : '0  ;
        ddr_ca_code_int  = (freq_ratio == 1) ? ca_code_int  : '0  ;

        case(msr)
            0 : begin
                //release ddr_phy_1x16_tb.u_phy_1x16.u_phy.u_ctrl_plane.i_pll_clk ;
                // Setup TX PIs for 90 degree offset
                set_tx_match_pi_cfg      (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0) );
                set_tx_dqs_sdr_rt_pi_cfg (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_tx_dqs_ddr_pi_cfg    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_dqs_code_int));
                set_tx_dqs_qdr_pi_cfg    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_dqs_code_int));
                set_tx_dqs_ddr_pi_cfg    (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_ca_code_int));
                set_tx_dqs_qdr_pi_cfg    (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_ca_code_int));
                set_tx_dq_sdr_rt_pi_cfg  (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_tx_dq_ddr_pi_cfg     (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_dq_code_int));
                set_tx_dq_qdr_pi_cfg     (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_dq_code_int));
                set_tx_dq_ddr_pi_cfg     (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_ca_code_int));
                set_tx_dq_qdr_pi_cfg     (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_ca_code_int));
                set_rx_rdqs_pi_cfg       (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_rx_ren_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK0),                   .en(1'b1), .gear(gear), .xcpl('0), .code(ren_code));
                set_rx_ren_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK1),                   .en(1'b1), .gear(gear), .xcpl('0), .code((ren_code+1'd1)));
                set_rx_rcs_pi_cfg        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
            end
            1 : begin
                set_tx_match_pi_cfg_m1      (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0) );
                set_tx_dqs_sdr_rt_pi_cfg_m1 (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_tx_dqs_ddr_pi_cfg_m1    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_dqs_code_int));
                set_tx_dqs_qdr_pi_cfg_m1    (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_dqs_code_int));
                set_tx_dqs_ddr_pi_cfg_m1    (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_ca_code_int));
                set_tx_dqs_qdr_pi_cfg_m1    (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_ca_code_int));
                set_tx_dq_sdr_rt_pi_cfg_m1  (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_tx_dq_ddr_pi_cfg_m1     (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_dq_code_int));
                set_tx_dq_qdr_pi_cfg_m1     (.byte_sel(DQ_ALL), .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_dq_code_int));
                set_tx_dq_ddr_pi_cfg_m1     (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(ddr_ca_code_int));
                set_tx_dq_qdr_pi_cfg_m1     (.byte_sel(CA),     .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(qdr_ca_code_int));
                set_rx_rdqs_pi_cfg_m1       (.byte_sel(ALL),    .rank_sel(RANK_ALL), .pi_sel(1'b0), .en(1'b1), .gear(gear), .xcpl('0), .code(code));
                set_rx_ren_pi_cfg_m1        (.byte_sel(ALL),    .rank_sel(RANK0),                   .en(1'b1), .gear(gear), .xcpl('0), .code(ren_code));
                set_rx_ren_pi_cfg_m1        (.byte_sel(ALL),    .rank_sel(RANK1),                   .en(1'b1), .gear(gear), .xcpl('0), .code((ren_code+1'd1)));
                set_rx_rcs_pi_cfg_m1        (.byte_sel(ALL),    .rank_sel(RANK_ALL),                .en(1'b1), .gear(gear), .xcpl('0), .code(code));
            end
        endcase
    end
endtask

task set_phy_wrdly_cfg ;
    input integer freq_MHz;
    input [1:0] freq_ratio ;
    input integer msr ;
    input real tdqss ;
    input integer tdqs2dq ;
    input logic [3:0] dqdqs_fc_ovr ;

    logic [31:0] dq_pi_dly ;
    logic [31:0] dqs_pi_dly ;
    logic [31:0] ca_pi_dly ;
    logic [5:0]  dq_pi_code ;
    logic [5:0]  dqs_pi_code ;
    logic [5:0]  ca_pi_code ;
    logic [3:0]  dqs_qc  ;
    logic [3:0]  dq_qc  ;
    logic [3:0]  ca_qc  ;
    logic [3:0]  sdr_fc  ;
    logic [1:0]  sdr_hc  ;
    logic [1:0]  ddr_hc  ;
    logic [31:0] fc_dly ;

    begin
        //        dqs_qc    = '0 ;
        //        dq_qc     = '0 ;
        //        ca_qc     = '0 ;
        //        sdr_fc    = '0 ;
        //        sdr_hc    = '0 ;
        //        ddr_hc    = '0 ;
        //        fc_dly    = '0 ;
        //        dq_pi_dly = '0 ;
        //        dqs_pi_dly = '0 ;
        //        ca_pi_dly = '0 ;
        //
        //        case(tdqss)
        //           1       : dqs_qc    = 4'h4 ; dq_qc    = 4'h4 ;
        //           0.75    : ca_qc     = 4'h1 ; dqs_qc   = 4'h4 ; dq_qc    = 4'h4 ;
        //           1.25    : dqs_qc    = 4'h5 ; dq_qc    = 4'h5 ;
        //           default : dqs_qc    = 4'h4 ; dq_qc    = 4'h4 ;
        //        endcase
        //
        //        if ((tdqs2dq/(1000000/freq_MHz) < 0.25 ) begin
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 0.5) begin
        //           dq_qc     =  dq_qc + 4'h1;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 0.25 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 0.75 ) begin
        //           dq_qc     =  dq_qc + 4'h2;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 0.5 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 1 ) begin
        //           dq_qc     =  dq_qc + 4'h3;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 0.75 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 1.25 ) begin
        //           dq_qc     =  dq_qc + 4'h4;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 1 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 1.5 ) begin
        //           dq_qc     =  dq_qc + 4'h5;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 1.25 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 1.75 ) begin
        //           dq_qc     =  dq_qc + 4'h6;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 1.5 ;
        //        end else if((tdqs2dq/(1000000/freq_MHz) < 2 ) begin
        //           dq_qc     =  dq_qc + 4'h7;
        //           dq_pi_dly =  (tdqs2dq/(1000000/freq_MHz) - 1.75 ;
        //        end
        //
        //        case({freq_ratio, dqs_qc} )
        //            {2'h1,4'h4}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; dqs_pi_dly = '0 ;                       end
        //            {2'h1,4'h5}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; dqs_pi_dly = (1000000/freq_MHz)*(1/4) ; end
        //            {2'h2,4'h4}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h0 ; dqs_pi_dly = '0 ;       end
        //            {2'h2,4'h5}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h0 ; dqs_pi_dly = (1000000/freq_MHz)*(1/4) ; end
        //            default        : begin  sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h0 ; dqs_pi_dly = 0 ;       end
        //        endcase
        //
        //        fc_dly = {{4{4'h0}},{4{dqdqs_fc_ovr + sdr_fc}}} ;
        //        $dispaly ("INFO: FC DLY for DQS WR path : %x SDR HC DLY for WR path : %x DDR HC DLY for WR path : %x", fc_dly, sdr_hc, ddr_hc ) ;
        //
        //        case (msr)
        //          0: begin
        //             set_txdqs_sdr_fc_dly     (.byte_sel(DQ_ALL),    .dqs(8'd0),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCK
        //             set_txdqs_sdr_fc_dly     (.byte_sel(DQ_ALL),    .dqs(8'd1),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //DQS
        //             set_txdqs_sdr_fc_dly     (.byte_sel(DQ_ALL),    .dqs(8'd3),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //OE
        //             set_txdqs_sdr_fc_dly     (.byte_sel(DQ_ALL),    .dqs(8'd6),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCK_OE
        //             set_txdqs_sdr_fc_dly     (.byte_sel(DQ_ALL),    .dqs(8'd7),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCS
        //             if (sdr_hc == 2'h1)
        //                if (freq_ratio == 2'h1) begin
        //                  set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200));
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3201));   //DQS/Parity
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3201));   //OE
        //                  // FIXME: extend WCS by 1/2 clock phase as it cannot be shifted by HC.
        //                end else if (freq_ratio == 2'h2) begin
        //                  set_txdqs_sdr_pipe_en (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_000F));
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031));   //DQS/Parity
        //                  set_txdqs_sdr_x_sel   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031));   //OE
        //                  // FIXME: extend WCS by 1/2 clock phase as it cannot be shifted by HC.
        //                end
        //             end
        //          end
        //          1: begin
        //             set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),    .dqs(8'd0),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCK
        //             set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),    .dqs(8'd1),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //DQS
        //             set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),    .dqs(8'd3),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //OE
        //             set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),    .dqs(8'd6),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCK_OE
        //             set_txdqs_sdr_fc_dly_m1  (.byte_sel(DQ_ALL),    .dqs(8'd7),  .rank_sel(RANK_ALL), .fc_dly(fc_dly)); //WCS
        //             if (sdr_hc == 2'h1)
        //                if (freq_ratio == 2'h1) begin
        //                  set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3200));
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3201));   //DQS/Parity
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK_ALL), .x_sel   ('h7654_3201));   //OE
        //                  // FIXME: extend WCS by 1/2 clock phase as it cannot be shifted by HC.
        //                end else if (freq_ratio == 2'h2) begin
        //                  set_txdqs_sdr_pipe_en_m1 (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_000F));
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_2020));
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd1),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031));   //DQS/Parity
        //                  set_txdqs_sdr_x_sel_m1   (.byte_sel(DQ_ALL), .dqs(8'd3),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031));   //OE
        //                  // FIXME: extend WCS by 1/2 clock phase as it cannot be shifted by HC.
        //                end
        //             end
        //          end
        //        endcase
        //
        //        case({freq_ratio, dq_qc} )
        //            {2'h1,4'h4}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            {2'h1,4'h5}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h1,4'h6}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h1 ; dq_pi_dly = '0 ;               end
        //            {2'h1,4'h7}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h1 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h1,4'h8}    : begin sdr_fc = 4'h2 ; sdr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            {2'h1,4'h9}    : begin sdr_fc = 4'h2 ; sdr_hc = 2'h0 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h1,4'hA}    : begin sdr_fc = 4'h2 ; sdr_hc = 2'h1 ; dq_pi_dly = '0 ;               end
        //            {2'h1,4'hB}    : begin sdr_fc = 4'h2 ; sdr_hc = 2'h1 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h1,4'hC}    : begin sdr_fc = 4'h3 ; sdr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            {2'h2,4'h4}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            {2'h2,4'h5}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h0 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h2,4'h6}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h1 ; dq_pi_dly = '0 ;               end
        //            {2'h2,4'h7}    : begin sdr_fc = 4'h0 ; sdr_hc = 2'h1 ; ddr_hc = 2'h1 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h2,4'h8}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            {2'h2,4'h9}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h0 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h2,4'hA}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h1 ; dq_pi_dly = '0 ;               end
        //            {2'h2,4'hB}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h1 ; dq_pi_dly = dq_pi_dly + 0.25 ; end
        //            {2'h2,4'hC}    : begin sdr_fc = 4'h1 ; sdr_hc = 2'h1 ; ddr_hc = 2'h0 ; dq_pi_dly = '0 ;               end
        //            default        : sdr_fc = 4'h1 ; sdr_hc = 2'h0 ; ddr_hc = 2'h0 ;
        //        endcase
        //
        //        fc_dly = {{4{4'h0}},{4{dqdqs_fc_ovr + sdr_fc}}} ;
        //        $dispaly ("INFO: FC DLY for DQ WR path : %x SDR HC DLY for WR path : %x DDR HC DLY for WR path : %x", fc_dly, sdr_hc, ddr_hc ) ;
        //
        //        case (msr)
        //          0: begin
        //             set_txdq_sdr_fc_dly      (.byte_sel(DQ_ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly(fc_dly));
        //             if (sdr_hc == 2'h1) begin
        //                if (freq_ratio == 2'h1) begin
        //                   set_txdq_sdr_pipe_en  (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                   set_txdq_sdr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3201)); // DDR setting
        //                end else if (freq_ratio == 2'h2) begin
        //                   set_txdq_sdr_pipe_en  (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_000F));
        //                   set_txdq_sdr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031)); // DDR setting
        //                end
        //             end
        //             if (ddr_hc == 2'h1)
        //                if (freq_ratio == 2'h2) begin
        //                   set_txdq_ddr_pipe_en  (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                   set_txdq_ddr_x_sel    (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3201));
        //                end
        //             end
        //          end
        //          1: begin
        //             set_txdq_sdr_fc_dly_m1   (.byte_sel(DQ_ALL),    .dq (8'd99), .rank_sel(RANK_ALL), .fc_dly(fc_dly));
        //             if (sdr_hc == 2'h1) begin
        //                if (freq_ratio == 2'h1) begin
        //                   set_txdq_sdr_pipe_en_m1  (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                   set_txdq_sdr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h7654_3201)); // DDR setting
        //                end else if (freq_ratio == 2'h2) begin
        //                   set_txdq_sdr_pipe_en_m1  (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .pipe_en ('h0000_000F));
        //                   set_txdq_sdr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99),  .rank_sel(RANK_ALL), .x_sel   ('h7654_2031)); // DDR setting
        //                end
        //             end
        //             if (ddr_hc == 2'h1)
        //                if (freq_ratio == 2'h2) begin
        //                   set_txdq_ddr_pipe_en_m1  (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .pipe_en ('h0000_0003));
        //                   set_txdq_ddr_x_sel_m1    (.byte_sel(DQ_ALL), .dq (8'd99), .rank_sel(RANK_ALL), .x_sel   ('h0000_3201));
        //                end
        //             end
        //          end
        //        endcase
        //
        //        ca_pi_dly   = ca_qc*0.25 ;
        //        dq_pi_code  = $ceil(dq_pi_dly*64) ;
        //        dqs_pi_code = $ceil(dqs_pi_dly*64) ;
        //        ca_pi_code  = $ceil(ca_pi_dly*64) ;
        //        $dispaly ("INFO: PI CODE for WR path : dq_pi_code = %x, dqs_pi_code = %x, ca_pi_code = %x", dq_pi_code,dqs_pi_code,ca_pi_code) ;
        //        set_pi_cfg (.freq_MHz(freq_MHz), .freq_ratio(freq_ratio), .msr(msr), .dqs_code(dqs_pi_code), .dq_code(dq_pi_code), .ca_code(ca_pi_code));
        //
    end
endtask

task set_dfi_cfg;
    input integer freq_MHz;
    input integer freq_ratio ;
    input integer msr ;
    input dwgb_t wrgb_mode ;
    input drgb_t rdgb_mode ;
    logic       wrd_pre_gb_pipe_en = '0 ;
    logic [1:0] wrd_gb_pipe_dly  = '0 ;
    logic [7:0] ckctrl_gb_pipe_dly ;
    logic [7:0] wctrl_gb_pipe_dly ;
    logic [7:0] wenctrl_gb_pipe_dly ;
    logic [7:0] rctrl_gb_pipe_dly ;
    logic       pre_gb_pipe_en;
    logic [7:0] wrd_en, wrd_oe, wck_oe, ie, re, ren, rcs;
    logic [7:0] wr_clken, rd_clken, ca_clken ;
    begin
        case(freq_ratio)
            1: begin
                case(freq_MHz)
                    230    : begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h0; wenctrl_gb_pipe_dly = 8'h0; rctrl_gb_pipe_dly = 8'h0; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h0 ; re = 4'h1 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h0 ; rd_clken = 4'h0 ; ca_clken = 4'h3 ; end
                    422    : begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h3; wenctrl_gb_pipe_dly = 8'h3; rctrl_gb_pipe_dly = 8'h3; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h1 ; re = 4'h2 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
                    //533    : begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h3; wenctrl_gb_pipe_dly = 8'h3; rctrl_gb_pipe_dly = 8'h3; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h1 ; re = 4'h2 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
                    652    : begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h3; wenctrl_gb_pipe_dly = 8'h3; rctrl_gb_pipe_dly = 8'h3; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h1 ; re = 4'h2 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
                    806    : begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h3; wenctrl_gb_pipe_dly = 8'h3; rctrl_gb_pipe_dly = 8'h3; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h0 ; re = 4'h1 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
                    default: begin ckctrl_gb_pipe_dly = 8'h3; wctrl_gb_pipe_dly = 8'h3; wenctrl_gb_pipe_dly = 8'h3; rctrl_gb_pipe_dly = 8'h3; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h0 ; re = 4'h1 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
                endcase
            end
            2: begin
                case(freq_MHz)
                    230    : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h0; wenctrl_gb_pipe_dly = 8'h0; rctrl_gb_pipe_dly = 8'h0; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h0 ; re = 4'h1 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'h0 ; rd_clken = 4'h0 ; ca_clken = 4'h6 ; end
                    422    : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h2; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h1 ; re = 4'h2 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    652    : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h2; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h1 ; re = 4'h2 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    806    : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h2; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 4'h5 ; wck_oe = 4'h5 ; ie = 4'h0 ; re = 4'h1 ; ren = 4'h0 ; rcs = 6'h0; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    1075   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h5; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd30+3'd5 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    //1344   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h5; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd30 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    //1612   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd38 ; wck_oe = 4'h5 ; ie = 4'h2 ; re = 4'h3 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    1612   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd38 ; wck_oe = 4'h5 ; ie = 4'h2 ; re = 4'h3 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; wrd_gb_pipe_dly = 2'h3; wrd_pre_gb_pipe_en = 1'b1; end
                    //1862   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd38 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    2112   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd40 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; wrd_gb_pipe_dly = 2'h3; wrd_pre_gb_pipe_en = 1'b1; end
                    //2112   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd40 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; wrd_gb_pipe_dly = 2'h0; wrd_pre_gb_pipe_en = 1'b0; end
                    2700   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd40 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    3200   : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd40 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                    default: begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h5; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd30 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; rcs = 6'h16 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
                endcase
            end
            //      4 :begin
            //          case(freq_MHz)
            //               2112  : begin ckctrl_gb_pipe_dly = 8'h2; wctrl_gb_pipe_dly = 8'h2; wenctrl_gb_pipe_dly = 8'h6; rctrl_gb_pipe_dly = 8'h2; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'd40 ; wck_oe = 4'h5 ; ie = 4'h3 ; re = 4'h4 ; ren = 4'h2 ; wr_clken = 4'hF ; rd_clken = 4'hF ; ca_clken = 4'h6 ; end
            //               default: begin ckctrl_gb_pipe_dly = 8'h0; wctrl_gb_pipe_dly = 8'h0; wenctrl_gb_pipe_dly = 8'h0; rctrl_gb_pipe_dly = 8'h0; pre_gb_pipe_en = 1'b0 ; wrd_en = 4'h4 ; wrd_oe = 8'h5  ; wck_oe = 4'h5 ; ie = 4'h2 ; re = 4'h3 ; ren = 4'h0 ; wr_clken = 4'h6 ; rd_clken = 4'hF ; ca_clken = 4'h3 ; end
            //            endcase
            //         end
        endcase
        case(msr)
            0 : begin
                set_dfiwrd_wdp_cfg     (.gb_mode(wrgb_mode), .gb_pipe_dly(wrd_gb_pipe_dly),     .pre_gb_pipe_en(wrd_pre_gb_pipe_en));
                set_dfiwrcctrl_wdp_cfg (.gb_mode(wrgb_mode), .gb_pipe_dly(2'h0),                .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfickctrl_wdp_cfg  (.gb_mode(wrgb_mode), .gb_pipe_dly(ckctrl_gb_pipe_dly),  .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfiwctrl_wdp_cfg   (.gb_mode(wrgb_mode), .gb_pipe_dly(wctrl_gb_pipe_dly),   .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfiwenctrl_wdp_cfg (.gb_mode(wrgb_mode), .gb_pipe_dly(wenctrl_gb_pipe_dly), .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfirctrl_wdp_cfg   (.gb_mode(wrgb_mode), .gb_pipe_dly(rctrl_gb_pipe_dly),   .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfi_rdgb_mode      (rdgb_mode);

                `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_WRC_M0_CFG    ,POST_GB_FC_DLY, PIPE_EN, 2'h0, 1'b0 );

                set_dfi_paden_pext_cfg (.wrd_en_cycles(wrd_en), .wrd_oe_cycles(wrd_oe), .wck_oe_cycles(wck_oe), .ie_cycles(ie), .re_cycles(re), .ren_cycles(ren), .rcs_cycles(rcs));
                set_dfi_clken_pext_cfg (.wr_clken_cycles(wr_clken), .rd_clken_cycles(rd_clken), .ca_clken_cycles(ca_clken));
                case(freq_MHz)
                    230: begin
                        set_dfi_traffic_ovr_cfg    (.sw_mode(1'b1), .sw_en(1'b1));
                    end
                    default: begin
                        set_dfi_traffic_ovr_cfg    (.sw_mode(1'b0), .sw_en(1'b1));
                    end
                endcase
            end
            1 : begin
                set_dfiwrd_wdp_cfg_m1     (.gb_mode(wrgb_mode), .gb_pipe_dly(2'h0),                .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfiwrcctrl_wdp_cfg_m1 (.gb_mode(wrgb_mode), .gb_pipe_dly(2'h0),                .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfickctrl_wdp_cfg_m1  (.gb_mode(wrgb_mode), .gb_pipe_dly(ckctrl_gb_pipe_dly),  .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfiwctrl_wdp_cfg_m1   (.gb_mode(wrgb_mode), .gb_pipe_dly(wctrl_gb_pipe_dly),   .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfiwenctrl_wdp_cfg_m1 (.gb_mode(wrgb_mode), .gb_pipe_dly(wenctrl_gb_pipe_dly), .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfirctrl_wdp_cfg_m1   (.gb_mode(wrgb_mode), .gb_pipe_dly(rctrl_gb_pipe_dly),   .pre_gb_pipe_en(pre_gb_pipe_en));
                set_dfi_rdgb_mode_m1      (rdgb_mode);

                `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_WRC_M1_CFG    ,POST_GB_FC_DLY, PIPE_EN, 2'h0, 1'b0 );

                set_dfi_paden_pext_cfg_m1 (.wrd_en_cycles(wrd_en), .wrd_oe_cycles(wrd_oe), .wck_oe_cycles(wck_oe), .ie_cycles(ie), .re_cycles(re), .ren_cycles(ren), .rcs_cycles(rcs));
                set_dfi_clken_pext_cfg_m1 (.wr_clken_cycles(wr_clken), .rd_clken_cycles(rd_clken), .ca_clken_cycles(ca_clken));
                case(freq_MHz)
                    230: begin
                        set_dfi_traffic_ovr_cfg_m1    (.sw_mode(1'b1), .sw_en(1'b1));
                    end
                    default: begin
                        set_dfi_traffic_ovr_cfg_m1    (.sw_mode(1'b0), .sw_en(1'b1));
                    end
                endcase
            end
        endcase
    end
endtask

task phy_bringup;
    output int err;
    int err_temp;
    int err_cnt;
    int bl;
    string s, r;
    begin
        `ifdef LPDDR4
            d = "lp4";
        `else
            d = "lp5";
        `endif
        case(vcoFreq1)
            230    : s= "230";
            422    : s= "422";
            652    : s= "652";
            806    : s= "806";
            1075   : s= "1075";
            1612   : s= "1612";
            2112   : s= "2112";
            default: s= "UNKN";
        endcase
        r = (freqRatio == 1) ? "1" : (freqRatio == 2) ? "2" : "UNKN" ;
        fn = {"wddr_1x32.uvm/wddr_1x32_",d,"_",s,"_ratio",r,".uvm.sv"};
        $display("INFO: Open  file %s ...\n", fn );
        fd = $fopen(fn,"w");

        err = 0;
        err_temp = 0;
        err_cnt  = 0;

        set_dfi_buf_clken(1'b0);
        /*Added for GLS*/`CSR_WRF1(DDR_FSW_OFFSET,DDR_FSW_CSP_1_CFG, DIV_RST_OVR_VAL, 1'b1 );
        if (pllfull)
            pll_full;
        else
            pll_short;

        set_phy_ch1_disable();
        //set_pi_cfg (.freq_MHz(vcoFreq1), .msr(0));
        set_pi_cfg (.freq_MHz(vcoFreq1), .freq_ratio(1), .msr(0), .dqs_code('0), .dq_code('0), .ca_code('0));

        sw_csp_byte_sync(); // Dont call for sw_freq
        /*Added for GLS*/`CSR_WRF1(DDR_FSW_OFFSET,DDR_FSW_CSP_1_CFG, DIV_RST_OVR_VAL, 1'b0 );
        /*Added for GLS*/sw_csp_byte_sync();

        `CSR_WR(DDR_DFI_OFFSET,DDR_DFI_CTRLUPD_IF_CFG, 32'h00000005 );
        //set_dfi_traffic_ovr_cfg (.sw_mode(1'b0), .sw_en(1'b1));
        set_dfi_ca_traffic_ovr_cfg (.sw_mode(1'b1), .sw_en(1'b1));
        set_dfi_ca_rddata_en (.en(1'b1));  // Enable CA RDDATA en for CA loopback.

        `ifdef LPK
            // Enable IO loopback
            set_tx_io_cmn_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b1));
        `else
            set_tx_io_cmn_cfg    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b0));
        `endif

        if(freqSw > 0)
        begin
            // M1
            // Setup TX PIs for 90 degree offset
            //set_pi_cfg (.freq_MHz(vcoFreq2), .msr(1));
            set_pi_cfg (.freq_MHz(vcoFreq2), .freq_ratio(1), .msr(1), .dqs_code('0), .dq_code('0), .ca_code('0));

            `ifdef LPK
                // Enable IO loopback
                set_tx_io_cmn_cfg_m1    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b1));
            `else
                set_tx_io_cmn_cfg_m1    (.byte_sel(ALL),    .rank_sel(RANK_ALL), .lpbk_en(1'b0));
            `endif

        end

        //----------------------------------------------------------------------------------
        // Case1: DDR 1:1 - egress DDR2to1
        // ---------------------------------------------------------------------------------
        if(freqRatio == 1) begin
            if(gb_set  == 1) begin
                config11;
                config_end;
            end
            //----------------------------------------------------------------------------------
            // Case2: DDR 1:1 | Feq- Mem:1.064, DP:1.064 | Row-23
            // ---------------------------------------------------------------------------------
            else if(gb_set  == 2) begin
                config11;
                if(freqSw > 0) begin
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // select DQS
                end
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // select DQS
                config_end;
            end

            //----------------------------------------------------------------------------------
            // Case3: DDR 1:1 | Feq- Mem:1.064, DP:1.064 | Row-24
            // ---------------------------------------------------------------------------------
            else if(gb_set  == 3) begin
                config11;
                if(freqSw > 0) begin

                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // select DQS

                end

                // DQ
                set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // select DQS

                config_end;
            end
            //----------------------------------------------------------------------------------
            // Case4: DDR 1:1 | Feq- Mem:1.064, DP:1.064 | Row-25
            // ---------------------------------------------------------------------------------
            else if(gb_set  == 4) begin
                config11;
                if(freqSw > 0) begin
                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // select DQS

                    set_dfi_rdgb_mode_m1      (DFIRGB_1TO1);

                end

                // DQ
                set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_1TO1_HF), .wgb_mode(WGB_1TO1));
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_1TO1_HF), .fgb_mode(FGB_1TO1),    .wck_mode(1'b1)); // select DQS

                set_dfi_rdgb_mode      (DFIRGB_1TO1);

                config_end;
            end

            //----------------------------------------------------------------------------------
            // Case5: DDR 1:1 | Feq- Mem:1.064, DP:1.064 | Row-26
            // ---------------------------------------------------------------------------------
            else if(gb_set  == 5) begin
                config11;
                if(freqSw > 0) begin
                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_IR), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_IR), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // select DQS

                end

                set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_IR), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_IR), .fgb_mode(FGB_2TO2),    .wck_mode(1'b1)); // select DQS

                config_end;
            end

            //----------------------------------------------------------------------------------
            // Case6: DDR 1:1 | Feq- Mem:2.128, DP:1.064 | Row-27
            // ---------------------------------------------------------------------------------
            else if(gb_set  == 6) begin
                config11;

                if(freqSw > 0) begin
                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_4TO1_IR), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_4TO1_IR), .fgb_mode(FGB_4TO4),    .wck_mode(1'b1)); // select DQS

                    //DFI Configuration
                    set_dfiwrd_wdp_cfg_m1     (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfiwrcctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfickctrl_wdp_cfg_m1  (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                    set_dfiwctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                    set_dfiwenctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                    set_dfirctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                    set_dfi_rdgb_mode_m1      (DFIRGB_4TO4);

                end

                set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_4TO1_IR), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_4TO1_IR), .fgb_mode(FGB_4TO4),    .wck_mode(1'b1)); // select DQS

                //DFI Configuration
                set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h3), .pre_gb_pipe_en(1'b0));
                set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                set_dfi_rdgb_mode      (DFIRGB_4TO4);

                config_end;
            end

        end  //frequency ==1 ends here

        //----------------------------------------------------------------------------------
        // Case4: DDR - DP 4to1 - egress QDR2to1
        // ---------------------------------------------------------------------------------
        if(freqRatio == 2) begin
            if(gb_set == 1)
            begin
                config21 ;
                config_end;

            end

            //----------------------------------------------------------------------------------
            // Case4: DDR - DP 2to1 | Freq- Mem:2.128 , DP:1.064 | WGB_4TO4 (Row : 19)
            // ---------------------------------------------------------------------------------
            else if(gb_set == 2)
            begin
                config21 ;
                if(freqSw > 0)
                begin
                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b1)); // CK  Loop back
                end

                // DQ
                set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_tx_gb             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b1)); // CK  Loop back

                config_end;

            end

            //----------------------------------------------------------------------------------
            // Case4: DDR - DP 2to1 | Freq- Mem:2.128 , DP:1.064 | WGB_4TO2 | Row : 20
            // ---------------------------------------------------------------------------------
            else if(gb_set == 3)
            begin

                config21;
                if(freqSw > 0)
                begin
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO4),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_4TO2));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_4TO2));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO4),  .wck_mode(1'b1)); // CK  Loop back

                end

                // DQ
                set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO4),    .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL), .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_4TO2));
                set_tx_gb             (.byte_sel(CA),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_4TO2));
                set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO4),  .wck_mode(1'b1)); // CK  Loop back
                config_end;

            end

            //----------------------------------------------------------------------------------
            // Case4: DDR - DP 2to1 | Freq- Mem: 2.128 , DP: 2.128 | WGB_2TO2 | Row : 21
            // ---------------------------------------------------------------------------------
            else if(gb_set == 4)
            begin
                config21;
                if(freqSw > 0)
                begin
                    // DQ
                    set_rx_gb_m1             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),    .wck_mode(1'b0)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                    set_tx_gb_m1             (.byte_sel(CA),         .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                    set_rx_gb_m1             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),  .wck_mode(1'b1)); // CK  Loop back
                    //DFI Configuration
                    set_dfiwrd_wdp_cfg_m1     (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfiwrcctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfickctrl_wdp_cfg_m1  (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
                    set_dfiwctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
                    set_dfiwenctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(8'h10), .pre_gb_pipe_en(1'b0));
                    set_dfirctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                    set_dfi_rdgb_mode_m1      (DFIRGB_2TO4);
                end

                // DQ
                set_rx_gb             (.byte_sel(DQ_ALL),     .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2), .wck_mode(1'b0)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL),     .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                set_tx_gb             (.byte_sel(CA),         .tgb_mode(DGB_2TO1_HF), .wgb_mode(WGB_2TO2));
                set_rx_gb             (.byte_sel(CA),         .rgb_mode(DGB_2TO1_HF), .fgb_mode(FGB_2TO2),  .wck_mode(1'b1)); // CK  Loop back

                //DFI Configuration
                set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
                set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(8'h10), .pre_gb_pipe_en(1'b0));
                set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_4TO2), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                set_dfi_rdgb_mode      (DFIRGB_2TO4);

                config_end;
            end
        end // freqratio==2 ends here

        //----------------------------------------------------------------------------------
        // Case: DDR - 4to1 | Freq: Mem-3.2, DP-0.8
        // ---------------------------------------------------------------------------------
        if(freqRatio == 4) begin
            if(gb_set == 1)
            begin
                config41;
                config_end;
            end
            //----------------------------------------------------------------------------------
            // Case: DDR - 4to1 | Freq: Mem- 3.2, DP- 1.6
            // ---------------------------------------------------------------------------------
            else if(gb_set == 2)
            begin
                config41;

                if(freqSw > 0)
                begin
                    // FREQ RATIO 1:4, DP_Freq : 1.6
                    set_rx_gb_m1             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b1)); // select DQS
                    set_tx_gb_m1             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_tx_gb_m1             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                    set_rx_gb_m1             (.byte_sel(CA),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b1)); // CK  Loop back

                    // FREQ RATIO 1:4, DP_Freq : 1.6
                    set_dfiwrd_wdp_cfg_m1     (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfiwrcctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                    set_dfickctrl_wdp_cfg_m1  (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
                    set_dfiwctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                    set_dfiwenctrl_wdp_cfg_m1 (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(8'h10), .pre_gb_pipe_en(1'b0));
                    set_dfirctrl_wdp_cfg_m1   (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                    set_dfi_rdgb_mode_m1      (DFIRGB_4TO8);
                end

                // FREQ RATIO 1:4, DP_Freq : 1.6
                set_rx_gb             (.byte_sel(DQ_ALL), .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),    .wck_mode(1'b1)); // select DQS
                set_tx_gb             (.byte_sel(DQ_ALL), .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_tx_gb             (.byte_sel(CA),     .tgb_mode(DGB_4TO1_HF), .wgb_mode(WGB_4TO4));
                set_rx_gb             (.byte_sel(CA),     .rgb_mode(DGB_4TO1_HF), .fgb_mode(FGB_4TO4),  .wck_mode(1'b1)); // CK  Loop back

                // FREQ RATIO 1:4, DP_Freq : 1.6 shankaran
                set_dfiwrd_wdp_cfg     (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfiwrcctrl_wdp_cfg (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h0), .pre_gb_pipe_en(1'b0));
                set_dfickctrl_wdp_cfg  (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b1));
                set_dfiwctrl_wdp_cfg   (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                set_dfiwenctrl_wdp_cfg (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(8'h10), .pre_gb_pipe_en(1'b0));
                set_dfirctrl_wdp_cfg   (.gb_mode(DFIWGB_8TO4), .gb_pipe_dly(2'h2), .pre_gb_pipe_en(1'b0));
                set_dfi_rdgb_mode      (DFIRGB_4TO8);

                config_end;

            end
        end // freqratio==4 end

        // FIXME: Must be enabled for Gear Box Test cases. Add a plus arg in next DV tag.
        //set_dfi_traffic_ovr_cfg (.sw_mode(0'b1), .sw_en(1'b1));
        //set_dfi_ca_traffic_ovr_cfg (.sw_mode(0'b1), .sw_en(1'b1));
        $display ("INFO: PHY bringup done..");
        $fclose(fd);

    end
endtask

task dfi_freqsw;
    logic ovr, req, ack, switch_done;
    logic [31:0] wdata;

    begin
        for (int i=0; i < freqSw; i++) begin

            wait(state == 1);

            #10us;

            // Enable HW Status ACK (i.e. assert INIT_COMPLETE)
            `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_ACK_OVR, 1'b0);

            `CSR_WRF1(DDR_FSW_OFFSET,DDR_FSW_CTRL_CFG, VCO_SEL_OVR, 1'b0);

            // SW PREP done
            `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b1);

            state = 2;
            `uvm_info(get_type_name(), $sformatf("Fsw state : %0d",state), UVM_LOW);
            wait(state == 3);

            if ((freqSw % 2) == 1 )
                config_vips(vcoFreq2,freqRatio);
            else
                config_vips(vcoFreq1,freqRatio);

            #10ns;

            do begin
                // get_dfi_status_ack(ack);
                get_cmn_switch_done(switch_done);
                //end while (!ack || !switch_done);
            end while (!switch_done);

            state = 4;
            `uvm_info(get_type_name(), $sformatf("Fsw state : %0d",state), UVM_LOW);
            wait(state == 5);

            #200ns;
            `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PREP_DONE, 1'b0);
            `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b1);
            #10ns;
            `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CTRL_CFG, PSTWORK_DONE, 1'b0);
            `CSR_WRF1(DDR_MCU_CSR_OFFSET, WAV_MCU_IRQ_FAST_CLR_CFG, CLR, 1'b1);
            //  `CSR_WRF1(DDR_CMN_OFFSET, DDR_CMN_CTRL_CFG, PREP_DONE, 1'b1);

        end
    end
endtask

function int get_freqid (input int freq);
    int freqid;
    case(freq)
        230  : freqid = 1;
        400  : freqid = 2;
        652  : freqid = 3;
        806  : freqid = 4;
        1067 : freqid = 5;
        1612 : freqid = 8;
        2112 : freqid = 9;
    endcase
    return freqid;
endfunction

task mcu_freqsw;

    output int err;
    integer indx;
    logic [31:0] id;
    logic [31:0] data;
    logic ovr, req, ack, switch_done;
    int freq;
    begin
        err = 0;
        #50ns;
        initialize_mem ;
        #1us;
        set_ldo_en(1'b1);
        #10ns;

        set_phy_ch1_disable();

        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));

        phy2host_receive_msg( id, data);
        `uvm_info(get_type_name(), $sformatf("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data), UVM_LOW);

        wait(state == 1);

        if ((freqSw % 2) == 1 )
            freq = vcoFreq2;
        else
            freq = vcoFreq1;

        `uvm_info(get_type_name(), $sformatf("freq = %d, get_freqid = %d,\n", freq,  get_freqid(freq)), UVM_LOW);

        host2phy_hw_freqswitch(get_freqid(freq));

        phy2host_receive_msg( id, data);
        `uvm_info(get_type_name(), $sformatf("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data), UVM_LOW);

        state = 2;
        `uvm_info(get_type_name(), $sformatf("Fsw state : %0d",state), UVM_LOW);
        wait(state == 3);

        if ((freqSw % 2) == 1 )
            config_vips(freq,freqRatio);
        else
            config_vips(freq,freqRatio);

        state = 4;
        `uvm_info(get_type_name(), $sformatf("Fsw state : %0d",state), UVM_LOW);
        wait(state == 5);

    end
endtask

task mcu_dfiupdate;

    output int err;
    integer indx;
    logic [31:0] id;
    logic [31:0] data;
    logic ovr, req, ack, switch_done;
    int freq;
    begin
        err = 0;
        #50ns;
        initialize_mem ;
        #1us;
        set_ldo_en(1'b1);
        #10ns;

        set_phy_ch1_disable();

        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));

        // Wait for message Boot is done
        phy2host_receive_msg( id, data);
        `uvm_info(get_type_name(), $sformatf("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data), UVM_LOW);

        wait(state == 1);

        host2phy_send_msg(3,0);
        `uvm_info(get_type_name(), $sformatf("PHY MSG SENT : ID = %x, DATA = %x,\n", 3, 0), UVM_LOW);

        state =2;
        `uvm_info(get_type_name(), $sformatf("dfiupdate state : %0d",state), UVM_LOW);

        wait(state == 3);

        host2phy_send_msg(0,0);

        #1us;

    end
endtask

task mcu_dfiphymas;

    output int err;
    integer indx;
    logic [31:0] id;
    logic [31:0] data;
    logic ovr, req, ack, switch_done;
    int freq;
    begin
        err = 0;
        #50ns;
        initialize_mem ;
        #1us;
        set_ldo_en(1'b1);
        #10ns;

        set_phy_ch1_disable();

        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));

        // Wait for message Boot is done
        phy2host_receive_msg( id, data);
        `uvm_info(get_type_name(), $sformatf("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data), UVM_LOW);

        wait(state == 1);

        host2phy_send_msg(4,0);
        `uvm_info(get_type_name(), $sformatf("PHY MSG SENT : ID = %x, DATA = %x,\n", 3, 0), UVM_LOW);

        state =2;
        `uvm_info(get_type_name(), $sformatf("mcu_dfiphymas state : %0d",state), UVM_LOW);

        wait(state == 3);

        host2phy_send_msg(0,0);

        #1us;

    end
endtask

task mcu_dfilp;

    output int err;
    integer indx;
    logic [31:0] id;
    logic [31:0] data;
    logic ovr, req, ack, switch_done;
    int freq;
    begin
        err = 0;
        #50ns;
        initialize_mem ;
        #1us;
        set_ldo_en(1'b1);
        #10ns;

        set_phy_ch1_disable();

        set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));

        // Wait for message Boot is done
        phy2host_receive_msg( id, data);
        `uvm_info(get_type_name(), $sformatf("PHY MSG RECIEVED : ID = %x, DATA = %x,\n", id, data), UVM_LOW);

        wait(state == 1);
    end
endtask
