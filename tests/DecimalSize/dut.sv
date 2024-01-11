


module gem_gxl();
  parameter [31:0] p_edma_queues              = 32'd1;
  parameter [31:0] p_edma_tx_pbuf_data        = 32;
  parameter [31:0] p_edma_rx_pbuf_data        = 32;
  parameter [31:0] p_edma_tx_pbuf_addr        = 9 ;
  parameter [31:0] p_edma_rx_pbuf_addr        = 9 ;
  



    parameter [31:0] p_edma_emac_tx_pbuf_addr = 32'd10;
    parameter [31:0] p_edma_emac_rx_pbuf_addr = 32'd10;
  
  parameter p_edma_tx_pbuf_queue_segment_size = 1;
  parameter [31:0] p_emac_bus_width           = 32;
  parameter [31:0] p_edma_bus_width           = 32;
  parameter p_edma_addr_width                 = 32;
  parameter p_edma_rx_fifo_size               = 10;
  parameter p_edma_tx_fifo_size               = 10;
  parameter p_edma_rx_base2_fifo_size         = 4'b1010;
  parameter p_edma_tx_base2_fifo_size         = 4'b1010;
  parameter p_edma_rx_fifo_cnt_width          = 4 ;
  parameter p_edma_tx_fifo_cnt_width          = 4 ;
  parameter p_edma_axi_access_pipeline_bits   = 4'd4;
  parameter p_edma_axi_tx_descr_rd_buff_bits  = 4'd1;
  parameter p_edma_axi_rx_descr_rd_buff_bits  = 4'd1;
  parameter p_edma_axi_tx_descr_wr_buff_bits  = 4'd1;
  parameter p_edma_axi_rx_descr_wr_buff_bits  = 4'd1;
  parameter p_edma_hprot_value                = 4'b0001;
  parameter p_edma_axi_prot_value             = 3'b000 ;
  parameter p_edma_axi_arcache_value          = 4'b0000 ;
  parameter p_edma_axi_awcache_value          = 4'b0000 ;
  parameter p_edma_dma_bus_width_def          = 2'b00;
  parameter p_edma_mdc_clock_div              = 3'b010;
  parameter p_edma_endian_swap_def            = 2'b00;
  parameter p_edma_rx_pbuf_size_def           = 2'b11;
  parameter p_edma_tx_pbuf_size_def           = 1'b1;
  parameter p_edma_rx_buffer_length_def       = 8'd2;
  parameter p_edma_jumbo_max_length           = 14'd10240;
  parameter p_gem_rx_pipeline_delay           = 10;
  parameter p_edma_srd_width                  = 20;


parameter p_edma_has_pcs = 1'b0;







parameter p_edma_pcs_legacy_if = 1'b0;





parameter p_edma_pcs_code_align = 1'b1;





  parameter p_xgm                  = 1'b0;



  parameter p_edma_phy_ident       = 1'b1;





  parameter p_num_spec_add_filters = 8;







  parameter p_num_type1_screeners = 8'd0;




  parameter p_num_type2_screeners = 8'd0;


  parameter p_num_scr2_compare_regs = 8'd1;




  parameter p_num_scr2_ethtype_regs = 8'd1;






  parameter p_edma_tx_pbuf_num_segments_q0 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q1 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q2 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q3 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q4 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q5 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q6 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q7 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q8 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q9 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q10 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q11 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q12 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q13 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q14 = 32'd0;




  parameter p_edma_tx_pbuf_num_segments_q15 = 32'd0;



  parameter p_edma_exclude_cbs = 1'b1;





  parameter p_edma_exclude_qbv = 1'd1;





  parameter p_edma_pbuf_cutthru = 1'b1;





  parameter p_edma_tsu = 1'b1;







  parameter p_edma_asf_prot_tsu = 1'd0;





  parameter p_edma_tsu_clk = 1'b0;





  parameter p_edma_ext_tsu_timer = 1'b0;



  parameter p_edma_axi = 1'b1;







  parameter p_edma_lso = 1'b0;





  parameter p_edma_rsc = 1'b0;





  parameter p_edma_spram = 1'b0;





  parameter p_edma_ext_fifo_interface  = 1'b0;





  parameter p_edma_add_rx_external_fifo_if  = 1'b0;





  parameter p_edma_add_tx_external_fifo_if  = 1'b0;





  parameter p_edma_host_if_soft_select = 1'b0;





  parameter p_edma_pfc_multi_quantum   = 1'b0;



  parameter p_edma_rx_pkt_buffer   = 1'b1;





  parameter p_edma_tx_pkt_buffer   = 1'b1;









  parameter p_gem_user_io = 1'b0;
  parameter p_gem_user_in_width = 32'd1;
  parameter p_gem_user_out_width = 32'd1;





  parameter p_edma_irq_read_clear = 1'b0;





  parameter p_edma_no_snapshot = 1'b0;





  parameter p_edma_no_stats = 1'b0;



  parameter p_edma_no_pcs = 1'b1;





  parameter p_edma_int_loopback = 1'b1;







  parameter p_edma_tx_add_fifo_if = 1'b0;













  parameter p_edma_asf_dap_prot  = 1'd0;
  parameter p_emac_parity_width  = 8'd0;
  parameter p_edma_parity_width  = 8'd0;
  parameter p_edma_rx_pbuf_prty  = 8'd0;
  parameter p_edma_tx_pbuf_prty  = 8'd0;


  parameter p_edma_rx_pbuf_addr_par = (p_edma_rx_pbuf_addr+7)/8;
  parameter p_edma_tx_pbuf_addr_par = (p_edma_tx_pbuf_addr+7)/8;
  parameter p_edma_emac_rx_pbuf_addr_par = (p_edma_emac_rx_pbuf_addr+7)/8;
  parameter p_edma_emac_tx_pbuf_addr_par = (p_edma_emac_tx_pbuf_addr+7)/8;








  parameter p_edma_asf_ecc_sram = 1'd0;
  parameter p_edma_rx_pbuf_temp     = p_edma_rx_pbuf_data == 32'd128 ? 8'd16
                                                                      : p_edma_rx_pbuf_data == 32'd64 ? 8'd8 : 8'd4;
  parameter p_edma_tx_pbuf_temp     = p_edma_tx_pbuf_data == 32'd128 ? 8'd16
                                                                      : p_edma_tx_pbuf_data == 32'd64 ? 8'd8 : 8'd4;


  parameter p_edma_tx_pbuf_reduncy  = ((p_edma_asf_dap_prot > 0) || (p_edma_asf_ecc_sram > 0)) ? p_edma_tx_pbuf_addr_par[7:0] + p_edma_tx_pbuf_temp[7:0]
                                                                                              : 8'd0;
  parameter p_edma_rx_pbuf_reduncy  = ((p_edma_asf_dap_prot > 0) || (p_edma_asf_ecc_sram > 0)) ? p_edma_rx_pbuf_addr_par[7:0] + p_edma_rx_pbuf_temp[7:0]
                                                                                              : 8'd0;
  parameter p_edma_emac_tx_pbuf_reduncy  = ((p_edma_asf_dap_prot > 0) || (p_edma_asf_ecc_sram > 0)) ? p_edma_emac_tx_pbuf_addr_par[7:0] + p_edma_tx_pbuf_temp[7:0]
                                                                                              : 8'd0;
  parameter p_edma_emac_rx_pbuf_reduncy  = ((p_edma_asf_dap_prot > 0) || (p_edma_asf_ecc_sram > 0)) ? p_edma_emac_rx_pbuf_addr_par[7:0] + p_edma_rx_pbuf_temp[7:0]
                                                                                              : 8'd0;





  parameter p_edma_asf_csr_prot = 1'd0;





  parameter p_edma_asf_trans_to_prot  = 1'd0;


  parameter p_edma_asf_integrity_prot = 1'd0;

  parameter p_edma_asf_prot_tx_sched  = 1'd0;

  parameter p_edma_asf_host_par = 1'd0;





  parameter p_gem_num_cb_streams  = 8'd1;
  parameter p_gem_has_cb          = 1'b0;





  parameter p_edma_has_br          = 1'b0;



  parameter p_gem_cb_history_len  = 8'd64;





  parameter p_edma_using_rgmii = 1'b1;







  parameter p_edma_include_rmii = 1'b0;


parameter grouped_params = {
p_edma_rx_pbuf_reduncy,

p_edma_tx_pbuf_reduncy,
p_edma_tx_pbuf_prty,
p_edma_rx_pbuf_prty,
p_edma_parity_width,
p_emac_parity_width,
p_edma_asf_trans_to_prot,
p_edma_asf_integrity_prot,
p_edma_asf_prot_tx_sched,
p_edma_asf_host_par,
p_edma_asf_ecc_sram,
p_edma_asf_csr_prot,
p_edma_asf_dap_prot,
p_edma_asf_prot_tsu,
p_edma_has_br,
p_edma_emac_tx_pbuf_addr,
p_edma_emac_rx_pbuf_addr,
p_edma_pcs_code_align,
p_edma_using_rgmii,

p_edma_include_rmii,
p_gem_rx_pipeline_delay,
p_edma_srd_width,
p_edma_has_pcs,
p_edma_pcs_legacy_if,
p_gem_num_cb_streams,
p_gem_cb_history_len,
p_gem_has_cb,
p_edma_exclude_qbv,
p_edma_queues,
p_edma_tx_pbuf_data,
p_edma_rx_pbuf_data,
p_edma_tx_pbuf_addr,
p_edma_rx_pbuf_addr,
p_edma_tx_pbuf_queue_segment_size,
p_emac_bus_width,
p_edma_bus_width,
p_edma_addr_width,
p_edma_rx_fifo_size,
p_edma_tx_fifo_size,
p_edma_rx_fifo_cnt_width,
p_edma_tx_fifo_cnt_width,
p_xgm,
p_edma_phy_ident,
p_num_spec_add_filters,
p_edma_tx_pbuf_num_segments_q0,
p_edma_tx_pbuf_num_segments_q1,
p_edma_tx_pbuf_num_segments_q2,
p_edma_tx_pbuf_num_segments_q3,
p_edma_tx_pbuf_num_segments_q4,
p_edma_tx_pbuf_num_segments_q5,
p_edma_tx_pbuf_num_segments_q6,
p_edma_tx_pbuf_num_segments_q7,
p_edma_tx_pbuf_num_segments_q8,
p_edma_tx_pbuf_num_segments_q9,
p_edma_tx_pbuf_num_segments_q10,
p_edma_tx_pbuf_num_segments_q11,
p_edma_tx_pbuf_num_segments_q12,
p_edma_tx_pbuf_num_segments_q13,
p_edma_tx_pbuf_num_segments_q14,
p_edma_tx_pbuf_num_segments_q15,
p_edma_exclude_cbs,
p_edma_pbuf_cutthru,
p_edma_tsu,
p_edma_tsu_clk,
p_edma_ext_tsu_timer,
p_edma_axi,
p_edma_lso,
p_edma_rsc,
p_edma_spram,
p_edma_ext_fifo_interface,
p_edma_add_rx_external_fifo_if,
p_edma_add_tx_external_fifo_if,
p_edma_host_if_soft_select,
p_edma_pfc_multi_quantum,
p_edma_rx_pkt_buffer,
p_edma_tx_pkt_buffer,
p_gem_user_io,
p_gem_user_in_width,
p_gem_user_out_width,
p_edma_irq_read_clear,
p_edma_no_snapshot,
p_edma_no_stats,
p_edma_no_pcs,
p_edma_int_loopback,
p_edma_tx_add_fifo_if,
p_edma_rx_base2_fifo_size,
p_edma_tx_base2_fifo_size,
p_edma_axi_access_pipeline_bits,
p_edma_axi_tx_descr_rd_buff_bits,
p_edma_axi_rx_descr_rd_buff_bits,
p_edma_axi_tx_descr_wr_buff_bits,
p_edma_axi_rx_descr_wr_buff_bits,
p_edma_hprot_value,
p_edma_axi_prot_value,
p_edma_axi_arcache_value,
p_edma_axi_awcache_value,
p_edma_dma_bus_width_def,
p_edma_mdc_clock_div,
p_edma_endian_swap_def,
p_edma_rx_pbuf_size_def,
p_edma_tx_pbuf_size_def,
p_edma_rx_buffer_length_def,
p_edma_jumbo_max_length,
p_num_type1_screeners,
p_num_type2_screeners,
p_num_scr2_compare_regs,
p_num_scr2_ethtype_regs
};
   
//gem_ss #(
 //   .grouped_params(grouped_params),
//    .p_edma_emac_tx_pbuf_reduncy(p_edma_emac_tx_pbuf_reduncy),
//    .p_edma_emac_rx_pbuf_reduncy(p_edma_emac_rx_pbuf_reduncy)
 //        ) i_gem_ss ();
   
endmodule // gem_gxl



module gem_ss ();


  parameter [1363:0] grouped_params = {1364{1'b0}};


  parameter [7:0]   p_edma_rx_pbuf_reduncy                = grouped_params [1363:1356];
parameter [7:0]   p_edma_tx_pbuf_reduncy                = grouped_params [1355:1348];
parameter [7:0]   p_edma_tx_pbuf_prty                   = grouped_params [1347:1340];
parameter [7:0]   p_edma_rx_pbuf_prty                   = grouped_params [1339:1332];
parameter [7:0]   p_edma_parity_width                   = grouped_params [1331:1324];
parameter [7:0]   p_emac_parity_width                   = grouped_params [1323:1316];
parameter         p_edma_asf_trans_to_prot              = grouped_params [1315];
parameter         p_edma_asf_integrity_prot             = grouped_params [1314];
parameter         p_edma_asf_prot_tx_sched              = grouped_params [1313];
parameter         p_edma_asf_host_par                   = grouped_params [1312];
parameter         p_edma_asf_ecc_sram                   = grouped_params [1311];
parameter         p_edma_asf_csr_prot                   = grouped_params [1310];
parameter         p_edma_asf_dap_prot                   = grouped_params [1309];
parameter         p_edma_asf_prot_tsu                   = grouped_params [1308];
parameter         p_edma_has_br                         = grouped_params [1307];
parameter [31:0]  p_edma_emac_tx_pbuf_addr              = grouped_params [1306:1275];
parameter [31:0]  p_edma_emac_rx_pbuf_addr              = grouped_params [1274:1243];
parameter         p_edma_pcs_code_align                 = grouped_params [1242];
parameter         p_edma_using_rgmii                    = grouped_params [1241];
parameter         p_edma_include_rmii                   = grouped_params [1240];
parameter [31:0]  p_gem_rx_pipeline_delay               = grouped_params [1239:1208];
parameter [31:0]  p_edma_srd_width                      = grouped_params [1207:1176];
parameter         p_edma_has_pcs                        = grouped_params [1175];
parameter         p_edma_pcs_legacy_if                  = grouped_params [1174];
parameter [7:0]   p_gem_num_cb_streams                  = grouped_params [1173:1166];
parameter [7:0]   p_gem_cb_history_len                  = grouped_params [1165:1158];
parameter         p_gem_has_cb                          = grouped_params [1157];
parameter         p_edma_exclude_qbv                    = grouped_params [1156];
parameter [31:0]  p_edma_queues                         = grouped_params [1155:1124];
parameter [31:0]  p_edma_tx_pbuf_data                   = grouped_params [1123:1092];
parameter [31:0]  p_edma_rx_pbuf_data                   = grouped_params [1091:1060];
parameter [31:0]  p_edma_tx_pbuf_addr                   = grouped_params [1059:1028];
parameter [31:0]  p_edma_rx_pbuf_addr                   = grouped_params [1027:996];
parameter [31:0]  p_edma_tx_pbuf_queue_segment_size     = grouped_params [995:964];
parameter [31:0]  p_emac_bus_width                      = grouped_params [963:932];
parameter [31:0]  p_edma_bus_width                      = grouped_params [931:900];
parameter [31:0]  p_edma_addr_width                     = grouped_params [899:868];
parameter [31:0]  p_edma_rx_fifo_size                   = grouped_params [867:836];
parameter [31:0]  p_edma_tx_fifo_size                   = grouped_params [835:804];
parameter [31:0]  p_edma_rx_fifo_cnt_width              = grouped_params [803:772];
parameter [31:0]  p_edma_tx_fifo_cnt_width              = grouped_params [771:740];
parameter         p_xgm                                 = grouped_params [739];
parameter         p_edma_phy_ident                      = grouped_params [738];
parameter [31:0]  p_num_spec_add_filters                = grouped_params [737:706];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q0        = grouped_params [705:674];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q1        = grouped_params [673:642];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q2        = grouped_params [641:610];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q3        = grouped_params [609:578];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q4        = grouped_params [577:546];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q5        = grouped_params [545:514];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q6        = grouped_params [513:482];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q7        = grouped_params [481:450];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q8        = grouped_params [449:418];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q9        = grouped_params [417:386];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q10       = grouped_params [385:354];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q11       = grouped_params [353:322];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q12       = grouped_params [321:290];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q13       = grouped_params [289:258];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q14       = grouped_params [257:226];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q15       = grouped_params [225:194];
parameter         p_edma_exclude_cbs                    = grouped_params [193];
parameter         p_edma_pbuf_cutthru                   = grouped_params [192];
parameter         p_edma_tsu                            = grouped_params [191];
parameter         p_edma_tsu_clk                        = grouped_params [190];
parameter         p_edma_ext_tsu_timer                  = grouped_params [189];
parameter         p_edma_axi                            = grouped_params [188];
parameter         p_edma_lso                            = grouped_params [187];
parameter         p_edma_rsc                            = grouped_params [186];
parameter         p_edma_spram                          = grouped_params [185];
parameter         p_edma_ext_fifo_interface             = grouped_params [184];
parameter         p_edma_add_rx_external_fifo_if        = grouped_params [183];
parameter         p_edma_add_tx_external_fifo_if        = grouped_params [182];
parameter         p_edma_host_if_soft_select            = grouped_params [181];
parameter         p_edma_pfc_multi_quantum              = grouped_params [180];
parameter         p_edma_rx_pkt_buffer                  = grouped_params [179];
parameter         p_edma_tx_pkt_buffer                  = grouped_params [178];
parameter         p_gem_user_io                         = grouped_params [177];
parameter [31:0]  p_gem_user_in_width                   = grouped_params [176:145];
parameter [31:0]  p_gem_user_out_width                  = grouped_params [144:113];
parameter         p_edma_irq_read_clear                 = grouped_params [112];
parameter         p_edma_no_snapshot                    = grouped_params [111];
parameter         p_edma_no_stats                       = grouped_params [110];
parameter         p_edma_no_pcs                         = grouped_params [109];
parameter         p_edma_int_loopback                   = grouped_params [108];
parameter         p_edma_tx_add_fifo_if                 = grouped_params [107];
parameter [3:0]   p_edma_rx_base2_fifo_size             = grouped_params [106:103];
parameter [3:0]   p_edma_tx_base2_fifo_size             = grouped_params [102:99];
parameter [3:0]   p_edma_axi_access_pipeline_bits       = grouped_params [98:95];
parameter [3:0]   p_edma_axi_tx_descr_rd_buff_bits      = grouped_params [94:91];
parameter [3:0]   p_edma_axi_rx_descr_rd_buff_bits      = grouped_params [90:87];
parameter [3:0]   p_edma_axi_tx_descr_wr_buff_bits      = grouped_params [86:83];
parameter [3:0]   p_edma_axi_rx_descr_wr_buff_bits      = grouped_params [82:79];
parameter [3:0]   p_edma_hprot_value                    = grouped_params [78:75];
parameter [2:0]   p_edma_axi_prot_value                 = grouped_params [74:72];
parameter [3:0]   p_edma_axi_arcache_value              = grouped_params [71:68];
parameter [3:0]   p_edma_axi_awcache_value              = grouped_params [67:64];
parameter [1:0]   p_edma_dma_bus_width_def              = grouped_params [63:62];
parameter [2:0]   p_edma_mdc_clock_div                  = grouped_params [61:59];
parameter [1:0]   p_edma_endian_swap_def                = grouped_params [58:57];
parameter [1:0]   p_edma_rx_pbuf_size_def               = grouped_params [56:55];
parameter         p_edma_tx_pbuf_size_def               = grouped_params [54];
parameter [7:0]   p_edma_rx_buffer_length_def           = grouped_params [53:46];
parameter [13:0]  p_edma_jumbo_max_length               = grouped_params [45:32];
parameter [7:0]   p_num_type1_screeners                 = grouped_params [31:24];
parameter [7:0]   p_num_type2_screeners                 = grouped_params [23:16];
parameter [7:0]   p_num_scr2_compare_regs               = grouped_params [15:8];
parameter [7:0]   p_num_scr2_ethtype_regs               = grouped_params [7:0];

// Parameters generated from above:
parameter p_emac_bus_pwid     = p_emac_bus_width/8;
parameter p_edma_bus_pwid     = p_edma_bus_width/8;
parameter p_edma_addr_pwid    = p_edma_addr_width/8;
parameter p_edma_rx_pbuf_pwid = p_edma_rx_pbuf_data/8;
parameter p_edma_tx_pbuf_pwid = p_edma_tx_pbuf_data/8;


  // If 802.3 BR functionality is added, the EMAC has a cutdown capability
  // from the PMAC
  parameter emac_grouped_params = {grouped_params[1363:1174],
                                   (grouped_params[1157] ? 8'd2 : 8'd1),   // Fix p_gem_num_cb_streams to 2 if CB has been enabled (p_gem_has_cb is in bit 1157)
                                   grouped_params[1165:1156],
                                   32'd1,                                  // Fix p_edma_queues to 1
                                   grouped_params[1123:1060],
                                   p_edma_emac_tx_pbuf_addr,               // Overwrite p_edma_tx_pbuf_addr with p_edma_tx_pbuf_addr
                                   p_edma_emac_rx_pbuf_addr,               // Overwrite p_edma_rx_pbuf_addr with p_edma_rx_pbuf_addr
                                   grouped_params[995:190],
                                   1'b1,                                   // ensure p_edma_ext_tsu_timer is set so eMAC can use pMAC's TSU
                                   grouped_params[188:187],
                                   1'b0,                                   // Disable p_edma_rsc
                                   grouped_params[185:178],
                                   1'b0,                                   // Disable user_io
                                   32'd1,                                  // set user_in_width to 1
                                   32'd1,                                  // set user_out_width to 1
                                   grouped_params[112:32],
                                   (grouped_params[1157] ? 8'd1 : 8'd0),   // No Type 1 screeners required as only 1 queue. Need to set to 1 though to avoid comp error
                                   (grouped_params[1157] ? 8'd2 : 8'd0),   // Fix to two Type 2 screeners for 802.1CB support (max 2 streams)
                                   (grouped_params[1157] ? 8'd6 : 8'd0),   // Fix to 6 compare regs for 802.1CB support (stream ID identification requires 3 comp regs per stream)
                                   8'd0 // No Ethtype regs required
                                  };

  parameter p_edma_emac_tx_pbuf_reduncy = p_edma_tx_pbuf_reduncy;
  parameter p_edma_emac_rx_pbuf_reduncy = p_edma_rx_pbuf_reduncy;

  parameter p_tx_sram_width = p_edma_tx_pbuf_reduncy + p_edma_tx_pbuf_data;
  parameter p_rx_sram_width = p_edma_rx_pbuf_reduncy + p_edma_rx_pbuf_data;
  parameter p_emac_tx_sram_width = p_edma_emac_tx_pbuf_reduncy + p_edma_tx_pbuf_data;
  parameter p_emac_rx_sram_width = p_edma_emac_rx_pbuf_reduncy + p_edma_rx_pbuf_data;


gem_top #(.grouped_params(grouped_params),
            .p_tx_sram_width(p_tx_sram_width),
            .p_rx_sram_width(p_rx_sram_width))

   i_gem_top ();
   
   
endmodule


module gem_top ();


  parameter [1363:0] grouped_params     = {1364{1'b0}};
  parameter          DRD_PKTDATA        = 2'b10;  // Read TX data from AXI
  parameter          RX_DMA_DATA_STORE  = 3'b011; // Data store
  parameter          p_tx_sram_width    = 64;
  parameter          p_rx_sram_width    = 64;

  parameter [7:0]   p_edma_rx_pbuf_reduncy                = grouped_params [1363:1356];
parameter [7:0]   p_edma_tx_pbuf_reduncy                = grouped_params [1355:1348];
parameter [7:0]   p_edma_tx_pbuf_prty                   = grouped_params [1347:1340];
parameter [7:0]   p_edma_rx_pbuf_prty                   = grouped_params [1339:1332];
parameter [7:0]   p_edma_parity_width                   = grouped_params [1331:1324];
parameter [7:0]   p_emac_parity_width                   = grouped_params [1323:1316];
parameter         p_edma_asf_trans_to_prot              = grouped_params [1315];
parameter         p_edma_asf_integrity_prot             = grouped_params [1314];
parameter         p_edma_asf_prot_tx_sched              = grouped_params [1313];
parameter         p_edma_asf_host_par                   = grouped_params [1312];
parameter         p_edma_asf_ecc_sram                   = grouped_params [1311];
parameter         p_edma_asf_csr_prot                   = grouped_params [1310];
parameter         p_edma_asf_dap_prot                   = grouped_params [1309];
parameter         p_edma_asf_prot_tsu                   = grouped_params [1308];
parameter         p_edma_has_br                         = grouped_params [1307];
parameter [31:0]  p_edma_emac_tx_pbuf_addr              = grouped_params [1306:1275];
parameter [31:0]  p_edma_emac_rx_pbuf_addr              = grouped_params [1274:1243];
parameter         p_edma_pcs_code_align                 = grouped_params [1242];
parameter         p_edma_using_rgmii                    = grouped_params [1241];
parameter         p_edma_include_rmii                   = grouped_params [1240];
parameter [31:0]  p_gem_rx_pipeline_delay               = grouped_params [1239:1208];
parameter [31:0]  p_edma_srd_width                      = grouped_params [1207:1176];
parameter         p_edma_has_pcs                        = grouped_params [1175];
parameter         p_edma_pcs_legacy_if                  = grouped_params [1174];
parameter [7:0]   p_gem_num_cb_streams                  = grouped_params [1173:1166];
parameter [7:0]   p_gem_cb_history_len                  = grouped_params [1165:1158];
parameter         p_gem_has_cb                          = grouped_params [1157];
parameter         p_edma_exclude_qbv                    = grouped_params [1156];
parameter [31:0]  p_edma_queues                         = grouped_params [1155:1124];
parameter [31:0]  p_edma_tx_pbuf_data                   = grouped_params [1123:1092];
parameter [31:0]  p_edma_rx_pbuf_data                   = grouped_params [1091:1060];
parameter [31:0]  p_edma_tx_pbuf_addr                   = grouped_params [1059:1028];
parameter [31:0]  p_edma_rx_pbuf_addr                   = grouped_params [1027:996];
parameter [31:0]  p_edma_tx_pbuf_queue_segment_size     = grouped_params [995:964];
parameter [31:0]  p_emac_bus_width                      = grouped_params [963:932];
parameter [31:0]  p_edma_bus_width                      = grouped_params [931:900];
parameter [31:0]  p_edma_addr_width                     = grouped_params [899:868];
parameter [31:0]  p_edma_rx_fifo_size                   = grouped_params [867:836];
parameter [31:0]  p_edma_tx_fifo_size                   = grouped_params [835:804];
parameter [31:0]  p_edma_rx_fifo_cnt_width              = grouped_params [803:772];
parameter [31:0]  p_edma_tx_fifo_cnt_width              = grouped_params [771:740];
parameter         p_xgm                                 = grouped_params [739];
parameter         p_edma_phy_ident                      = grouped_params [738];
parameter [31:0]  p_num_spec_add_filters                = grouped_params [737:706];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q0        = grouped_params [705:674];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q1        = grouped_params [673:642];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q2        = grouped_params [641:610];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q3        = grouped_params [609:578];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q4        = grouped_params [577:546];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q5        = grouped_params [545:514];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q6        = grouped_params [513:482];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q7        = grouped_params [481:450];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q8        = grouped_params [449:418];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q9        = grouped_params [417:386];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q10       = grouped_params [385:354];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q11       = grouped_params [353:322];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q12       = grouped_params [321:290];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q13       = grouped_params [289:258];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q14       = grouped_params [257:226];
parameter [31:0]  p_edma_tx_pbuf_num_segments_q15       = grouped_params [225:194];
parameter         p_edma_exclude_cbs                    = grouped_params [193];
parameter         p_edma_pbuf_cutthru                   = grouped_params [192];
parameter         p_edma_tsu                            = grouped_params [191];
parameter         p_edma_tsu_clk                        = grouped_params [190];
parameter         p_edma_ext_tsu_timer                  = grouped_params [189];
parameter         p_edma_axi                            = grouped_params [188];
parameter         p_edma_lso                            = grouped_params [187];
parameter         p_edma_rsc                            = grouped_params [186];
parameter         p_edma_spram                          = grouped_params [185];
parameter         p_edma_ext_fifo_interface             = grouped_params [184];
parameter         p_edma_add_rx_external_fifo_if        = grouped_params [183];
parameter         p_edma_add_tx_external_fifo_if        = grouped_params [182];
parameter         p_edma_host_if_soft_select            = grouped_params [181];
parameter         p_edma_pfc_multi_quantum              = grouped_params [180];
parameter         p_edma_rx_pkt_buffer                  = grouped_params [179];
parameter         p_edma_tx_pkt_buffer                  = grouped_params [178];
parameter         p_gem_user_io                         = grouped_params [177];
parameter [31:0]  p_gem_user_in_width                   = grouped_params [176:145];
parameter [31:0]  p_gem_user_out_width                  = grouped_params [144:113];
parameter         p_edma_irq_read_clear                 = grouped_params [112];
parameter         p_edma_no_snapshot                    = grouped_params [111];
parameter         p_edma_no_stats                       = grouped_params [110];
parameter         p_edma_no_pcs                         = grouped_params [109];
parameter         p_edma_int_loopback                   = grouped_params [108];
parameter         p_edma_tx_add_fifo_if                 = grouped_params [107];
parameter [3:0]   p_edma_rx_base2_fifo_size             = grouped_params [106:103];
parameter [3:0]   p_edma_tx_base2_fifo_size             = grouped_params [102:99];
parameter [3:0]   p_edma_axi_access_pipeline_bits       = grouped_params [98:95];
parameter [3:0]   p_edma_axi_tx_descr_rd_buff_bits      = grouped_params [94:91];
parameter [3:0]   p_edma_axi_rx_descr_rd_buff_bits      = grouped_params [90:87];
parameter [3:0]   p_edma_axi_tx_descr_wr_buff_bits      = grouped_params [86:83];
parameter [3:0]   p_edma_axi_rx_descr_wr_buff_bits      = grouped_params [82:79];
parameter [3:0]   p_edma_hprot_value                    = grouped_params [78:75];
parameter [2:0]   p_edma_axi_prot_value                 = grouped_params [74:72];
parameter [3:0]   p_edma_axi_arcache_value              = grouped_params [71:68];
parameter [3:0]   p_edma_axi_awcache_value              = grouped_params [67:64];
parameter [1:0]   p_edma_dma_bus_width_def              = grouped_params [63:62];
parameter [2:0]   p_edma_mdc_clock_div                  = grouped_params [61:59];
parameter [1:0]   p_edma_endian_swap_def                = grouped_params [58:57];
parameter [1:0]   p_edma_rx_pbuf_size_def               = grouped_params [56:55];
parameter         p_edma_tx_pbuf_size_def               = grouped_params [54];
parameter [7:0]   p_edma_rx_buffer_length_def           = grouped_params [53:46];
parameter [13:0]  p_edma_jumbo_max_length               = grouped_params [45:32];
parameter [7:0]   p_num_type1_screeners                 = grouped_params [31:24];
parameter [7:0]   p_num_type2_screeners                 = grouped_params [23:16];
parameter [7:0]   p_num_scr2_compare_regs               = grouped_params [15:8];
parameter [7:0]   p_num_scr2_ethtype_regs               = grouped_params [7:0];

// Parameters generated from above:
parameter p_emac_bus_pwid     = p_emac_bus_width/8;
parameter p_edma_bus_pwid     = p_edma_bus_width/8;
parameter p_edma_addr_pwid    = p_edma_addr_width/8;
parameter p_edma_rx_pbuf_pwid = p_edma_rx_pbuf_data/8;
parameter p_edma_tx_pbuf_pwid = p_edma_tx_pbuf_data/8;

parameter DEBUG = p_edma_queues[31:0];


generate for (m=0; m<p_edma_queues[31:0]; m=m+1)
   begin: gen_rx_q_flush_sync_rx_clk
     // Synchronising bit 0 of rx_q_flush_pclk in rx_clk domain
     cdnsdru_datasync_v1 i_rx_q_flush_bit0_rxclk(
       .clk    (rx_clk),
       .reset_n(n_rxreset),
       .din    (rx_q_flush_pclk[32*m]),
       .dout   (drop_all_frames_rx_clk[m])
     );

     // Synchronising bit 3 of rx_q_flush_pclk in rx_clk domain
     cdnsdru_datasync_v1 i_rx_q_flush_bit3_rxclk(
       .clk    (rx_clk),
       .reset_n(n_rxreset),
       .din    (rx_q_flush_pclk[(32*m)+3]),
       .dout   (limit_frames_size_rx_clk[m])
     );
     assign max_val_pclk [(15+(m*16)):(m*16)] = rx_q_flush_pclk [(32*m)+31:(32*m)+16]; // max_val is a static
   end
   endgenerate


   
endmodule
