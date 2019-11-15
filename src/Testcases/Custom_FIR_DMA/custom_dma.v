//megafunction wizard: %Altera SOPC Builder%
//GENERATION: STANDARD
//VERSION: WM1.0


//Legal Notice: (C)2010 Altera Corporation. All rights reserved.  Your
//use of Altera Corporation's design tools, logic functions and other
//software and tools, and its AMPP partner logic functions, and any
//output files any of the foregoing (including device programming or
//simulation files), and any associated documentation or information are
//expressly subject to the terms and conditions of the Altera Program
//License Subscription Agreement or other applicable license agreement,
//including, without limitation, that your use is for the sole purpose
//of programming logic devices manufactured by Altera and sold by Altera
//or its authorized distributors.  Please refer to the applicable
//agreement for further details.

// synthesis translate_off
`timescale 1ns / 1ps
// synthesis translate_on

// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module cpu_jtag_debug_module_arbitrator (
                                          // inputs:
                                           clk,
                                           cpu_jtag_debug_module_readdata,
                                           cpu_jtag_debug_module_resetrequest,
                                           pipeline_bridge_m1_address_to_slave,
                                           pipeline_bridge_m1_burstcount,
                                           pipeline_bridge_m1_byteenable,
                                           pipeline_bridge_m1_chipselect,
                                           pipeline_bridge_m1_debugaccess,
                                           pipeline_bridge_m1_latency_counter,
                                           pipeline_bridge_m1_read,
                                           pipeline_bridge_m1_write,
                                           pipeline_bridge_m1_writedata,
                                           reset_n,

                                          // outputs:
                                           cpu_jtag_debug_module_address,
                                           cpu_jtag_debug_module_begintransfer,
                                           cpu_jtag_debug_module_byteenable,
                                           cpu_jtag_debug_module_chipselect,
                                           cpu_jtag_debug_module_debugaccess,
                                           cpu_jtag_debug_module_readdata_from_sa,
                                           cpu_jtag_debug_module_reset_n,
                                           cpu_jtag_debug_module_resetrequest_from_sa,
                                           cpu_jtag_debug_module_write,
                                           cpu_jtag_debug_module_writedata,
                                           d1_cpu_jtag_debug_module_end_xfer,
                                           pipeline_bridge_m1_granted_cpu_jtag_debug_module,
                                           pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module,
                                           pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module,
                                           pipeline_bridge_m1_requests_cpu_jtag_debug_module
                                        )
;

  output  [  8: 0] cpu_jtag_debug_module_address;
  output           cpu_jtag_debug_module_begintransfer;
  output  [  3: 0] cpu_jtag_debug_module_byteenable;
  output           cpu_jtag_debug_module_chipselect;
  output           cpu_jtag_debug_module_debugaccess;
  output  [ 31: 0] cpu_jtag_debug_module_readdata_from_sa;
  output           cpu_jtag_debug_module_reset_n;
  output           cpu_jtag_debug_module_resetrequest_from_sa;
  output           cpu_jtag_debug_module_write;
  output  [ 31: 0] cpu_jtag_debug_module_writedata;
  output           d1_cpu_jtag_debug_module_end_xfer;
  output           pipeline_bridge_m1_granted_cpu_jtag_debug_module;
  output           pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module;
  output           pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module;
  output           pipeline_bridge_m1_requests_cpu_jtag_debug_module;
  input            clk;
  input   [ 31: 0] cpu_jtag_debug_module_readdata;
  input            cpu_jtag_debug_module_resetrequest;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input   [  3: 0] pipeline_bridge_m1_byteenable;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_debugaccess;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;

  wire    [  8: 0] cpu_jtag_debug_module_address;
  wire             cpu_jtag_debug_module_allgrants;
  wire             cpu_jtag_debug_module_allow_new_arb_cycle;
  wire             cpu_jtag_debug_module_any_bursting_master_saved_grant;
  wire             cpu_jtag_debug_module_any_continuerequest;
  wire             cpu_jtag_debug_module_arb_counter_enable;
  reg              cpu_jtag_debug_module_arb_share_counter;
  wire             cpu_jtag_debug_module_arb_share_counter_next_value;
  wire             cpu_jtag_debug_module_arb_share_set_values;
  wire             cpu_jtag_debug_module_beginbursttransfer_internal;
  wire             cpu_jtag_debug_module_begins_xfer;
  wire             cpu_jtag_debug_module_begintransfer;
  wire    [  3: 0] cpu_jtag_debug_module_byteenable;
  wire             cpu_jtag_debug_module_chipselect;
  wire             cpu_jtag_debug_module_debugaccess;
  wire             cpu_jtag_debug_module_end_xfer;
  wire             cpu_jtag_debug_module_firsttransfer;
  wire             cpu_jtag_debug_module_grant_vector;
  wire             cpu_jtag_debug_module_in_a_read_cycle;
  wire             cpu_jtag_debug_module_in_a_write_cycle;
  wire             cpu_jtag_debug_module_master_qreq_vector;
  wire             cpu_jtag_debug_module_non_bursting_master_requests;
  wire    [ 31: 0] cpu_jtag_debug_module_readdata_from_sa;
  reg              cpu_jtag_debug_module_reg_firsttransfer;
  wire             cpu_jtag_debug_module_reset_n;
  wire             cpu_jtag_debug_module_resetrequest_from_sa;
  reg              cpu_jtag_debug_module_slavearbiterlockenable;
  wire             cpu_jtag_debug_module_slavearbiterlockenable2;
  wire             cpu_jtag_debug_module_unreg_firsttransfer;
  wire             cpu_jtag_debug_module_waits_for_read;
  wire             cpu_jtag_debug_module_waits_for_write;
  wire             cpu_jtag_debug_module_write;
  wire    [ 31: 0] cpu_jtag_debug_module_writedata;
  reg              d1_cpu_jtag_debug_module_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_cpu_jtag_debug_module;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_requests_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_saved_grant_cpu_jtag_debug_module;
  wire    [ 11: 0] shifted_address_to_cpu_jtag_debug_module_from_pipeline_bridge_m1;
  wire             wait_for_cpu_jtag_debug_module_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~cpu_jtag_debug_module_end_xfer;
    end


  assign cpu_jtag_debug_module_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module));
  //assign cpu_jtag_debug_module_readdata_from_sa = cpu_jtag_debug_module_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign cpu_jtag_debug_module_readdata_from_sa = cpu_jtag_debug_module_readdata;

  assign pipeline_bridge_m1_requests_cpu_jtag_debug_module = ({pipeline_bridge_m1_address_to_slave[11] , 11'b0} == 12'h0) & pipeline_bridge_m1_chipselect;
  //cpu_jtag_debug_module_arb_share_counter set values, which is an e_mux
  assign cpu_jtag_debug_module_arb_share_set_values = 1;

  //cpu_jtag_debug_module_non_bursting_master_requests mux, which is an e_mux
  assign cpu_jtag_debug_module_non_bursting_master_requests = pipeline_bridge_m1_requests_cpu_jtag_debug_module;

  //cpu_jtag_debug_module_any_bursting_master_saved_grant mux, which is an e_mux
  assign cpu_jtag_debug_module_any_bursting_master_saved_grant = 0;

  //cpu_jtag_debug_module_arb_share_counter_next_value assignment, which is an e_assign
  assign cpu_jtag_debug_module_arb_share_counter_next_value = cpu_jtag_debug_module_firsttransfer ? (cpu_jtag_debug_module_arb_share_set_values - 1) : |cpu_jtag_debug_module_arb_share_counter ? (cpu_jtag_debug_module_arb_share_counter - 1) : 0;

  //cpu_jtag_debug_module_allgrants all slave grants, which is an e_mux
  assign cpu_jtag_debug_module_allgrants = |cpu_jtag_debug_module_grant_vector;

  //cpu_jtag_debug_module_end_xfer assignment, which is an e_assign
  assign cpu_jtag_debug_module_end_xfer = ~(cpu_jtag_debug_module_waits_for_read | cpu_jtag_debug_module_waits_for_write);

  //end_xfer_arb_share_counter_term_cpu_jtag_debug_module arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_cpu_jtag_debug_module = cpu_jtag_debug_module_end_xfer & (~cpu_jtag_debug_module_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //cpu_jtag_debug_module_arb_share_counter arbitration counter enable, which is an e_assign
  assign cpu_jtag_debug_module_arb_counter_enable = (end_xfer_arb_share_counter_term_cpu_jtag_debug_module & cpu_jtag_debug_module_allgrants) | (end_xfer_arb_share_counter_term_cpu_jtag_debug_module & ~cpu_jtag_debug_module_non_bursting_master_requests);

  //cpu_jtag_debug_module_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_jtag_debug_module_arb_share_counter <= 0;
      else if (cpu_jtag_debug_module_arb_counter_enable)
          cpu_jtag_debug_module_arb_share_counter <= cpu_jtag_debug_module_arb_share_counter_next_value;
    end


  //cpu_jtag_debug_module_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_jtag_debug_module_slavearbiterlockenable <= 0;
      else if ((|cpu_jtag_debug_module_master_qreq_vector & end_xfer_arb_share_counter_term_cpu_jtag_debug_module) | (end_xfer_arb_share_counter_term_cpu_jtag_debug_module & ~cpu_jtag_debug_module_non_bursting_master_requests))
          cpu_jtag_debug_module_slavearbiterlockenable <= |cpu_jtag_debug_module_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 cpu/jtag_debug_module arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = cpu_jtag_debug_module_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //cpu_jtag_debug_module_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign cpu_jtag_debug_module_slavearbiterlockenable2 = |cpu_jtag_debug_module_arb_share_counter_next_value;

  //pipeline_bridge/m1 cpu/jtag_debug_module arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = cpu_jtag_debug_module_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //cpu_jtag_debug_module_any_continuerequest at least one master continues requesting, which is an e_assign
  assign cpu_jtag_debug_module_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module = pipeline_bridge_m1_requests_cpu_jtag_debug_module & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((pipeline_bridge_m1_latency_counter != 0))));
  //local readdatavalid pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module = pipeline_bridge_m1_granted_cpu_jtag_debug_module & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~cpu_jtag_debug_module_waits_for_read;

  //cpu_jtag_debug_module_writedata mux, which is an e_mux
  assign cpu_jtag_debug_module_writedata = pipeline_bridge_m1_writedata;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_cpu_jtag_debug_module = pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module;

  //pipeline_bridge/m1 saved-grant cpu/jtag_debug_module, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_cpu_jtag_debug_module = pipeline_bridge_m1_requests_cpu_jtag_debug_module;

  //allow new arb cycle for cpu/jtag_debug_module, which is an e_assign
  assign cpu_jtag_debug_module_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign cpu_jtag_debug_module_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign cpu_jtag_debug_module_master_qreq_vector = 1;

  assign cpu_jtag_debug_module_begintransfer = cpu_jtag_debug_module_begins_xfer;
  //cpu_jtag_debug_module_reset_n assignment, which is an e_assign
  assign cpu_jtag_debug_module_reset_n = reset_n;

  //assign cpu_jtag_debug_module_resetrequest_from_sa = cpu_jtag_debug_module_resetrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign cpu_jtag_debug_module_resetrequest_from_sa = cpu_jtag_debug_module_resetrequest;

  assign cpu_jtag_debug_module_chipselect = pipeline_bridge_m1_granted_cpu_jtag_debug_module;
  //cpu_jtag_debug_module_firsttransfer first transaction, which is an e_assign
  assign cpu_jtag_debug_module_firsttransfer = cpu_jtag_debug_module_begins_xfer ? cpu_jtag_debug_module_unreg_firsttransfer : cpu_jtag_debug_module_reg_firsttransfer;

  //cpu_jtag_debug_module_unreg_firsttransfer first transaction, which is an e_assign
  assign cpu_jtag_debug_module_unreg_firsttransfer = ~(cpu_jtag_debug_module_slavearbiterlockenable & cpu_jtag_debug_module_any_continuerequest);

  //cpu_jtag_debug_module_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_jtag_debug_module_reg_firsttransfer <= 1'b1;
      else if (cpu_jtag_debug_module_begins_xfer)
          cpu_jtag_debug_module_reg_firsttransfer <= cpu_jtag_debug_module_unreg_firsttransfer;
    end


  //cpu_jtag_debug_module_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign cpu_jtag_debug_module_beginbursttransfer_internal = cpu_jtag_debug_module_begins_xfer;

  //cpu_jtag_debug_module_write assignment, which is an e_mux
  assign cpu_jtag_debug_module_write = pipeline_bridge_m1_granted_cpu_jtag_debug_module & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  assign shifted_address_to_cpu_jtag_debug_module_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //cpu_jtag_debug_module_address mux, which is an e_mux
  assign cpu_jtag_debug_module_address = shifted_address_to_cpu_jtag_debug_module_from_pipeline_bridge_m1 >> 2;

  //d1_cpu_jtag_debug_module_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_cpu_jtag_debug_module_end_xfer <= 1;
      else 
        d1_cpu_jtag_debug_module_end_xfer <= cpu_jtag_debug_module_end_xfer;
    end


  //cpu_jtag_debug_module_waits_for_read in a cycle, which is an e_mux
  assign cpu_jtag_debug_module_waits_for_read = cpu_jtag_debug_module_in_a_read_cycle & cpu_jtag_debug_module_begins_xfer;

  //cpu_jtag_debug_module_in_a_read_cycle assignment, which is an e_assign
  assign cpu_jtag_debug_module_in_a_read_cycle = pipeline_bridge_m1_granted_cpu_jtag_debug_module & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = cpu_jtag_debug_module_in_a_read_cycle;

  //cpu_jtag_debug_module_waits_for_write in a cycle, which is an e_mux
  assign cpu_jtag_debug_module_waits_for_write = cpu_jtag_debug_module_in_a_write_cycle & 0;

  //cpu_jtag_debug_module_in_a_write_cycle assignment, which is an e_assign
  assign cpu_jtag_debug_module_in_a_write_cycle = pipeline_bridge_m1_granted_cpu_jtag_debug_module & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = cpu_jtag_debug_module_in_a_write_cycle;

  assign wait_for_cpu_jtag_debug_module_counter = 0;
  //cpu_jtag_debug_module_byteenable byte enable port mux, which is an e_mux
  assign cpu_jtag_debug_module_byteenable = (pipeline_bridge_m1_granted_cpu_jtag_debug_module)? pipeline_bridge_m1_byteenable :
    -1;

  //debugaccess mux, which is an e_mux
  assign cpu_jtag_debug_module_debugaccess = (pipeline_bridge_m1_granted_cpu_jtag_debug_module)? pipeline_bridge_m1_debugaccess :
    0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //cpu/jtag_debug_module enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_cpu_jtag_debug_module && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave cpu/jtag_debug_module", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module cpu_data_master_arbitrator (
                                    // inputs:
                                     clk,
                                     cpu_data_master_address,
                                     cpu_data_master_burstcount,
                                     cpu_data_master_byteenable,
                                     cpu_data_master_granted_custom_dma_burst_0_upstream,
                                     cpu_data_master_granted_custom_dma_burst_2_upstream,
                                     cpu_data_master_granted_custom_dma_burst_4_upstream,
                                     cpu_data_master_qualified_request_custom_dma_burst_0_upstream,
                                     cpu_data_master_qualified_request_custom_dma_burst_2_upstream,
                                     cpu_data_master_qualified_request_custom_dma_burst_4_upstream,
                                     cpu_data_master_read,
                                     cpu_data_master_read_data_valid_custom_dma_burst_0_upstream,
                                     cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register,
                                     cpu_data_master_read_data_valid_custom_dma_burst_2_upstream,
                                     cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register,
                                     cpu_data_master_read_data_valid_custom_dma_burst_4_upstream,
                                     cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register,
                                     cpu_data_master_requests_custom_dma_burst_0_upstream,
                                     cpu_data_master_requests_custom_dma_burst_2_upstream,
                                     cpu_data_master_requests_custom_dma_burst_4_upstream,
                                     cpu_data_master_write,
                                     cpu_data_master_writedata,
                                     custom_dma_burst_0_upstream_readdata_from_sa,
                                     custom_dma_burst_0_upstream_waitrequest_from_sa,
                                     custom_dma_burst_2_upstream_readdata_from_sa,
                                     custom_dma_burst_2_upstream_waitrequest_from_sa,
                                     custom_dma_burst_4_upstream_readdata_from_sa,
                                     custom_dma_burst_4_upstream_waitrequest_from_sa,
                                     d1_custom_dma_burst_0_upstream_end_xfer,
                                     d1_custom_dma_burst_2_upstream_end_xfer,
                                     d1_custom_dma_burst_4_upstream_end_xfer,
                                     fir_dma_control_irq_from_sa,
                                     jtag_uart_avalon_jtag_slave_irq_from_sa,
                                     reset_n,
                                     timestamp_timer_s1_irq_from_sa,

                                    // outputs:
                                     cpu_data_master_address_to_slave,
                                     cpu_data_master_irq,
                                     cpu_data_master_latency_counter,
                                     cpu_data_master_readdata,
                                     cpu_data_master_readdatavalid,
                                     cpu_data_master_waitrequest
                                  )
;

  output  [ 26: 0] cpu_data_master_address_to_slave;
  output  [ 31: 0] cpu_data_master_irq;
  output           cpu_data_master_latency_counter;
  output  [ 31: 0] cpu_data_master_readdata;
  output           cpu_data_master_readdatavalid;
  output           cpu_data_master_waitrequest;
  input            clk;
  input   [ 26: 0] cpu_data_master_address;
  input   [  3: 0] cpu_data_master_burstcount;
  input   [  3: 0] cpu_data_master_byteenable;
  input            cpu_data_master_granted_custom_dma_burst_0_upstream;
  input            cpu_data_master_granted_custom_dma_burst_2_upstream;
  input            cpu_data_master_granted_custom_dma_burst_4_upstream;
  input            cpu_data_master_qualified_request_custom_dma_burst_0_upstream;
  input            cpu_data_master_qualified_request_custom_dma_burst_2_upstream;
  input            cpu_data_master_qualified_request_custom_dma_burst_4_upstream;
  input            cpu_data_master_read;
  input            cpu_data_master_read_data_valid_custom_dma_burst_0_upstream;
  input            cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  input            cpu_data_master_read_data_valid_custom_dma_burst_2_upstream;
  input            cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  input            cpu_data_master_read_data_valid_custom_dma_burst_4_upstream;
  input            cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  input            cpu_data_master_requests_custom_dma_burst_0_upstream;
  input            cpu_data_master_requests_custom_dma_burst_2_upstream;
  input            cpu_data_master_requests_custom_dma_burst_4_upstream;
  input            cpu_data_master_write;
  input   [ 31: 0] cpu_data_master_writedata;
  input   [ 31: 0] custom_dma_burst_0_upstream_readdata_from_sa;
  input            custom_dma_burst_0_upstream_waitrequest_from_sa;
  input   [ 31: 0] custom_dma_burst_2_upstream_readdata_from_sa;
  input            custom_dma_burst_2_upstream_waitrequest_from_sa;
  input   [ 31: 0] custom_dma_burst_4_upstream_readdata_from_sa;
  input            custom_dma_burst_4_upstream_waitrequest_from_sa;
  input            d1_custom_dma_burst_0_upstream_end_xfer;
  input            d1_custom_dma_burst_2_upstream_end_xfer;
  input            d1_custom_dma_burst_4_upstream_end_xfer;
  input            fir_dma_control_irq_from_sa;
  input            jtag_uart_avalon_jtag_slave_irq_from_sa;
  input            reset_n;
  input            timestamp_timer_s1_irq_from_sa;

  reg              active_and_waiting_last_time;
  reg     [ 26: 0] cpu_data_master_address_last_time;
  wire    [ 26: 0] cpu_data_master_address_to_slave;
  reg     [  3: 0] cpu_data_master_burstcount_last_time;
  reg     [  3: 0] cpu_data_master_byteenable_last_time;
  wire    [ 31: 0] cpu_data_master_irq;
  wire             cpu_data_master_is_granted_some_slave;
  reg              cpu_data_master_latency_counter;
  reg              cpu_data_master_read_but_no_slave_selected;
  reg              cpu_data_master_read_last_time;
  wire    [ 31: 0] cpu_data_master_readdata;
  wire             cpu_data_master_readdatavalid;
  wire             cpu_data_master_run;
  wire             cpu_data_master_waitrequest;
  reg              cpu_data_master_write_last_time;
  reg     [ 31: 0] cpu_data_master_writedata_last_time;
  wire             latency_load_value;
  wire             p1_cpu_data_master_latency_counter;
  wire             pre_flush_cpu_data_master_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (cpu_data_master_qualified_request_custom_dma_burst_0_upstream | ~cpu_data_master_requests_custom_dma_burst_0_upstream) & ((~cpu_data_master_qualified_request_custom_dma_burst_0_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_0_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write)))) & ((~cpu_data_master_qualified_request_custom_dma_burst_0_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_0_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write)))) & 1 & (cpu_data_master_qualified_request_custom_dma_burst_2_upstream | ~cpu_data_master_requests_custom_dma_burst_2_upstream) & ((~cpu_data_master_qualified_request_custom_dma_burst_2_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_2_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write)))) & ((~cpu_data_master_qualified_request_custom_dma_burst_2_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_2_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write)))) & 1 & (cpu_data_master_qualified_request_custom_dma_burst_4_upstream | ~cpu_data_master_requests_custom_dma_burst_4_upstream) & ((~cpu_data_master_qualified_request_custom_dma_burst_4_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_4_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write)))) & ((~cpu_data_master_qualified_request_custom_dma_burst_4_upstream | ~(cpu_data_master_read | cpu_data_master_write) | (1 & ~custom_dma_burst_4_upstream_waitrequest_from_sa & (cpu_data_master_read | cpu_data_master_write))));

  //cascaded wait assignment, which is an e_assign
  assign cpu_data_master_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign cpu_data_master_address_to_slave = cpu_data_master_address[26 : 0];

  //cpu_data_master_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_read_but_no_slave_selected <= 0;
      else 
        cpu_data_master_read_but_no_slave_selected <= cpu_data_master_read & cpu_data_master_run & ~cpu_data_master_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign cpu_data_master_is_granted_some_slave = cpu_data_master_granted_custom_dma_burst_0_upstream |
    cpu_data_master_granted_custom_dma_burst_2_upstream |
    cpu_data_master_granted_custom_dma_burst_4_upstream;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_cpu_data_master_readdatavalid = cpu_data_master_read_data_valid_custom_dma_burst_0_upstream |
    cpu_data_master_read_data_valid_custom_dma_burst_2_upstream |
    cpu_data_master_read_data_valid_custom_dma_burst_4_upstream;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign cpu_data_master_readdatavalid = cpu_data_master_read_but_no_slave_selected |
    pre_flush_cpu_data_master_readdatavalid |
    cpu_data_master_read_but_no_slave_selected |
    pre_flush_cpu_data_master_readdatavalid |
    cpu_data_master_read_but_no_slave_selected |
    pre_flush_cpu_data_master_readdatavalid;

  //cpu/data_master readdata mux, which is an e_mux
  assign cpu_data_master_readdata = ({32 {~cpu_data_master_read_data_valid_custom_dma_burst_0_upstream}} | custom_dma_burst_0_upstream_readdata_from_sa) &
    ({32 {~cpu_data_master_read_data_valid_custom_dma_burst_2_upstream}} | custom_dma_burst_2_upstream_readdata_from_sa) &
    ({32 {~cpu_data_master_read_data_valid_custom_dma_burst_4_upstream}} | custom_dma_burst_4_upstream_readdata_from_sa);

  //actual waitrequest port, which is an e_assign
  assign cpu_data_master_waitrequest = ~cpu_data_master_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_latency_counter <= 0;
      else 
        cpu_data_master_latency_counter <= p1_cpu_data_master_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_cpu_data_master_latency_counter = ((cpu_data_master_run & cpu_data_master_read))? latency_load_value :
    (cpu_data_master_latency_counter)? cpu_data_master_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //irq assign, which is an e_assign
  assign cpu_data_master_irq = {1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    1'b0,
    fir_dma_control_irq_from_sa,
    jtag_uart_avalon_jtag_slave_irq_from_sa,
    timestamp_timer_s1_irq_from_sa};


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //cpu_data_master_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_address_last_time <= 0;
      else 
        cpu_data_master_address_last_time <= cpu_data_master_address;
    end


  //cpu/data_master waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= cpu_data_master_waitrequest & (cpu_data_master_read | cpu_data_master_write);
    end


  //cpu_data_master_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_address != cpu_data_master_address_last_time))
        begin
          $write("%0d ns: cpu_data_master_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_data_master_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_burstcount_last_time <= 0;
      else 
        cpu_data_master_burstcount_last_time <= cpu_data_master_burstcount;
    end


  //cpu_data_master_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_burstcount != cpu_data_master_burstcount_last_time))
        begin
          $write("%0d ns: cpu_data_master_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_data_master_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_byteenable_last_time <= 0;
      else 
        cpu_data_master_byteenable_last_time <= cpu_data_master_byteenable;
    end


  //cpu_data_master_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_byteenable != cpu_data_master_byteenable_last_time))
        begin
          $write("%0d ns: cpu_data_master_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_data_master_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_read_last_time <= 0;
      else 
        cpu_data_master_read_last_time <= cpu_data_master_read;
    end


  //cpu_data_master_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_read != cpu_data_master_read_last_time))
        begin
          $write("%0d ns: cpu_data_master_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_data_master_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_write_last_time <= 0;
      else 
        cpu_data_master_write_last_time <= cpu_data_master_write;
    end


  //cpu_data_master_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_write != cpu_data_master_write_last_time))
        begin
          $write("%0d ns: cpu_data_master_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_data_master_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_data_master_writedata_last_time <= 0;
      else 
        cpu_data_master_writedata_last_time <= cpu_data_master_writedata;
    end


  //cpu_data_master_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_data_master_writedata != cpu_data_master_writedata_last_time) & cpu_data_master_write)
        begin
          $write("%0d ns: cpu_data_master_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module cpu_instruction_master_arbitrator (
                                           // inputs:
                                            clk,
                                            cpu_instruction_master_address,
                                            cpu_instruction_master_burstcount,
                                            cpu_instruction_master_granted_custom_dma_burst_1_upstream,
                                            cpu_instruction_master_granted_custom_dma_burst_3_upstream,
                                            cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream,
                                            cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream,
                                            cpu_instruction_master_read,
                                            cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream,
                                            cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register,
                                            cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream,
                                            cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register,
                                            cpu_instruction_master_requests_custom_dma_burst_1_upstream,
                                            cpu_instruction_master_requests_custom_dma_burst_3_upstream,
                                            custom_dma_burst_1_upstream_readdata_from_sa,
                                            custom_dma_burst_1_upstream_waitrequest_from_sa,
                                            custom_dma_burst_3_upstream_readdata_from_sa,
                                            custom_dma_burst_3_upstream_waitrequest_from_sa,
                                            d1_custom_dma_burst_1_upstream_end_xfer,
                                            d1_custom_dma_burst_3_upstream_end_xfer,
                                            reset_n,

                                           // outputs:
                                            cpu_instruction_master_address_to_slave,
                                            cpu_instruction_master_latency_counter,
                                            cpu_instruction_master_readdata,
                                            cpu_instruction_master_readdatavalid,
                                            cpu_instruction_master_waitrequest
                                         )
;

  output  [ 26: 0] cpu_instruction_master_address_to_slave;
  output           cpu_instruction_master_latency_counter;
  output  [ 31: 0] cpu_instruction_master_readdata;
  output           cpu_instruction_master_readdatavalid;
  output           cpu_instruction_master_waitrequest;
  input            clk;
  input   [ 26: 0] cpu_instruction_master_address;
  input   [  3: 0] cpu_instruction_master_burstcount;
  input            cpu_instruction_master_granted_custom_dma_burst_1_upstream;
  input            cpu_instruction_master_granted_custom_dma_burst_3_upstream;
  input            cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream;
  input            cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream;
  input            cpu_instruction_master_read;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register;
  input            cpu_instruction_master_requests_custom_dma_burst_1_upstream;
  input            cpu_instruction_master_requests_custom_dma_burst_3_upstream;
  input   [ 31: 0] custom_dma_burst_1_upstream_readdata_from_sa;
  input            custom_dma_burst_1_upstream_waitrequest_from_sa;
  input   [ 31: 0] custom_dma_burst_3_upstream_readdata_from_sa;
  input            custom_dma_burst_3_upstream_waitrequest_from_sa;
  input            d1_custom_dma_burst_1_upstream_end_xfer;
  input            d1_custom_dma_burst_3_upstream_end_xfer;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 26: 0] cpu_instruction_master_address_last_time;
  wire    [ 26: 0] cpu_instruction_master_address_to_slave;
  reg     [  3: 0] cpu_instruction_master_burstcount_last_time;
  wire             cpu_instruction_master_is_granted_some_slave;
  reg              cpu_instruction_master_latency_counter;
  reg              cpu_instruction_master_read_but_no_slave_selected;
  reg              cpu_instruction_master_read_last_time;
  wire    [ 31: 0] cpu_instruction_master_readdata;
  wire             cpu_instruction_master_readdatavalid;
  wire             cpu_instruction_master_run;
  wire             cpu_instruction_master_waitrequest;
  wire             latency_load_value;
  wire             p1_cpu_instruction_master_latency_counter;
  wire             pre_flush_cpu_instruction_master_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream | ~cpu_instruction_master_requests_custom_dma_burst_1_upstream) & ((~cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream | ~(cpu_instruction_master_read) | (1 & ~custom_dma_burst_1_upstream_waitrequest_from_sa & (cpu_instruction_master_read)))) & 1 & (cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream | ~cpu_instruction_master_requests_custom_dma_burst_3_upstream) & ((~cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream | ~(cpu_instruction_master_read) | (1 & ~custom_dma_burst_3_upstream_waitrequest_from_sa & (cpu_instruction_master_read))));

  //cascaded wait assignment, which is an e_assign
  assign cpu_instruction_master_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign cpu_instruction_master_address_to_slave = cpu_instruction_master_address[26 : 0];

  //cpu_instruction_master_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_instruction_master_read_but_no_slave_selected <= 0;
      else 
        cpu_instruction_master_read_but_no_slave_selected <= cpu_instruction_master_read & cpu_instruction_master_run & ~cpu_instruction_master_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign cpu_instruction_master_is_granted_some_slave = cpu_instruction_master_granted_custom_dma_burst_1_upstream |
    cpu_instruction_master_granted_custom_dma_burst_3_upstream;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_cpu_instruction_master_readdatavalid = cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream |
    cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign cpu_instruction_master_readdatavalid = cpu_instruction_master_read_but_no_slave_selected |
    pre_flush_cpu_instruction_master_readdatavalid |
    cpu_instruction_master_read_but_no_slave_selected |
    pre_flush_cpu_instruction_master_readdatavalid;

  //cpu/instruction_master readdata mux, which is an e_mux
  assign cpu_instruction_master_readdata = ({32 {~cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream}} | custom_dma_burst_1_upstream_readdata_from_sa) &
    ({32 {~cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream}} | custom_dma_burst_3_upstream_readdata_from_sa);

  //actual waitrequest port, which is an e_assign
  assign cpu_instruction_master_waitrequest = ~cpu_instruction_master_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_instruction_master_latency_counter <= 0;
      else 
        cpu_instruction_master_latency_counter <= p1_cpu_instruction_master_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_cpu_instruction_master_latency_counter = ((cpu_instruction_master_run & cpu_instruction_master_read))? latency_load_value :
    (cpu_instruction_master_latency_counter)? cpu_instruction_master_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //cpu_instruction_master_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_instruction_master_address_last_time <= 0;
      else 
        cpu_instruction_master_address_last_time <= cpu_instruction_master_address;
    end


  //cpu/instruction_master waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= cpu_instruction_master_waitrequest & (cpu_instruction_master_read);
    end


  //cpu_instruction_master_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_instruction_master_address != cpu_instruction_master_address_last_time))
        begin
          $write("%0d ns: cpu_instruction_master_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_instruction_master_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_instruction_master_burstcount_last_time <= 0;
      else 
        cpu_instruction_master_burstcount_last_time <= cpu_instruction_master_burstcount;
    end


  //cpu_instruction_master_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_instruction_master_burstcount != cpu_instruction_master_burstcount_last_time))
        begin
          $write("%0d ns: cpu_instruction_master_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //cpu_instruction_master_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          cpu_instruction_master_read_last_time <= 0;
      else 
        cpu_instruction_master_read_last_time <= cpu_instruction_master_read;
    end


  //cpu_instruction_master_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (cpu_instruction_master_read != cpu_instruction_master_read_last_time))
        begin
          $write("%0d ns: cpu_instruction_master_read did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_custom_dma_burst_0_upstream_module (
                                                                // inputs:
                                                                 clear_fifo,
                                                                 clk,
                                                                 data_in,
                                                                 read,
                                                                 reset_n,
                                                                 sync_reset,
                                                                 write,

                                                                // outputs:
                                                                 data_out,
                                                                 empty,
                                                                 fifo_contains_ones_n,
                                                                 full
                                                              )
;

  output  [  3: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  3: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  3: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  3: 0] p0_stage_0;
  wire             p1_full_1;
  wire    [  3: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  3: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  3: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  3: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  3: 0] p5_stage_5;
  reg     [  3: 0] stage_0;
  reg     [  3: 0] stage_1;
  reg     [  3: 0] stage_2;
  reg     [  3: 0] stage_3;
  reg     [  3: 0] stage_4;
  reg     [  3: 0] stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_0_upstream_module (
                                                                            // inputs:
                                                                             clear_fifo,
                                                                             clk,
                                                                             data_in,
                                                                             read,
                                                                             reset_n,
                                                                             sync_reset,
                                                                             write,

                                                                            // outputs:
                                                                             data_out,
                                                                             empty,
                                                                             fifo_contains_ones_n,
                                                                             full
                                                                          )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  reg              stage_0;
  reg              stage_1;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_0_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 cpu_data_master_address_to_slave,
                                                 cpu_data_master_burstcount,
                                                 cpu_data_master_byteenable,
                                                 cpu_data_master_debugaccess,
                                                 cpu_data_master_latency_counter,
                                                 cpu_data_master_read,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register,
                                                 cpu_data_master_write,
                                                 cpu_data_master_writedata,
                                                 custom_dma_burst_0_upstream_readdata,
                                                 custom_dma_burst_0_upstream_readdatavalid,
                                                 custom_dma_burst_0_upstream_waitrequest,
                                                 reset_n,

                                                // outputs:
                                                 cpu_data_master_granted_custom_dma_burst_0_upstream,
                                                 cpu_data_master_qualified_request_custom_dma_burst_0_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_0_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register,
                                                 cpu_data_master_requests_custom_dma_burst_0_upstream,
                                                 custom_dma_burst_0_upstream_address,
                                                 custom_dma_burst_0_upstream_burstcount,
                                                 custom_dma_burst_0_upstream_byteaddress,
                                                 custom_dma_burst_0_upstream_byteenable,
                                                 custom_dma_burst_0_upstream_debugaccess,
                                                 custom_dma_burst_0_upstream_read,
                                                 custom_dma_burst_0_upstream_readdata_from_sa,
                                                 custom_dma_burst_0_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_0_upstream_write,
                                                 custom_dma_burst_0_upstream_writedata,
                                                 d1_custom_dma_burst_0_upstream_end_xfer
                                              )
;

  output           cpu_data_master_granted_custom_dma_burst_0_upstream;
  output           cpu_data_master_qualified_request_custom_dma_burst_0_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_0_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  output           cpu_data_master_requests_custom_dma_burst_0_upstream;
  output  [ 20: 0] custom_dma_burst_0_upstream_address;
  output  [  3: 0] custom_dma_burst_0_upstream_burstcount;
  output  [ 22: 0] custom_dma_burst_0_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_0_upstream_byteenable;
  output           custom_dma_burst_0_upstream_debugaccess;
  output           custom_dma_burst_0_upstream_read;
  output  [ 31: 0] custom_dma_burst_0_upstream_readdata_from_sa;
  output           custom_dma_burst_0_upstream_waitrequest_from_sa;
  output           custom_dma_burst_0_upstream_write;
  output  [ 31: 0] custom_dma_burst_0_upstream_writedata;
  output           d1_custom_dma_burst_0_upstream_end_xfer;
  input            clk;
  input   [ 26: 0] cpu_data_master_address_to_slave;
  input   [  3: 0] cpu_data_master_burstcount;
  input   [  3: 0] cpu_data_master_byteenable;
  input            cpu_data_master_debugaccess;
  input            cpu_data_master_latency_counter;
  input            cpu_data_master_read;
  input            cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  input            cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  input            cpu_data_master_write;
  input   [ 31: 0] cpu_data_master_writedata;
  input   [ 31: 0] custom_dma_burst_0_upstream_readdata;
  input            custom_dma_burst_0_upstream_readdatavalid;
  input            custom_dma_burst_0_upstream_waitrequest;
  input            reset_n;

  wire             cpu_data_master_arbiterlock;
  wire             cpu_data_master_arbiterlock2;
  wire             cpu_data_master_continuerequest;
  wire             cpu_data_master_granted_custom_dma_burst_0_upstream;
  wire             cpu_data_master_qualified_request_custom_dma_burst_0_upstream;
  wire             cpu_data_master_rdv_fifo_empty_custom_dma_burst_0_upstream;
  wire             cpu_data_master_rdv_fifo_output_from_custom_dma_burst_0_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_0_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  wire             cpu_data_master_requests_custom_dma_burst_0_upstream;
  wire             cpu_data_master_saved_grant_custom_dma_burst_0_upstream;
  wire    [ 20: 0] custom_dma_burst_0_upstream_address;
  wire             custom_dma_burst_0_upstream_allgrants;
  wire             custom_dma_burst_0_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_0_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_0_upstream_any_continuerequest;
  wire             custom_dma_burst_0_upstream_arb_counter_enable;
  reg     [  3: 0] custom_dma_burst_0_upstream_arb_share_counter;
  wire    [  3: 0] custom_dma_burst_0_upstream_arb_share_counter_next_value;
  wire    [  3: 0] custom_dma_burst_0_upstream_arb_share_set_values;
  reg     [  2: 0] custom_dma_burst_0_upstream_bbt_burstcounter;
  wire             custom_dma_burst_0_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_0_upstream_begins_xfer;
  wire    [  3: 0] custom_dma_burst_0_upstream_burstcount;
  wire             custom_dma_burst_0_upstream_burstcount_fifo_empty;
  wire    [ 22: 0] custom_dma_burst_0_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_0_upstream_byteenable;
  reg     [  3: 0] custom_dma_burst_0_upstream_current_burst;
  wire    [  3: 0] custom_dma_burst_0_upstream_current_burst_minus_one;
  wire             custom_dma_burst_0_upstream_debugaccess;
  wire             custom_dma_burst_0_upstream_end_xfer;
  wire             custom_dma_burst_0_upstream_firsttransfer;
  wire             custom_dma_burst_0_upstream_grant_vector;
  wire             custom_dma_burst_0_upstream_in_a_read_cycle;
  wire             custom_dma_burst_0_upstream_in_a_write_cycle;
  reg              custom_dma_burst_0_upstream_load_fifo;
  wire             custom_dma_burst_0_upstream_master_qreq_vector;
  wire             custom_dma_burst_0_upstream_move_on_to_next_transaction;
  wire    [  2: 0] custom_dma_burst_0_upstream_next_bbt_burstcount;
  wire    [  3: 0] custom_dma_burst_0_upstream_next_burst_count;
  wire             custom_dma_burst_0_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_0_upstream_read;
  wire    [ 31: 0] custom_dma_burst_0_upstream_readdata_from_sa;
  wire             custom_dma_burst_0_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_0_upstream_reg_firsttransfer;
  wire    [  3: 0] custom_dma_burst_0_upstream_selected_burstcount;
  reg              custom_dma_burst_0_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_0_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_0_upstream_this_cycle_is_the_last_burst;
  wire    [  3: 0] custom_dma_burst_0_upstream_transaction_burst_count;
  wire             custom_dma_burst_0_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_0_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_0_upstream_waits_for_read;
  wire             custom_dma_burst_0_upstream_waits_for_write;
  wire             custom_dma_burst_0_upstream_write;
  wire    [ 31: 0] custom_dma_burst_0_upstream_writedata;
  reg              d1_custom_dma_burst_0_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p0_custom_dma_burst_0_upstream_load_fifo;
  wire             wait_for_custom_dma_burst_0_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_0_upstream_end_xfer;
    end


  assign custom_dma_burst_0_upstream_begins_xfer = ~d1_reasons_to_wait & ((cpu_data_master_qualified_request_custom_dma_burst_0_upstream));
  //assign custom_dma_burst_0_upstream_readdata_from_sa = custom_dma_burst_0_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_0_upstream_readdata_from_sa = custom_dma_burst_0_upstream_readdata;

  assign cpu_data_master_requests_custom_dma_burst_0_upstream = ({cpu_data_master_address_to_slave[26 : 21] , 21'b0} == 27'h6000000) & (cpu_data_master_read | cpu_data_master_write);
  //assign custom_dma_burst_0_upstream_waitrequest_from_sa = custom_dma_burst_0_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_0_upstream_waitrequest_from_sa = custom_dma_burst_0_upstream_waitrequest;

  //assign custom_dma_burst_0_upstream_readdatavalid_from_sa = custom_dma_burst_0_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_0_upstream_readdatavalid_from_sa = custom_dma_burst_0_upstream_readdatavalid;

  //custom_dma_burst_0_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_0_upstream_arb_share_set_values = (cpu_data_master_granted_custom_dma_burst_0_upstream)? (((cpu_data_master_write) ? cpu_data_master_burstcount : 1)) :
    1;

  //custom_dma_burst_0_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_0_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_0_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_0_upstream_any_bursting_master_saved_grant = cpu_data_master_saved_grant_custom_dma_burst_0_upstream;

  //custom_dma_burst_0_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_0_upstream_arb_share_counter_next_value = custom_dma_burst_0_upstream_firsttransfer ? (custom_dma_burst_0_upstream_arb_share_set_values - 1) : |custom_dma_burst_0_upstream_arb_share_counter ? (custom_dma_burst_0_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_0_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_0_upstream_allgrants = |custom_dma_burst_0_upstream_grant_vector;

  //custom_dma_burst_0_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_0_upstream_end_xfer = ~(custom_dma_burst_0_upstream_waits_for_read | custom_dma_burst_0_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream = custom_dma_burst_0_upstream_end_xfer & (~custom_dma_burst_0_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_0_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_0_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream & custom_dma_burst_0_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream & ~custom_dma_burst_0_upstream_non_bursting_master_requests);

  //custom_dma_burst_0_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_0_upstream_arb_counter_enable)
          custom_dma_burst_0_upstream_arb_share_counter <= custom_dma_burst_0_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_0_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_0_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_0_upstream & ~custom_dma_burst_0_upstream_non_bursting_master_requests))
          custom_dma_burst_0_upstream_slavearbiterlockenable <= |custom_dma_burst_0_upstream_arb_share_counter_next_value;
    end


  //cpu/data_master custom_dma_burst_0/upstream arbiterlock, which is an e_assign
  assign cpu_data_master_arbiterlock = custom_dma_burst_0_upstream_slavearbiterlockenable & cpu_data_master_continuerequest;

  //custom_dma_burst_0_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_0_upstream_slavearbiterlockenable2 = |custom_dma_burst_0_upstream_arb_share_counter_next_value;

  //cpu/data_master custom_dma_burst_0/upstream arbiterlock2, which is an e_assign
  assign cpu_data_master_arbiterlock2 = custom_dma_burst_0_upstream_slavearbiterlockenable2 & cpu_data_master_continuerequest;

  //custom_dma_burst_0_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_0_upstream_any_continuerequest = 1;

  //cpu_data_master_continuerequest continued request, which is an e_assign
  assign cpu_data_master_continuerequest = 1;

  assign cpu_data_master_qualified_request_custom_dma_burst_0_upstream = cpu_data_master_requests_custom_dma_burst_0_upstream & ~((cpu_data_master_read & ((cpu_data_master_latency_counter != 0) | (1 < cpu_data_master_latency_counter) | (|cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register) | (|cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register))));
  //unique name for custom_dma_burst_0_upstream_move_on_to_next_transaction, which is an e_assign
  assign custom_dma_burst_0_upstream_move_on_to_next_transaction = custom_dma_burst_0_upstream_this_cycle_is_the_last_burst & custom_dma_burst_0_upstream_load_fifo;

  //the currently selected burstcount for custom_dma_burst_0_upstream, which is an e_mux
  assign custom_dma_burst_0_upstream_selected_burstcount = (cpu_data_master_granted_custom_dma_burst_0_upstream)? cpu_data_master_burstcount :
    1;

  //burstcount_fifo_for_custom_dma_burst_0_upstream, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_custom_dma_burst_0_upstream_module burstcount_fifo_for_custom_dma_burst_0_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_0_upstream_selected_burstcount),
      .data_out             (custom_dma_burst_0_upstream_transaction_burst_count),
      .empty                (custom_dma_burst_0_upstream_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (custom_dma_burst_0_upstream_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read & custom_dma_burst_0_upstream_load_fifo & ~(custom_dma_burst_0_upstream_this_cycle_is_the_last_burst & custom_dma_burst_0_upstream_burstcount_fifo_empty))
    );

  //custom_dma_burst_0_upstream current burst minus one, which is an e_assign
  assign custom_dma_burst_0_upstream_current_burst_minus_one = custom_dma_burst_0_upstream_current_burst - 1;

  //what to load in current_burst, for custom_dma_burst_0_upstream, which is an e_mux
  assign custom_dma_burst_0_upstream_next_burst_count = (((in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read) & ~custom_dma_burst_0_upstream_load_fifo))? custom_dma_burst_0_upstream_selected_burstcount :
    ((in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read & custom_dma_burst_0_upstream_this_cycle_is_the_last_burst & custom_dma_burst_0_upstream_burstcount_fifo_empty))? custom_dma_burst_0_upstream_selected_burstcount :
    (custom_dma_burst_0_upstream_this_cycle_is_the_last_burst)? custom_dma_burst_0_upstream_transaction_burst_count :
    custom_dma_burst_0_upstream_current_burst_minus_one;

  //the current burst count for custom_dma_burst_0_upstream, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_current_burst <= 0;
      else if (custom_dma_burst_0_upstream_readdatavalid_from_sa | (~custom_dma_burst_0_upstream_load_fifo & (in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read)))
          custom_dma_burst_0_upstream_current_burst <= custom_dma_burst_0_upstream_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_custom_dma_burst_0_upstream_load_fifo = (~custom_dma_burst_0_upstream_load_fifo)? 1 :
    (((in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read) & custom_dma_burst_0_upstream_load_fifo))? 1 :
    ~custom_dma_burst_0_upstream_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_load_fifo <= 0;
      else if ((in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read) & ~custom_dma_burst_0_upstream_load_fifo | custom_dma_burst_0_upstream_this_cycle_is_the_last_burst)
          custom_dma_burst_0_upstream_load_fifo <= p0_custom_dma_burst_0_upstream_load_fifo;
    end


  //the last cycle in the burst for custom_dma_burst_0_upstream, which is an e_assign
  assign custom_dma_burst_0_upstream_this_cycle_is_the_last_burst = ~(|custom_dma_burst_0_upstream_current_burst_minus_one) & custom_dma_burst_0_upstream_readdatavalid_from_sa;

  //rdv_fifo_for_cpu_data_master_to_custom_dma_burst_0_upstream, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_cpu_data_master_to_custom_dma_burst_0_upstream_module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_0_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (cpu_data_master_granted_custom_dma_burst_0_upstream),
      .data_out             (cpu_data_master_rdv_fifo_output_from_custom_dma_burst_0_upstream),
      .empty                (),
      .fifo_contains_ones_n (cpu_data_master_rdv_fifo_empty_custom_dma_burst_0_upstream),
      .full                 (),
      .read                 (custom_dma_burst_0_upstream_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_0_upstream_waits_for_read)
    );

  assign cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register = ~cpu_data_master_rdv_fifo_empty_custom_dma_burst_0_upstream;
  //local readdatavalid cpu_data_master_read_data_valid_custom_dma_burst_0_upstream, which is an e_mux
  assign cpu_data_master_read_data_valid_custom_dma_burst_0_upstream = custom_dma_burst_0_upstream_readdatavalid_from_sa;

  //custom_dma_burst_0_upstream_writedata mux, which is an e_mux
  assign custom_dma_burst_0_upstream_writedata = cpu_data_master_writedata;

  //byteaddress mux for custom_dma_burst_0/upstream, which is an e_mux
  assign custom_dma_burst_0_upstream_byteaddress = cpu_data_master_address_to_slave;

  //master is always granted when requested
  assign cpu_data_master_granted_custom_dma_burst_0_upstream = cpu_data_master_qualified_request_custom_dma_burst_0_upstream;

  //cpu/data_master saved-grant custom_dma_burst_0/upstream, which is an e_assign
  assign cpu_data_master_saved_grant_custom_dma_burst_0_upstream = cpu_data_master_requests_custom_dma_burst_0_upstream;

  //allow new arb cycle for custom_dma_burst_0/upstream, which is an e_assign
  assign custom_dma_burst_0_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_0_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_0_upstream_master_qreq_vector = 1;

  //custom_dma_burst_0_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_0_upstream_firsttransfer = custom_dma_burst_0_upstream_begins_xfer ? custom_dma_burst_0_upstream_unreg_firsttransfer : custom_dma_burst_0_upstream_reg_firsttransfer;

  //custom_dma_burst_0_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_0_upstream_unreg_firsttransfer = ~(custom_dma_burst_0_upstream_slavearbiterlockenable & custom_dma_burst_0_upstream_any_continuerequest);

  //custom_dma_burst_0_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_0_upstream_begins_xfer)
          custom_dma_burst_0_upstream_reg_firsttransfer <= custom_dma_burst_0_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_0_upstream_next_bbt_burstcount next_bbt_burstcount, which is an e_mux
  assign custom_dma_burst_0_upstream_next_bbt_burstcount = ((((custom_dma_burst_0_upstream_write) && (custom_dma_burst_0_upstream_bbt_burstcounter == 0))))? (custom_dma_burst_0_upstream_burstcount - 1) :
    ((((custom_dma_burst_0_upstream_read) && (custom_dma_burst_0_upstream_bbt_burstcounter == 0))))? 0 :
    (custom_dma_burst_0_upstream_bbt_burstcounter - 1);

  //custom_dma_burst_0_upstream_bbt_burstcounter bbt_burstcounter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_upstream_bbt_burstcounter <= 0;
      else if (custom_dma_burst_0_upstream_begins_xfer)
          custom_dma_burst_0_upstream_bbt_burstcounter <= custom_dma_burst_0_upstream_next_bbt_burstcount;
    end


  //custom_dma_burst_0_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_0_upstream_beginbursttransfer_internal = custom_dma_burst_0_upstream_begins_xfer & (custom_dma_burst_0_upstream_bbt_burstcounter == 0);

  //custom_dma_burst_0_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_0_upstream_read = cpu_data_master_granted_custom_dma_burst_0_upstream & cpu_data_master_read;

  //custom_dma_burst_0_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_0_upstream_write = cpu_data_master_granted_custom_dma_burst_0_upstream & cpu_data_master_write;

  //custom_dma_burst_0_upstream_address mux, which is an e_mux
  assign custom_dma_burst_0_upstream_address = cpu_data_master_address_to_slave;

  //d1_custom_dma_burst_0_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_0_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_0_upstream_end_xfer <= custom_dma_burst_0_upstream_end_xfer;
    end


  //custom_dma_burst_0_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_0_upstream_waits_for_read = custom_dma_burst_0_upstream_in_a_read_cycle & custom_dma_burst_0_upstream_waitrequest_from_sa;

  //custom_dma_burst_0_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_0_upstream_in_a_read_cycle = cpu_data_master_granted_custom_dma_burst_0_upstream & cpu_data_master_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_0_upstream_in_a_read_cycle;

  //custom_dma_burst_0_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_0_upstream_waits_for_write = custom_dma_burst_0_upstream_in_a_write_cycle & custom_dma_burst_0_upstream_waitrequest_from_sa;

  //custom_dma_burst_0_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_0_upstream_in_a_write_cycle = cpu_data_master_granted_custom_dma_burst_0_upstream & cpu_data_master_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_0_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_0_upstream_counter = 0;
  //custom_dma_burst_0_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_0_upstream_byteenable = (cpu_data_master_granted_custom_dma_burst_0_upstream)? cpu_data_master_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign custom_dma_burst_0_upstream_burstcount = (cpu_data_master_granted_custom_dma_burst_0_upstream)? cpu_data_master_burstcount :
    1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_0_upstream_debugaccess = (cpu_data_master_granted_custom_dma_burst_0_upstream)? cpu_data_master_debugaccess :
    0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_0/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //cpu/data_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (cpu_data_master_requests_custom_dma_burst_0_upstream && (cpu_data_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: cpu/data_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_0/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_0_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_0_downstream_address,
                                                   custom_dma_burst_0_downstream_burstcount,
                                                   custom_dma_burst_0_downstream_byteenable,
                                                   custom_dma_burst_0_downstream_granted_ext_ssram_s1,
                                                   custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1,
                                                   custom_dma_burst_0_downstream_read,
                                                   custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1,
                                                   custom_dma_burst_0_downstream_requests_ext_ssram_s1,
                                                   custom_dma_burst_0_downstream_write,
                                                   custom_dma_burst_0_downstream_writedata,
                                                   d1_ext_ssram_bus_avalon_slave_end_xfer,
                                                   incoming_ext_ssram_bus_data,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_0_downstream_address_to_slave,
                                                   custom_dma_burst_0_downstream_latency_counter,
                                                   custom_dma_burst_0_downstream_readdata,
                                                   custom_dma_burst_0_downstream_readdatavalid,
                                                   custom_dma_burst_0_downstream_reset_n,
                                                   custom_dma_burst_0_downstream_waitrequest
                                                )
;

  output  [ 20: 0] custom_dma_burst_0_downstream_address_to_slave;
  output  [  2: 0] custom_dma_burst_0_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_0_downstream_readdata;
  output           custom_dma_burst_0_downstream_readdatavalid;
  output           custom_dma_burst_0_downstream_reset_n;
  output           custom_dma_burst_0_downstream_waitrequest;
  input            clk;
  input   [ 20: 0] custom_dma_burst_0_downstream_address;
  input            custom_dma_burst_0_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_0_downstream_byteenable;
  input            custom_dma_burst_0_downstream_granted_ext_ssram_s1;
  input            custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1;
  input            custom_dma_burst_0_downstream_read;
  input            custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1;
  input            custom_dma_burst_0_downstream_requests_ext_ssram_s1;
  input            custom_dma_burst_0_downstream_write;
  input   [ 31: 0] custom_dma_burst_0_downstream_writedata;
  input            d1_ext_ssram_bus_avalon_slave_end_xfer;
  input   [ 31: 0] incoming_ext_ssram_bus_data;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 20: 0] custom_dma_burst_0_downstream_address_last_time;
  wire    [ 20: 0] custom_dma_burst_0_downstream_address_to_slave;
  reg              custom_dma_burst_0_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_0_downstream_byteenable_last_time;
  wire             custom_dma_burst_0_downstream_is_granted_some_slave;
  reg     [  2: 0] custom_dma_burst_0_downstream_latency_counter;
  reg              custom_dma_burst_0_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_0_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_0_downstream_readdata;
  wire             custom_dma_burst_0_downstream_readdatavalid;
  wire             custom_dma_burst_0_downstream_reset_n;
  wire             custom_dma_burst_0_downstream_run;
  wire             custom_dma_burst_0_downstream_waitrequest;
  reg              custom_dma_burst_0_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_0_downstream_writedata_last_time;
  wire    [  2: 0] latency_load_value;
  wire    [  2: 0] p1_custom_dma_burst_0_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_0_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 | ~custom_dma_burst_0_downstream_requests_ext_ssram_s1) & (custom_dma_burst_0_downstream_granted_ext_ssram_s1 | ~custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1) & ((~custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 | ~(custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write) | (1 & (custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write)))) & ((~custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 | ~(custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write) | (1 & (custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_0_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_0_downstream_address_to_slave = custom_dma_burst_0_downstream_address;

  //custom_dma_burst_0_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_0_downstream_read_but_no_slave_selected <= custom_dma_burst_0_downstream_read & custom_dma_burst_0_downstream_run & ~custom_dma_burst_0_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_0_downstream_is_granted_some_slave = custom_dma_burst_0_downstream_granted_ext_ssram_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_0_downstream_readdatavalid = custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_0_downstream_readdatavalid = custom_dma_burst_0_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_0_downstream_readdatavalid;

  //custom_dma_burst_0/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_0_downstream_readdata = incoming_ext_ssram_bus_data;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_0_downstream_waitrequest = ~custom_dma_burst_0_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_0_downstream_latency_counter <= p1_custom_dma_burst_0_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_0_downstream_latency_counter = ((custom_dma_burst_0_downstream_run & custom_dma_burst_0_downstream_read))? latency_load_value :
    (custom_dma_burst_0_downstream_latency_counter)? custom_dma_burst_0_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = {3 {custom_dma_burst_0_downstream_requests_ext_ssram_s1}} & 4;

  //custom_dma_burst_0_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_0_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_0_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_address_last_time <= custom_dma_burst_0_downstream_address;
    end


  //custom_dma_burst_0/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_0_downstream_waitrequest & (custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write);
    end


  //custom_dma_burst_0_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_address != custom_dma_burst_0_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_0_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_burstcount_last_time <= custom_dma_burst_0_downstream_burstcount;
    end


  //custom_dma_burst_0_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_burstcount != custom_dma_burst_0_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_0_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_byteenable_last_time <= custom_dma_burst_0_downstream_byteenable;
    end


  //custom_dma_burst_0_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_byteenable != custom_dma_burst_0_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_0_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_read_last_time <= custom_dma_burst_0_downstream_read;
    end


  //custom_dma_burst_0_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_read != custom_dma_burst_0_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_0_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_write_last_time <= custom_dma_burst_0_downstream_write;
    end


  //custom_dma_burst_0_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_write != custom_dma_burst_0_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_0_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_0_downstream_writedata_last_time <= custom_dma_burst_0_downstream_writedata;
    end


  //custom_dma_burst_0_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_0_downstream_writedata != custom_dma_burst_0_downstream_writedata_last_time) & custom_dma_burst_0_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_0_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_custom_dma_burst_1_upstream_module (
                                                                // inputs:
                                                                 clear_fifo,
                                                                 clk,
                                                                 data_in,
                                                                 read,
                                                                 reset_n,
                                                                 sync_reset,
                                                                 write,

                                                                // outputs:
                                                                 data_out,
                                                                 empty,
                                                                 fifo_contains_ones_n,
                                                                 full
                                                              )
;

  output  [  3: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  3: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  3: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  3: 0] p0_stage_0;
  wire             p1_full_1;
  wire    [  3: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  3: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  3: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  3: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  3: 0] p5_stage_5;
  reg     [  3: 0] stage_0;
  reg     [  3: 0] stage_1;
  reg     [  3: 0] stage_2;
  reg     [  3: 0] stage_3;
  reg     [  3: 0] stage_4;
  reg     [  3: 0] stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_1_upstream_module (
                                                                                   // inputs:
                                                                                    clear_fifo,
                                                                                    clk,
                                                                                    data_in,
                                                                                    read,
                                                                                    reset_n,
                                                                                    sync_reset,
                                                                                    write,

                                                                                   // outputs:
                                                                                    data_out,
                                                                                    empty,
                                                                                    fifo_contains_ones_n,
                                                                                    full
                                                                                 )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  reg              stage_0;
  reg              stage_1;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_1_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 cpu_instruction_master_address_to_slave,
                                                 cpu_instruction_master_burstcount,
                                                 cpu_instruction_master_latency_counter,
                                                 cpu_instruction_master_read,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register,
                                                 custom_dma_burst_1_upstream_readdata,
                                                 custom_dma_burst_1_upstream_readdatavalid,
                                                 custom_dma_burst_1_upstream_waitrequest,
                                                 reset_n,

                                                // outputs:
                                                 cpu_instruction_master_granted_custom_dma_burst_1_upstream,
                                                 cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register,
                                                 cpu_instruction_master_requests_custom_dma_burst_1_upstream,
                                                 custom_dma_burst_1_upstream_address,
                                                 custom_dma_burst_1_upstream_byteaddress,
                                                 custom_dma_burst_1_upstream_byteenable,
                                                 custom_dma_burst_1_upstream_debugaccess,
                                                 custom_dma_burst_1_upstream_read,
                                                 custom_dma_burst_1_upstream_readdata_from_sa,
                                                 custom_dma_burst_1_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_1_upstream_write,
                                                 d1_custom_dma_burst_1_upstream_end_xfer
                                              )
;

  output           cpu_instruction_master_granted_custom_dma_burst_1_upstream;
  output           cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream;
  output           cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream;
  output           cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register;
  output           cpu_instruction_master_requests_custom_dma_burst_1_upstream;
  output  [ 11: 0] custom_dma_burst_1_upstream_address;
  output  [ 13: 0] custom_dma_burst_1_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_1_upstream_byteenable;
  output           custom_dma_burst_1_upstream_debugaccess;
  output           custom_dma_burst_1_upstream_read;
  output  [ 31: 0] custom_dma_burst_1_upstream_readdata_from_sa;
  output           custom_dma_burst_1_upstream_waitrequest_from_sa;
  output           custom_dma_burst_1_upstream_write;
  output           d1_custom_dma_burst_1_upstream_end_xfer;
  input            clk;
  input   [ 26: 0] cpu_instruction_master_address_to_slave;
  input   [  3: 0] cpu_instruction_master_burstcount;
  input            cpu_instruction_master_latency_counter;
  input            cpu_instruction_master_read;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register;
  input   [ 31: 0] custom_dma_burst_1_upstream_readdata;
  input            custom_dma_burst_1_upstream_readdatavalid;
  input            custom_dma_burst_1_upstream_waitrequest;
  input            reset_n;

  wire             cpu_instruction_master_arbiterlock;
  wire             cpu_instruction_master_arbiterlock2;
  wire             cpu_instruction_master_continuerequest;
  wire             cpu_instruction_master_granted_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_rdv_fifo_output_from_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register;
  wire             cpu_instruction_master_requests_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_saved_grant_custom_dma_burst_1_upstream;
  wire    [ 11: 0] custom_dma_burst_1_upstream_address;
  wire             custom_dma_burst_1_upstream_allgrants;
  wire             custom_dma_burst_1_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_1_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_1_upstream_any_continuerequest;
  wire             custom_dma_burst_1_upstream_arb_counter_enable;
  reg     [  3: 0] custom_dma_burst_1_upstream_arb_share_counter;
  wire    [  3: 0] custom_dma_burst_1_upstream_arb_share_counter_next_value;
  wire    [  3: 0] custom_dma_burst_1_upstream_arb_share_set_values;
  wire             custom_dma_burst_1_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_1_upstream_begins_xfer;
  wire             custom_dma_burst_1_upstream_burstcount_fifo_empty;
  wire    [ 13: 0] custom_dma_burst_1_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_1_upstream_byteenable;
  reg     [  3: 0] custom_dma_burst_1_upstream_current_burst;
  wire    [  3: 0] custom_dma_burst_1_upstream_current_burst_minus_one;
  wire             custom_dma_burst_1_upstream_debugaccess;
  wire             custom_dma_burst_1_upstream_end_xfer;
  wire             custom_dma_burst_1_upstream_firsttransfer;
  wire             custom_dma_burst_1_upstream_grant_vector;
  wire             custom_dma_burst_1_upstream_in_a_read_cycle;
  wire             custom_dma_burst_1_upstream_in_a_write_cycle;
  reg              custom_dma_burst_1_upstream_load_fifo;
  wire             custom_dma_burst_1_upstream_master_qreq_vector;
  wire             custom_dma_burst_1_upstream_move_on_to_next_transaction;
  wire    [  3: 0] custom_dma_burst_1_upstream_next_burst_count;
  wire             custom_dma_burst_1_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_1_upstream_read;
  wire    [ 31: 0] custom_dma_burst_1_upstream_readdata_from_sa;
  wire             custom_dma_burst_1_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_1_upstream_reg_firsttransfer;
  wire    [  3: 0] custom_dma_burst_1_upstream_selected_burstcount;
  reg              custom_dma_burst_1_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_1_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_1_upstream_this_cycle_is_the_last_burst;
  wire    [  3: 0] custom_dma_burst_1_upstream_transaction_burst_count;
  wire             custom_dma_burst_1_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_1_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_1_upstream_waits_for_read;
  wire             custom_dma_burst_1_upstream_waits_for_write;
  wire             custom_dma_burst_1_upstream_write;
  reg              d1_custom_dma_burst_1_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p0_custom_dma_burst_1_upstream_load_fifo;
  wire             wait_for_custom_dma_burst_1_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_1_upstream_end_xfer;
    end


  assign custom_dma_burst_1_upstream_begins_xfer = ~d1_reasons_to_wait & ((cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream));
  //assign custom_dma_burst_1_upstream_readdata_from_sa = custom_dma_burst_1_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_1_upstream_readdata_from_sa = custom_dma_burst_1_upstream_readdata;

  assign cpu_instruction_master_requests_custom_dma_burst_1_upstream = (({cpu_instruction_master_address_to_slave[26 : 12] , 12'b0} == 27'h5000000) & (cpu_instruction_master_read)) & cpu_instruction_master_read;
  //assign custom_dma_burst_1_upstream_waitrequest_from_sa = custom_dma_burst_1_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_1_upstream_waitrequest_from_sa = custom_dma_burst_1_upstream_waitrequest;

  //assign custom_dma_burst_1_upstream_readdatavalid_from_sa = custom_dma_burst_1_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_1_upstream_readdatavalid_from_sa = custom_dma_burst_1_upstream_readdatavalid;

  //custom_dma_burst_1_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_1_upstream_arb_share_set_values = 1;

  //custom_dma_burst_1_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_1_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_1_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_1_upstream_any_bursting_master_saved_grant = cpu_instruction_master_saved_grant_custom_dma_burst_1_upstream;

  //custom_dma_burst_1_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_1_upstream_arb_share_counter_next_value = custom_dma_burst_1_upstream_firsttransfer ? (custom_dma_burst_1_upstream_arb_share_set_values - 1) : |custom_dma_burst_1_upstream_arb_share_counter ? (custom_dma_burst_1_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_1_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_1_upstream_allgrants = |custom_dma_burst_1_upstream_grant_vector;

  //custom_dma_burst_1_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_1_upstream_end_xfer = ~(custom_dma_burst_1_upstream_waits_for_read | custom_dma_burst_1_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream = custom_dma_burst_1_upstream_end_xfer & (~custom_dma_burst_1_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_1_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_1_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream & custom_dma_burst_1_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream & ~custom_dma_burst_1_upstream_non_bursting_master_requests);

  //custom_dma_burst_1_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_1_upstream_arb_counter_enable)
          custom_dma_burst_1_upstream_arb_share_counter <= custom_dma_burst_1_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_1_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_1_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_1_upstream & ~custom_dma_burst_1_upstream_non_bursting_master_requests))
          custom_dma_burst_1_upstream_slavearbiterlockenable <= |custom_dma_burst_1_upstream_arb_share_counter_next_value;
    end


  //cpu/instruction_master custom_dma_burst_1/upstream arbiterlock, which is an e_assign
  assign cpu_instruction_master_arbiterlock = custom_dma_burst_1_upstream_slavearbiterlockenable & cpu_instruction_master_continuerequest;

  //custom_dma_burst_1_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_1_upstream_slavearbiterlockenable2 = |custom_dma_burst_1_upstream_arb_share_counter_next_value;

  //cpu/instruction_master custom_dma_burst_1/upstream arbiterlock2, which is an e_assign
  assign cpu_instruction_master_arbiterlock2 = custom_dma_burst_1_upstream_slavearbiterlockenable2 & cpu_instruction_master_continuerequest;

  //custom_dma_burst_1_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_1_upstream_any_continuerequest = 1;

  //cpu_instruction_master_continuerequest continued request, which is an e_assign
  assign cpu_instruction_master_continuerequest = 1;

  assign cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream = cpu_instruction_master_requests_custom_dma_burst_1_upstream & ~((cpu_instruction_master_read & ((cpu_instruction_master_latency_counter != 0) | (1 < cpu_instruction_master_latency_counter) | (|cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register))));
  //unique name for custom_dma_burst_1_upstream_move_on_to_next_transaction, which is an e_assign
  assign custom_dma_burst_1_upstream_move_on_to_next_transaction = custom_dma_burst_1_upstream_this_cycle_is_the_last_burst & custom_dma_burst_1_upstream_load_fifo;

  //the currently selected burstcount for custom_dma_burst_1_upstream, which is an e_mux
  assign custom_dma_burst_1_upstream_selected_burstcount = (cpu_instruction_master_granted_custom_dma_burst_1_upstream)? cpu_instruction_master_burstcount :
    1;

  //burstcount_fifo_for_custom_dma_burst_1_upstream, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_custom_dma_burst_1_upstream_module burstcount_fifo_for_custom_dma_burst_1_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_1_upstream_selected_burstcount),
      .data_out             (custom_dma_burst_1_upstream_transaction_burst_count),
      .empty                (custom_dma_burst_1_upstream_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (custom_dma_burst_1_upstream_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read & custom_dma_burst_1_upstream_load_fifo & ~(custom_dma_burst_1_upstream_this_cycle_is_the_last_burst & custom_dma_burst_1_upstream_burstcount_fifo_empty))
    );

  //custom_dma_burst_1_upstream current burst minus one, which is an e_assign
  assign custom_dma_burst_1_upstream_current_burst_minus_one = custom_dma_burst_1_upstream_current_burst - 1;

  //what to load in current_burst, for custom_dma_burst_1_upstream, which is an e_mux
  assign custom_dma_burst_1_upstream_next_burst_count = (((in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read) & ~custom_dma_burst_1_upstream_load_fifo))? custom_dma_burst_1_upstream_selected_burstcount :
    ((in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read & custom_dma_burst_1_upstream_this_cycle_is_the_last_burst & custom_dma_burst_1_upstream_burstcount_fifo_empty))? custom_dma_burst_1_upstream_selected_burstcount :
    (custom_dma_burst_1_upstream_this_cycle_is_the_last_burst)? custom_dma_burst_1_upstream_transaction_burst_count :
    custom_dma_burst_1_upstream_current_burst_minus_one;

  //the current burst count for custom_dma_burst_1_upstream, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_upstream_current_burst <= 0;
      else if (custom_dma_burst_1_upstream_readdatavalid_from_sa | (~custom_dma_burst_1_upstream_load_fifo & (in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read)))
          custom_dma_burst_1_upstream_current_burst <= custom_dma_burst_1_upstream_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_custom_dma_burst_1_upstream_load_fifo = (~custom_dma_burst_1_upstream_load_fifo)? 1 :
    (((in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read) & custom_dma_burst_1_upstream_load_fifo))? 1 :
    ~custom_dma_burst_1_upstream_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_upstream_load_fifo <= 0;
      else if ((in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read) & ~custom_dma_burst_1_upstream_load_fifo | custom_dma_burst_1_upstream_this_cycle_is_the_last_burst)
          custom_dma_burst_1_upstream_load_fifo <= p0_custom_dma_burst_1_upstream_load_fifo;
    end


  //the last cycle in the burst for custom_dma_burst_1_upstream, which is an e_assign
  assign custom_dma_burst_1_upstream_this_cycle_is_the_last_burst = ~(|custom_dma_burst_1_upstream_current_burst_minus_one) & custom_dma_burst_1_upstream_readdatavalid_from_sa;

  //rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_1_upstream, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_1_upstream_module rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_1_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (cpu_instruction_master_granted_custom_dma_burst_1_upstream),
      .data_out             (cpu_instruction_master_rdv_fifo_output_from_custom_dma_burst_1_upstream),
      .empty                (),
      .fifo_contains_ones_n (cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_1_upstream),
      .full                 (),
      .read                 (custom_dma_burst_1_upstream_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_1_upstream_waits_for_read)
    );

  assign cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register = ~cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_1_upstream;
  //local readdatavalid cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream, which is an e_mux
  assign cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream = custom_dma_burst_1_upstream_readdatavalid_from_sa;

  //byteaddress mux for custom_dma_burst_1/upstream, which is an e_mux
  assign custom_dma_burst_1_upstream_byteaddress = cpu_instruction_master_address_to_slave;

  //master is always granted when requested
  assign cpu_instruction_master_granted_custom_dma_burst_1_upstream = cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream;

  //cpu/instruction_master saved-grant custom_dma_burst_1/upstream, which is an e_assign
  assign cpu_instruction_master_saved_grant_custom_dma_burst_1_upstream = cpu_instruction_master_requests_custom_dma_burst_1_upstream;

  //allow new arb cycle for custom_dma_burst_1/upstream, which is an e_assign
  assign custom_dma_burst_1_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_1_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_1_upstream_master_qreq_vector = 1;

  //custom_dma_burst_1_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_1_upstream_firsttransfer = custom_dma_burst_1_upstream_begins_xfer ? custom_dma_burst_1_upstream_unreg_firsttransfer : custom_dma_burst_1_upstream_reg_firsttransfer;

  //custom_dma_burst_1_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_1_upstream_unreg_firsttransfer = ~(custom_dma_burst_1_upstream_slavearbiterlockenable & custom_dma_burst_1_upstream_any_continuerequest);

  //custom_dma_burst_1_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_1_upstream_begins_xfer)
          custom_dma_burst_1_upstream_reg_firsttransfer <= custom_dma_burst_1_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_1_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_1_upstream_beginbursttransfer_internal = custom_dma_burst_1_upstream_begins_xfer;

  //custom_dma_burst_1_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_1_upstream_read = cpu_instruction_master_granted_custom_dma_burst_1_upstream & cpu_instruction_master_read;

  //custom_dma_burst_1_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_1_upstream_write = 0;

  //custom_dma_burst_1_upstream_address mux, which is an e_mux
  assign custom_dma_burst_1_upstream_address = cpu_instruction_master_address_to_slave;

  //d1_custom_dma_burst_1_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_1_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_1_upstream_end_xfer <= custom_dma_burst_1_upstream_end_xfer;
    end


  //custom_dma_burst_1_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_1_upstream_waits_for_read = custom_dma_burst_1_upstream_in_a_read_cycle & custom_dma_burst_1_upstream_waitrequest_from_sa;

  //custom_dma_burst_1_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_1_upstream_in_a_read_cycle = cpu_instruction_master_granted_custom_dma_burst_1_upstream & cpu_instruction_master_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_1_upstream_in_a_read_cycle;

  //custom_dma_burst_1_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_1_upstream_waits_for_write = custom_dma_burst_1_upstream_in_a_write_cycle & custom_dma_burst_1_upstream_waitrequest_from_sa;

  //custom_dma_burst_1_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_1_upstream_in_a_write_cycle = 0;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_1_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_1_upstream_counter = 0;
  //custom_dma_burst_1_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_1_upstream_byteenable = -1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_1_upstream_debugaccess = 0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_1/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //cpu/instruction_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (cpu_instruction_master_requests_custom_dma_burst_1_upstream && (cpu_instruction_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: cpu/instruction_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_1/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_1_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_1_downstream_address,
                                                   custom_dma_burst_1_downstream_burstcount,
                                                   custom_dma_burst_1_downstream_byteenable,
                                                   custom_dma_burst_1_downstream_granted_pipeline_bridge_s1,
                                                   custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1,
                                                   custom_dma_burst_1_downstream_read,
                                                   custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1,
                                                   custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register,
                                                   custom_dma_burst_1_downstream_requests_pipeline_bridge_s1,
                                                   custom_dma_burst_1_downstream_write,
                                                   custom_dma_burst_1_downstream_writedata,
                                                   d1_pipeline_bridge_s1_end_xfer,
                                                   pipeline_bridge_s1_readdata_from_sa,
                                                   pipeline_bridge_s1_waitrequest_from_sa,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_1_downstream_address_to_slave,
                                                   custom_dma_burst_1_downstream_latency_counter,
                                                   custom_dma_burst_1_downstream_readdata,
                                                   custom_dma_burst_1_downstream_readdatavalid,
                                                   custom_dma_burst_1_downstream_reset_n,
                                                   custom_dma_burst_1_downstream_waitrequest
                                                )
;

  output  [ 11: 0] custom_dma_burst_1_downstream_address_to_slave;
  output           custom_dma_burst_1_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_1_downstream_readdata;
  output           custom_dma_burst_1_downstream_readdatavalid;
  output           custom_dma_burst_1_downstream_reset_n;
  output           custom_dma_burst_1_downstream_waitrequest;
  input            clk;
  input   [ 11: 0] custom_dma_burst_1_downstream_address;
  input            custom_dma_burst_1_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_1_downstream_byteenable;
  input            custom_dma_burst_1_downstream_granted_pipeline_bridge_s1;
  input            custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1;
  input            custom_dma_burst_1_downstream_read;
  input            custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1;
  input            custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  input            custom_dma_burst_1_downstream_requests_pipeline_bridge_s1;
  input            custom_dma_burst_1_downstream_write;
  input   [ 31: 0] custom_dma_burst_1_downstream_writedata;
  input            d1_pipeline_bridge_s1_end_xfer;
  input   [ 31: 0] pipeline_bridge_s1_readdata_from_sa;
  input            pipeline_bridge_s1_waitrequest_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 11: 0] custom_dma_burst_1_downstream_address_last_time;
  wire    [ 11: 0] custom_dma_burst_1_downstream_address_to_slave;
  reg              custom_dma_burst_1_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_1_downstream_byteenable_last_time;
  wire             custom_dma_burst_1_downstream_is_granted_some_slave;
  reg              custom_dma_burst_1_downstream_latency_counter;
  reg              custom_dma_burst_1_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_1_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_1_downstream_readdata;
  wire             custom_dma_burst_1_downstream_readdatavalid;
  wire             custom_dma_burst_1_downstream_reset_n;
  wire             custom_dma_burst_1_downstream_run;
  wire             custom_dma_burst_1_downstream_waitrequest;
  reg              custom_dma_burst_1_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_1_downstream_writedata_last_time;
  wire             latency_load_value;
  wire             p1_custom_dma_burst_1_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_1_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1 | ~custom_dma_burst_1_downstream_requests_pipeline_bridge_s1) & (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 | ~custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1) & ((~custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1 | ~(custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write) | (1 & ~pipeline_bridge_s1_waitrequest_from_sa & (custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write)))) & ((~custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1 | ~(custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write) | (1 & ~pipeline_bridge_s1_waitrequest_from_sa & (custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_1_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_1_downstream_address_to_slave = custom_dma_burst_1_downstream_address;

  //custom_dma_burst_1_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_1_downstream_read_but_no_slave_selected <= custom_dma_burst_1_downstream_read & custom_dma_burst_1_downstream_run & ~custom_dma_burst_1_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_1_downstream_is_granted_some_slave = custom_dma_burst_1_downstream_granted_pipeline_bridge_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_1_downstream_readdatavalid = custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_1_downstream_readdatavalid = custom_dma_burst_1_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_1_downstream_readdatavalid;

  //custom_dma_burst_1/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_1_downstream_readdata = pipeline_bridge_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_1_downstream_waitrequest = ~custom_dma_burst_1_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_1_downstream_latency_counter <= p1_custom_dma_burst_1_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_1_downstream_latency_counter = ((custom_dma_burst_1_downstream_run & custom_dma_burst_1_downstream_read))? latency_load_value :
    (custom_dma_burst_1_downstream_latency_counter)? custom_dma_burst_1_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //custom_dma_burst_1_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_1_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_1_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_address_last_time <= custom_dma_burst_1_downstream_address;
    end


  //custom_dma_burst_1/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_1_downstream_waitrequest & (custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write);
    end


  //custom_dma_burst_1_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_address != custom_dma_burst_1_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_1_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_burstcount_last_time <= custom_dma_burst_1_downstream_burstcount;
    end


  //custom_dma_burst_1_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_burstcount != custom_dma_burst_1_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_1_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_byteenable_last_time <= custom_dma_burst_1_downstream_byteenable;
    end


  //custom_dma_burst_1_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_byteenable != custom_dma_burst_1_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_1_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_read_last_time <= custom_dma_burst_1_downstream_read;
    end


  //custom_dma_burst_1_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_read != custom_dma_burst_1_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_1_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_write_last_time <= custom_dma_burst_1_downstream_write;
    end


  //custom_dma_burst_1_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_write != custom_dma_burst_1_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_1_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_1_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_1_downstream_writedata_last_time <= custom_dma_burst_1_downstream_writedata;
    end


  //custom_dma_burst_1_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_1_downstream_writedata != custom_dma_burst_1_downstream_writedata_last_time) & custom_dma_burst_1_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_1_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_custom_dma_burst_2_upstream_module (
                                                                // inputs:
                                                                 clear_fifo,
                                                                 clk,
                                                                 data_in,
                                                                 read,
                                                                 reset_n,
                                                                 sync_reset,
                                                                 write,

                                                                // outputs:
                                                                 data_out,
                                                                 empty,
                                                                 fifo_contains_ones_n,
                                                                 full
                                                              )
;

  output  [  3: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  3: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  3: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  3: 0] p0_stage_0;
  wire             p1_full_1;
  wire    [  3: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  3: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  3: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  3: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  3: 0] p5_stage_5;
  reg     [  3: 0] stage_0;
  reg     [  3: 0] stage_1;
  reg     [  3: 0] stage_2;
  reg     [  3: 0] stage_3;
  reg     [  3: 0] stage_4;
  reg     [  3: 0] stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_2_upstream_module (
                                                                            // inputs:
                                                                             clear_fifo,
                                                                             clk,
                                                                             data_in,
                                                                             read,
                                                                             reset_n,
                                                                             sync_reset,
                                                                             write,

                                                                            // outputs:
                                                                             data_out,
                                                                             empty,
                                                                             fifo_contains_ones_n,
                                                                             full
                                                                          )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  wire             full_6;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  reg              stage_0;
  reg              stage_1;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_5;
  assign empty = !full_0;
  assign full_6 = 0;
  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    0;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_2_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 cpu_data_master_address_to_slave,
                                                 cpu_data_master_burstcount,
                                                 cpu_data_master_byteenable,
                                                 cpu_data_master_debugaccess,
                                                 cpu_data_master_latency_counter,
                                                 cpu_data_master_read,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register,
                                                 cpu_data_master_write,
                                                 cpu_data_master_writedata,
                                                 custom_dma_burst_2_upstream_readdata,
                                                 custom_dma_burst_2_upstream_readdatavalid,
                                                 custom_dma_burst_2_upstream_waitrequest,
                                                 reset_n,

                                                // outputs:
                                                 cpu_data_master_granted_custom_dma_burst_2_upstream,
                                                 cpu_data_master_qualified_request_custom_dma_burst_2_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_2_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register,
                                                 cpu_data_master_requests_custom_dma_burst_2_upstream,
                                                 custom_dma_burst_2_upstream_address,
                                                 custom_dma_burst_2_upstream_burstcount,
                                                 custom_dma_burst_2_upstream_byteaddress,
                                                 custom_dma_burst_2_upstream_byteenable,
                                                 custom_dma_burst_2_upstream_debugaccess,
                                                 custom_dma_burst_2_upstream_read,
                                                 custom_dma_burst_2_upstream_readdata_from_sa,
                                                 custom_dma_burst_2_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_2_upstream_write,
                                                 custom_dma_burst_2_upstream_writedata,
                                                 d1_custom_dma_burst_2_upstream_end_xfer
                                              )
;

  output           cpu_data_master_granted_custom_dma_burst_2_upstream;
  output           cpu_data_master_qualified_request_custom_dma_burst_2_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_2_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  output           cpu_data_master_requests_custom_dma_burst_2_upstream;
  output  [ 11: 0] custom_dma_burst_2_upstream_address;
  output  [  3: 0] custom_dma_burst_2_upstream_burstcount;
  output  [ 13: 0] custom_dma_burst_2_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_2_upstream_byteenable;
  output           custom_dma_burst_2_upstream_debugaccess;
  output           custom_dma_burst_2_upstream_read;
  output  [ 31: 0] custom_dma_burst_2_upstream_readdata_from_sa;
  output           custom_dma_burst_2_upstream_waitrequest_from_sa;
  output           custom_dma_burst_2_upstream_write;
  output  [ 31: 0] custom_dma_burst_2_upstream_writedata;
  output           d1_custom_dma_burst_2_upstream_end_xfer;
  input            clk;
  input   [ 26: 0] cpu_data_master_address_to_slave;
  input   [  3: 0] cpu_data_master_burstcount;
  input   [  3: 0] cpu_data_master_byteenable;
  input            cpu_data_master_debugaccess;
  input            cpu_data_master_latency_counter;
  input            cpu_data_master_read;
  input            cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  input            cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  input            cpu_data_master_write;
  input   [ 31: 0] cpu_data_master_writedata;
  input   [ 31: 0] custom_dma_burst_2_upstream_readdata;
  input            custom_dma_burst_2_upstream_readdatavalid;
  input            custom_dma_burst_2_upstream_waitrequest;
  input            reset_n;

  wire             cpu_data_master_arbiterlock;
  wire             cpu_data_master_arbiterlock2;
  wire             cpu_data_master_continuerequest;
  wire             cpu_data_master_granted_custom_dma_burst_2_upstream;
  wire             cpu_data_master_qualified_request_custom_dma_burst_2_upstream;
  wire             cpu_data_master_rdv_fifo_empty_custom_dma_burst_2_upstream;
  wire             cpu_data_master_rdv_fifo_output_from_custom_dma_burst_2_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_2_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  wire             cpu_data_master_requests_custom_dma_burst_2_upstream;
  wire             cpu_data_master_saved_grant_custom_dma_burst_2_upstream;
  wire    [ 11: 0] custom_dma_burst_2_upstream_address;
  wire             custom_dma_burst_2_upstream_allgrants;
  wire             custom_dma_burst_2_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_2_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_2_upstream_any_continuerequest;
  wire             custom_dma_burst_2_upstream_arb_counter_enable;
  reg     [  3: 0] custom_dma_burst_2_upstream_arb_share_counter;
  wire    [  3: 0] custom_dma_burst_2_upstream_arb_share_counter_next_value;
  wire    [  3: 0] custom_dma_burst_2_upstream_arb_share_set_values;
  reg     [  2: 0] custom_dma_burst_2_upstream_bbt_burstcounter;
  wire             custom_dma_burst_2_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_2_upstream_begins_xfer;
  wire    [  3: 0] custom_dma_burst_2_upstream_burstcount;
  wire             custom_dma_burst_2_upstream_burstcount_fifo_empty;
  wire    [ 13: 0] custom_dma_burst_2_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_2_upstream_byteenable;
  reg     [  3: 0] custom_dma_burst_2_upstream_current_burst;
  wire    [  3: 0] custom_dma_burst_2_upstream_current_burst_minus_one;
  wire             custom_dma_burst_2_upstream_debugaccess;
  wire             custom_dma_burst_2_upstream_end_xfer;
  wire             custom_dma_burst_2_upstream_firsttransfer;
  wire             custom_dma_burst_2_upstream_grant_vector;
  wire             custom_dma_burst_2_upstream_in_a_read_cycle;
  wire             custom_dma_burst_2_upstream_in_a_write_cycle;
  reg              custom_dma_burst_2_upstream_load_fifo;
  wire             custom_dma_burst_2_upstream_master_qreq_vector;
  wire             custom_dma_burst_2_upstream_move_on_to_next_transaction;
  wire    [  2: 0] custom_dma_burst_2_upstream_next_bbt_burstcount;
  wire    [  3: 0] custom_dma_burst_2_upstream_next_burst_count;
  wire             custom_dma_burst_2_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_2_upstream_read;
  wire    [ 31: 0] custom_dma_burst_2_upstream_readdata_from_sa;
  wire             custom_dma_burst_2_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_2_upstream_reg_firsttransfer;
  wire    [  3: 0] custom_dma_burst_2_upstream_selected_burstcount;
  reg              custom_dma_burst_2_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_2_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_2_upstream_this_cycle_is_the_last_burst;
  wire    [  3: 0] custom_dma_burst_2_upstream_transaction_burst_count;
  wire             custom_dma_burst_2_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_2_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_2_upstream_waits_for_read;
  wire             custom_dma_burst_2_upstream_waits_for_write;
  wire             custom_dma_burst_2_upstream_write;
  wire    [ 31: 0] custom_dma_burst_2_upstream_writedata;
  reg              d1_custom_dma_burst_2_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p0_custom_dma_burst_2_upstream_load_fifo;
  wire             wait_for_custom_dma_burst_2_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_2_upstream_end_xfer;
    end


  assign custom_dma_burst_2_upstream_begins_xfer = ~d1_reasons_to_wait & ((cpu_data_master_qualified_request_custom_dma_burst_2_upstream));
  //assign custom_dma_burst_2_upstream_readdatavalid_from_sa = custom_dma_burst_2_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_2_upstream_readdatavalid_from_sa = custom_dma_burst_2_upstream_readdatavalid;

  //assign custom_dma_burst_2_upstream_readdata_from_sa = custom_dma_burst_2_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_2_upstream_readdata_from_sa = custom_dma_burst_2_upstream_readdata;

  assign cpu_data_master_requests_custom_dma_burst_2_upstream = ({cpu_data_master_address_to_slave[26 : 12] , 12'b0} == 27'h5000000) & (cpu_data_master_read | cpu_data_master_write);
  //assign custom_dma_burst_2_upstream_waitrequest_from_sa = custom_dma_burst_2_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_2_upstream_waitrequest_from_sa = custom_dma_burst_2_upstream_waitrequest;

  //custom_dma_burst_2_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_2_upstream_arb_share_set_values = (cpu_data_master_granted_custom_dma_burst_2_upstream)? (((cpu_data_master_write) ? cpu_data_master_burstcount : 1)) :
    1;

  //custom_dma_burst_2_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_2_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_2_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_2_upstream_any_bursting_master_saved_grant = cpu_data_master_saved_grant_custom_dma_burst_2_upstream;

  //custom_dma_burst_2_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_2_upstream_arb_share_counter_next_value = custom_dma_burst_2_upstream_firsttransfer ? (custom_dma_burst_2_upstream_arb_share_set_values - 1) : |custom_dma_burst_2_upstream_arb_share_counter ? (custom_dma_burst_2_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_2_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_2_upstream_allgrants = |custom_dma_burst_2_upstream_grant_vector;

  //custom_dma_burst_2_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_2_upstream_end_xfer = ~(custom_dma_burst_2_upstream_waits_for_read | custom_dma_burst_2_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream = custom_dma_burst_2_upstream_end_xfer & (~custom_dma_burst_2_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_2_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_2_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream & custom_dma_burst_2_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream & ~custom_dma_burst_2_upstream_non_bursting_master_requests);

  //custom_dma_burst_2_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_2_upstream_arb_counter_enable)
          custom_dma_burst_2_upstream_arb_share_counter <= custom_dma_burst_2_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_2_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_2_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_2_upstream & ~custom_dma_burst_2_upstream_non_bursting_master_requests))
          custom_dma_burst_2_upstream_slavearbiterlockenable <= |custom_dma_burst_2_upstream_arb_share_counter_next_value;
    end


  //cpu/data_master custom_dma_burst_2/upstream arbiterlock, which is an e_assign
  assign cpu_data_master_arbiterlock = custom_dma_burst_2_upstream_slavearbiterlockenable & cpu_data_master_continuerequest;

  //custom_dma_burst_2_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_2_upstream_slavearbiterlockenable2 = |custom_dma_burst_2_upstream_arb_share_counter_next_value;

  //cpu/data_master custom_dma_burst_2/upstream arbiterlock2, which is an e_assign
  assign cpu_data_master_arbiterlock2 = custom_dma_burst_2_upstream_slavearbiterlockenable2 & cpu_data_master_continuerequest;

  //custom_dma_burst_2_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_2_upstream_any_continuerequest = 1;

  //cpu_data_master_continuerequest continued request, which is an e_assign
  assign cpu_data_master_continuerequest = 1;

  assign cpu_data_master_qualified_request_custom_dma_burst_2_upstream = cpu_data_master_requests_custom_dma_burst_2_upstream & ~((cpu_data_master_read & ((cpu_data_master_latency_counter != 0) | (1 < cpu_data_master_latency_counter) | (|cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register) | (|cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register))));
  //unique name for custom_dma_burst_2_upstream_move_on_to_next_transaction, which is an e_assign
  assign custom_dma_burst_2_upstream_move_on_to_next_transaction = custom_dma_burst_2_upstream_this_cycle_is_the_last_burst & custom_dma_burst_2_upstream_load_fifo;

  //the currently selected burstcount for custom_dma_burst_2_upstream, which is an e_mux
  assign custom_dma_burst_2_upstream_selected_burstcount = (cpu_data_master_granted_custom_dma_burst_2_upstream)? cpu_data_master_burstcount :
    1;

  //burstcount_fifo_for_custom_dma_burst_2_upstream, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_custom_dma_burst_2_upstream_module burstcount_fifo_for_custom_dma_burst_2_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_2_upstream_selected_burstcount),
      .data_out             (custom_dma_burst_2_upstream_transaction_burst_count),
      .empty                (custom_dma_burst_2_upstream_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (custom_dma_burst_2_upstream_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read & custom_dma_burst_2_upstream_load_fifo & ~(custom_dma_burst_2_upstream_this_cycle_is_the_last_burst & custom_dma_burst_2_upstream_burstcount_fifo_empty))
    );

  //custom_dma_burst_2_upstream current burst minus one, which is an e_assign
  assign custom_dma_burst_2_upstream_current_burst_minus_one = custom_dma_burst_2_upstream_current_burst - 1;

  //what to load in current_burst, for custom_dma_burst_2_upstream, which is an e_mux
  assign custom_dma_burst_2_upstream_next_burst_count = (((in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read) & ~custom_dma_burst_2_upstream_load_fifo))? custom_dma_burst_2_upstream_selected_burstcount :
    ((in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read & custom_dma_burst_2_upstream_this_cycle_is_the_last_burst & custom_dma_burst_2_upstream_burstcount_fifo_empty))? custom_dma_burst_2_upstream_selected_burstcount :
    (custom_dma_burst_2_upstream_this_cycle_is_the_last_burst)? custom_dma_burst_2_upstream_transaction_burst_count :
    custom_dma_burst_2_upstream_current_burst_minus_one;

  //the current burst count for custom_dma_burst_2_upstream, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_current_burst <= 0;
      else if (custom_dma_burst_2_upstream_readdatavalid_from_sa | (~custom_dma_burst_2_upstream_load_fifo & (in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read)))
          custom_dma_burst_2_upstream_current_burst <= custom_dma_burst_2_upstream_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_custom_dma_burst_2_upstream_load_fifo = (~custom_dma_burst_2_upstream_load_fifo)? 1 :
    (((in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read) & custom_dma_burst_2_upstream_load_fifo))? 1 :
    ~custom_dma_burst_2_upstream_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_load_fifo <= 0;
      else if ((in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read) & ~custom_dma_burst_2_upstream_load_fifo | custom_dma_burst_2_upstream_this_cycle_is_the_last_burst)
          custom_dma_burst_2_upstream_load_fifo <= p0_custom_dma_burst_2_upstream_load_fifo;
    end


  //the last cycle in the burst for custom_dma_burst_2_upstream, which is an e_assign
  assign custom_dma_burst_2_upstream_this_cycle_is_the_last_burst = ~(|custom_dma_burst_2_upstream_current_burst_minus_one) & custom_dma_burst_2_upstream_readdatavalid_from_sa;

  //rdv_fifo_for_cpu_data_master_to_custom_dma_burst_2_upstream, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_cpu_data_master_to_custom_dma_burst_2_upstream_module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_2_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (cpu_data_master_granted_custom_dma_burst_2_upstream),
      .data_out             (cpu_data_master_rdv_fifo_output_from_custom_dma_burst_2_upstream),
      .empty                (),
      .fifo_contains_ones_n (cpu_data_master_rdv_fifo_empty_custom_dma_burst_2_upstream),
      .full                 (),
      .read                 (custom_dma_burst_2_upstream_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_2_upstream_waits_for_read)
    );

  assign cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register = ~cpu_data_master_rdv_fifo_empty_custom_dma_burst_2_upstream;
  //local readdatavalid cpu_data_master_read_data_valid_custom_dma_burst_2_upstream, which is an e_mux
  assign cpu_data_master_read_data_valid_custom_dma_burst_2_upstream = custom_dma_burst_2_upstream_readdatavalid_from_sa;

  //custom_dma_burst_2_upstream_writedata mux, which is an e_mux
  assign custom_dma_burst_2_upstream_writedata = cpu_data_master_writedata;

  //byteaddress mux for custom_dma_burst_2/upstream, which is an e_mux
  assign custom_dma_burst_2_upstream_byteaddress = cpu_data_master_address_to_slave;

  //master is always granted when requested
  assign cpu_data_master_granted_custom_dma_burst_2_upstream = cpu_data_master_qualified_request_custom_dma_burst_2_upstream;

  //cpu/data_master saved-grant custom_dma_burst_2/upstream, which is an e_assign
  assign cpu_data_master_saved_grant_custom_dma_burst_2_upstream = cpu_data_master_requests_custom_dma_burst_2_upstream;

  //allow new arb cycle for custom_dma_burst_2/upstream, which is an e_assign
  assign custom_dma_burst_2_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_2_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_2_upstream_master_qreq_vector = 1;

  //custom_dma_burst_2_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_2_upstream_firsttransfer = custom_dma_burst_2_upstream_begins_xfer ? custom_dma_burst_2_upstream_unreg_firsttransfer : custom_dma_burst_2_upstream_reg_firsttransfer;

  //custom_dma_burst_2_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_2_upstream_unreg_firsttransfer = ~(custom_dma_burst_2_upstream_slavearbiterlockenable & custom_dma_burst_2_upstream_any_continuerequest);

  //custom_dma_burst_2_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_2_upstream_begins_xfer)
          custom_dma_burst_2_upstream_reg_firsttransfer <= custom_dma_burst_2_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_2_upstream_next_bbt_burstcount next_bbt_burstcount, which is an e_mux
  assign custom_dma_burst_2_upstream_next_bbt_burstcount = ((((custom_dma_burst_2_upstream_write) && (custom_dma_burst_2_upstream_bbt_burstcounter == 0))))? (custom_dma_burst_2_upstream_burstcount - 1) :
    ((((custom_dma_burst_2_upstream_read) && (custom_dma_burst_2_upstream_bbt_burstcounter == 0))))? 0 :
    (custom_dma_burst_2_upstream_bbt_burstcounter - 1);

  //custom_dma_burst_2_upstream_bbt_burstcounter bbt_burstcounter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_upstream_bbt_burstcounter <= 0;
      else if (custom_dma_burst_2_upstream_begins_xfer)
          custom_dma_burst_2_upstream_bbt_burstcounter <= custom_dma_burst_2_upstream_next_bbt_burstcount;
    end


  //custom_dma_burst_2_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_2_upstream_beginbursttransfer_internal = custom_dma_burst_2_upstream_begins_xfer & (custom_dma_burst_2_upstream_bbt_burstcounter == 0);

  //custom_dma_burst_2_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_2_upstream_read = cpu_data_master_granted_custom_dma_burst_2_upstream & cpu_data_master_read;

  //custom_dma_burst_2_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_2_upstream_write = cpu_data_master_granted_custom_dma_burst_2_upstream & cpu_data_master_write;

  //custom_dma_burst_2_upstream_address mux, which is an e_mux
  assign custom_dma_burst_2_upstream_address = cpu_data_master_address_to_slave;

  //d1_custom_dma_burst_2_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_2_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_2_upstream_end_xfer <= custom_dma_burst_2_upstream_end_xfer;
    end


  //custom_dma_burst_2_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_2_upstream_waits_for_read = custom_dma_burst_2_upstream_in_a_read_cycle & custom_dma_burst_2_upstream_waitrequest_from_sa;

  //custom_dma_burst_2_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_2_upstream_in_a_read_cycle = cpu_data_master_granted_custom_dma_burst_2_upstream & cpu_data_master_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_2_upstream_in_a_read_cycle;

  //custom_dma_burst_2_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_2_upstream_waits_for_write = custom_dma_burst_2_upstream_in_a_write_cycle & custom_dma_burst_2_upstream_waitrequest_from_sa;

  //custom_dma_burst_2_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_2_upstream_in_a_write_cycle = cpu_data_master_granted_custom_dma_burst_2_upstream & cpu_data_master_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_2_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_2_upstream_counter = 0;
  //custom_dma_burst_2_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_2_upstream_byteenable = (cpu_data_master_granted_custom_dma_burst_2_upstream)? cpu_data_master_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign custom_dma_burst_2_upstream_burstcount = (cpu_data_master_granted_custom_dma_burst_2_upstream)? cpu_data_master_burstcount :
    1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_2_upstream_debugaccess = (cpu_data_master_granted_custom_dma_burst_2_upstream)? cpu_data_master_debugaccess :
    0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_2/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //cpu/data_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (cpu_data_master_requests_custom_dma_burst_2_upstream && (cpu_data_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: cpu/data_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_2/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_2_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_2_downstream_address,
                                                   custom_dma_burst_2_downstream_burstcount,
                                                   custom_dma_burst_2_downstream_byteenable,
                                                   custom_dma_burst_2_downstream_granted_pipeline_bridge_s1,
                                                   custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1,
                                                   custom_dma_burst_2_downstream_read,
                                                   custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1,
                                                   custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register,
                                                   custom_dma_burst_2_downstream_requests_pipeline_bridge_s1,
                                                   custom_dma_burst_2_downstream_write,
                                                   custom_dma_burst_2_downstream_writedata,
                                                   d1_pipeline_bridge_s1_end_xfer,
                                                   pipeline_bridge_s1_readdata_from_sa,
                                                   pipeline_bridge_s1_waitrequest_from_sa,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_2_downstream_address_to_slave,
                                                   custom_dma_burst_2_downstream_latency_counter,
                                                   custom_dma_burst_2_downstream_readdata,
                                                   custom_dma_burst_2_downstream_readdatavalid,
                                                   custom_dma_burst_2_downstream_reset_n,
                                                   custom_dma_burst_2_downstream_waitrequest
                                                )
;

  output  [ 11: 0] custom_dma_burst_2_downstream_address_to_slave;
  output           custom_dma_burst_2_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_2_downstream_readdata;
  output           custom_dma_burst_2_downstream_readdatavalid;
  output           custom_dma_burst_2_downstream_reset_n;
  output           custom_dma_burst_2_downstream_waitrequest;
  input            clk;
  input   [ 11: 0] custom_dma_burst_2_downstream_address;
  input            custom_dma_burst_2_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_2_downstream_byteenable;
  input            custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;
  input            custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1;
  input            custom_dma_burst_2_downstream_read;
  input            custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1;
  input            custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  input            custom_dma_burst_2_downstream_requests_pipeline_bridge_s1;
  input            custom_dma_burst_2_downstream_write;
  input   [ 31: 0] custom_dma_burst_2_downstream_writedata;
  input            d1_pipeline_bridge_s1_end_xfer;
  input   [ 31: 0] pipeline_bridge_s1_readdata_from_sa;
  input            pipeline_bridge_s1_waitrequest_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 11: 0] custom_dma_burst_2_downstream_address_last_time;
  wire    [ 11: 0] custom_dma_burst_2_downstream_address_to_slave;
  reg              custom_dma_burst_2_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_2_downstream_byteenable_last_time;
  wire             custom_dma_burst_2_downstream_is_granted_some_slave;
  reg              custom_dma_burst_2_downstream_latency_counter;
  reg              custom_dma_burst_2_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_2_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_2_downstream_readdata;
  wire             custom_dma_burst_2_downstream_readdatavalid;
  wire             custom_dma_burst_2_downstream_reset_n;
  wire             custom_dma_burst_2_downstream_run;
  wire             custom_dma_burst_2_downstream_waitrequest;
  reg              custom_dma_burst_2_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_2_downstream_writedata_last_time;
  wire             latency_load_value;
  wire             p1_custom_dma_burst_2_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_2_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1 | ~custom_dma_burst_2_downstream_requests_pipeline_bridge_s1) & (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 | ~custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1) & ((~custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1 | ~(custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write) | (1 & ~pipeline_bridge_s1_waitrequest_from_sa & (custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write)))) & ((~custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1 | ~(custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write) | (1 & ~pipeline_bridge_s1_waitrequest_from_sa & (custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_2_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_2_downstream_address_to_slave = custom_dma_burst_2_downstream_address;

  //custom_dma_burst_2_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_2_downstream_read_but_no_slave_selected <= custom_dma_burst_2_downstream_read & custom_dma_burst_2_downstream_run & ~custom_dma_burst_2_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_2_downstream_is_granted_some_slave = custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_2_downstream_readdatavalid = custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_2_downstream_readdatavalid = custom_dma_burst_2_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_2_downstream_readdatavalid;

  //custom_dma_burst_2/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_2_downstream_readdata = pipeline_bridge_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_2_downstream_waitrequest = ~custom_dma_burst_2_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_2_downstream_latency_counter <= p1_custom_dma_burst_2_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_2_downstream_latency_counter = ((custom_dma_burst_2_downstream_run & custom_dma_burst_2_downstream_read))? latency_load_value :
    (custom_dma_burst_2_downstream_latency_counter)? custom_dma_burst_2_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //custom_dma_burst_2_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_2_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_2_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_address_last_time <= custom_dma_burst_2_downstream_address;
    end


  //custom_dma_burst_2/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_2_downstream_waitrequest & (custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write);
    end


  //custom_dma_burst_2_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_address != custom_dma_burst_2_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_2_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_burstcount_last_time <= custom_dma_burst_2_downstream_burstcount;
    end


  //custom_dma_burst_2_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_burstcount != custom_dma_burst_2_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_2_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_byteenable_last_time <= custom_dma_burst_2_downstream_byteenable;
    end


  //custom_dma_burst_2_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_byteenable != custom_dma_burst_2_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_2_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_read_last_time <= custom_dma_burst_2_downstream_read;
    end


  //custom_dma_burst_2_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_read != custom_dma_burst_2_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_2_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_write_last_time <= custom_dma_burst_2_downstream_write;
    end


  //custom_dma_burst_2_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_write != custom_dma_burst_2_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_2_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_2_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_2_downstream_writedata_last_time <= custom_dma_burst_2_downstream_writedata;
    end


  //custom_dma_burst_2_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_2_downstream_writedata != custom_dma_burst_2_downstream_writedata_last_time) & custom_dma_burst_2_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_2_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_custom_dma_burst_3_upstream_module (
                                                                // inputs:
                                                                 clear_fifo,
                                                                 clk,
                                                                 data_in,
                                                                 read,
                                                                 reset_n,
                                                                 sync_reset,
                                                                 write,

                                                                // outputs:
                                                                 data_out,
                                                                 empty,
                                                                 fifo_contains_ones_n,
                                                                 full
                                                              )
;

  output  [  3: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  3: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  3: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  reg              full_16;
  reg              full_17;
  wire             full_18;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  3: 0] p0_stage_0;
  wire             p10_full_10;
  wire    [  3: 0] p10_stage_10;
  wire             p11_full_11;
  wire    [  3: 0] p11_stage_11;
  wire             p12_full_12;
  wire    [  3: 0] p12_stage_12;
  wire             p13_full_13;
  wire    [  3: 0] p13_stage_13;
  wire             p14_full_14;
  wire    [  3: 0] p14_stage_14;
  wire             p15_full_15;
  wire    [  3: 0] p15_stage_15;
  wire             p16_full_16;
  wire    [  3: 0] p16_stage_16;
  wire             p17_full_17;
  wire    [  3: 0] p17_stage_17;
  wire             p1_full_1;
  wire    [  3: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  3: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  3: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  3: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  3: 0] p5_stage_5;
  wire             p6_full_6;
  wire    [  3: 0] p6_stage_6;
  wire             p7_full_7;
  wire    [  3: 0] p7_stage_7;
  wire             p8_full_8;
  wire    [  3: 0] p8_stage_8;
  wire             p9_full_9;
  wire    [  3: 0] p9_stage_9;
  reg     [  3: 0] stage_0;
  reg     [  3: 0] stage_1;
  reg     [  3: 0] stage_10;
  reg     [  3: 0] stage_11;
  reg     [  3: 0] stage_12;
  reg     [  3: 0] stage_13;
  reg     [  3: 0] stage_14;
  reg     [  3: 0] stage_15;
  reg     [  3: 0] stage_16;
  reg     [  3: 0] stage_17;
  reg     [  3: 0] stage_2;
  reg     [  3: 0] stage_3;
  reg     [  3: 0] stage_4;
  reg     [  3: 0] stage_5;
  reg     [  3: 0] stage_6;
  reg     [  3: 0] stage_7;
  reg     [  3: 0] stage_8;
  reg     [  3: 0] stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_17;
  assign empty = !full_0;
  assign full_18 = 0;
  //data_17, which is an e_mux
  assign p17_stage_17 = ((full_18 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_17 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_17))
          if (sync_reset & full_17 & !((full_18 == 0) & read & write))
              stage_17 <= 0;
          else 
            stage_17 <= p17_stage_17;
    end


  //control_17, which is an e_mux
  assign p17_full_17 = ((read & !write) == 0)? full_16 :
    0;

  //control_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_17 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_17 <= 0;
          else 
            full_17 <= p17_full_17;
    end


  //data_16, which is an e_mux
  assign p16_stage_16 = ((full_17 & ~clear_fifo) == 0)? data_in :
    stage_17;

  //data_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_16 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_16))
          if (sync_reset & full_16 & !((full_17 == 0) & read & write))
              stage_16 <= 0;
          else 
            stage_16 <= p16_stage_16;
    end


  //control_16, which is an e_mux
  assign p16_full_16 = ((read & !write) == 0)? full_15 :
    full_17;

  //control_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_16 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_16 <= 0;
          else 
            full_16 <= p16_full_16;
    end


  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    stage_16;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    full_16;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_3_upstream_module (
                                                                                   // inputs:
                                                                                    clear_fifo,
                                                                                    clk,
                                                                                    data_in,
                                                                                    read,
                                                                                    reset_n,
                                                                                    sync_reset,
                                                                                    write,

                                                                                   // outputs:
                                                                                    data_out,
                                                                                    empty,
                                                                                    fifo_contains_ones_n,
                                                                                    full
                                                                                 )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  reg              full_16;
  reg              full_17;
  wire             full_18;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p10_full_10;
  wire             p10_stage_10;
  wire             p11_full_11;
  wire             p11_stage_11;
  wire             p12_full_12;
  wire             p12_stage_12;
  wire             p13_full_13;
  wire             p13_stage_13;
  wire             p14_full_14;
  wire             p14_stage_14;
  wire             p15_full_15;
  wire             p15_stage_15;
  wire             p16_full_16;
  wire             p16_stage_16;
  wire             p17_full_17;
  wire             p17_stage_17;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  wire             p6_full_6;
  wire             p6_stage_6;
  wire             p7_full_7;
  wire             p7_stage_7;
  wire             p8_full_8;
  wire             p8_stage_8;
  wire             p9_full_9;
  wire             p9_stage_9;
  reg              stage_0;
  reg              stage_1;
  reg              stage_10;
  reg              stage_11;
  reg              stage_12;
  reg              stage_13;
  reg              stage_14;
  reg              stage_15;
  reg              stage_16;
  reg              stage_17;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  reg              stage_6;
  reg              stage_7;
  reg              stage_8;
  reg              stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_17;
  assign empty = !full_0;
  assign full_18 = 0;
  //data_17, which is an e_mux
  assign p17_stage_17 = ((full_18 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_17 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_17))
          if (sync_reset & full_17 & !((full_18 == 0) & read & write))
              stage_17 <= 0;
          else 
            stage_17 <= p17_stage_17;
    end


  //control_17, which is an e_mux
  assign p17_full_17 = ((read & !write) == 0)? full_16 :
    0;

  //control_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_17 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_17 <= 0;
          else 
            full_17 <= p17_full_17;
    end


  //data_16, which is an e_mux
  assign p16_stage_16 = ((full_17 & ~clear_fifo) == 0)? data_in :
    stage_17;

  //data_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_16 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_16))
          if (sync_reset & full_16 & !((full_17 == 0) & read & write))
              stage_16 <= 0;
          else 
            stage_16 <= p16_stage_16;
    end


  //control_16, which is an e_mux
  assign p16_full_16 = ((read & !write) == 0)? full_15 :
    full_17;

  //control_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_16 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_16 <= 0;
          else 
            full_16 <= p16_full_16;
    end


  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    stage_16;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    full_16;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_3_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 cpu_instruction_master_address_to_slave,
                                                 cpu_instruction_master_burstcount,
                                                 cpu_instruction_master_latency_counter,
                                                 cpu_instruction_master_read,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register,
                                                 custom_dma_burst_3_upstream_readdata,
                                                 custom_dma_burst_3_upstream_readdatavalid,
                                                 custom_dma_burst_3_upstream_waitrequest,
                                                 reset_n,

                                                // outputs:
                                                 cpu_instruction_master_granted_custom_dma_burst_3_upstream,
                                                 cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream,
                                                 cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register,
                                                 cpu_instruction_master_requests_custom_dma_burst_3_upstream,
                                                 custom_dma_burst_3_upstream_address,
                                                 custom_dma_burst_3_upstream_byteaddress,
                                                 custom_dma_burst_3_upstream_byteenable,
                                                 custom_dma_burst_3_upstream_debugaccess,
                                                 custom_dma_burst_3_upstream_read,
                                                 custom_dma_burst_3_upstream_readdata_from_sa,
                                                 custom_dma_burst_3_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_3_upstream_write,
                                                 d1_custom_dma_burst_3_upstream_end_xfer
                                              )
;

  output           cpu_instruction_master_granted_custom_dma_burst_3_upstream;
  output           cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream;
  output           cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream;
  output           cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register;
  output           cpu_instruction_master_requests_custom_dma_burst_3_upstream;
  output  [ 24: 0] custom_dma_burst_3_upstream_address;
  output  [ 26: 0] custom_dma_burst_3_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_3_upstream_byteenable;
  output           custom_dma_burst_3_upstream_debugaccess;
  output           custom_dma_burst_3_upstream_read;
  output  [ 31: 0] custom_dma_burst_3_upstream_readdata_from_sa;
  output           custom_dma_burst_3_upstream_waitrequest_from_sa;
  output           custom_dma_burst_3_upstream_write;
  output           d1_custom_dma_burst_3_upstream_end_xfer;
  input            clk;
  input   [ 26: 0] cpu_instruction_master_address_to_slave;
  input   [  3: 0] cpu_instruction_master_burstcount;
  input            cpu_instruction_master_latency_counter;
  input            cpu_instruction_master_read;
  input            cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register;
  input   [ 31: 0] custom_dma_burst_3_upstream_readdata;
  input            custom_dma_burst_3_upstream_readdatavalid;
  input            custom_dma_burst_3_upstream_waitrequest;
  input            reset_n;

  wire             cpu_instruction_master_arbiterlock;
  wire             cpu_instruction_master_arbiterlock2;
  wire             cpu_instruction_master_continuerequest;
  wire             cpu_instruction_master_granted_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_rdv_fifo_output_from_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register;
  wire             cpu_instruction_master_requests_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_saved_grant_custom_dma_burst_3_upstream;
  wire    [ 24: 0] custom_dma_burst_3_upstream_address;
  wire             custom_dma_burst_3_upstream_allgrants;
  wire             custom_dma_burst_3_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_3_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_3_upstream_any_continuerequest;
  wire             custom_dma_burst_3_upstream_arb_counter_enable;
  reg     [  3: 0] custom_dma_burst_3_upstream_arb_share_counter;
  wire    [  3: 0] custom_dma_burst_3_upstream_arb_share_counter_next_value;
  wire    [  3: 0] custom_dma_burst_3_upstream_arb_share_set_values;
  wire             custom_dma_burst_3_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_3_upstream_begins_xfer;
  wire             custom_dma_burst_3_upstream_burstcount_fifo_empty;
  wire    [ 26: 0] custom_dma_burst_3_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_3_upstream_byteenable;
  reg     [  3: 0] custom_dma_burst_3_upstream_current_burst;
  wire    [  3: 0] custom_dma_burst_3_upstream_current_burst_minus_one;
  wire             custom_dma_burst_3_upstream_debugaccess;
  wire             custom_dma_burst_3_upstream_end_xfer;
  wire             custom_dma_burst_3_upstream_firsttransfer;
  wire             custom_dma_burst_3_upstream_grant_vector;
  wire             custom_dma_burst_3_upstream_in_a_read_cycle;
  wire             custom_dma_burst_3_upstream_in_a_write_cycle;
  reg              custom_dma_burst_3_upstream_load_fifo;
  wire             custom_dma_burst_3_upstream_master_qreq_vector;
  wire             custom_dma_burst_3_upstream_move_on_to_next_transaction;
  wire    [  3: 0] custom_dma_burst_3_upstream_next_burst_count;
  wire             custom_dma_burst_3_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_3_upstream_read;
  wire    [ 31: 0] custom_dma_burst_3_upstream_readdata_from_sa;
  wire             custom_dma_burst_3_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_3_upstream_reg_firsttransfer;
  wire    [  3: 0] custom_dma_burst_3_upstream_selected_burstcount;
  reg              custom_dma_burst_3_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_3_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_3_upstream_this_cycle_is_the_last_burst;
  wire    [  3: 0] custom_dma_burst_3_upstream_transaction_burst_count;
  wire             custom_dma_burst_3_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_3_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_3_upstream_waits_for_read;
  wire             custom_dma_burst_3_upstream_waits_for_write;
  wire             custom_dma_burst_3_upstream_write;
  reg              d1_custom_dma_burst_3_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p0_custom_dma_burst_3_upstream_load_fifo;
  wire             wait_for_custom_dma_burst_3_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_3_upstream_end_xfer;
    end


  assign custom_dma_burst_3_upstream_begins_xfer = ~d1_reasons_to_wait & ((cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream));
  //assign custom_dma_burst_3_upstream_readdatavalid_from_sa = custom_dma_burst_3_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_3_upstream_readdatavalid_from_sa = custom_dma_burst_3_upstream_readdatavalid;

  //assign custom_dma_burst_3_upstream_readdata_from_sa = custom_dma_burst_3_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_3_upstream_readdata_from_sa = custom_dma_burst_3_upstream_readdata;

  assign cpu_instruction_master_requests_custom_dma_burst_3_upstream = (({cpu_instruction_master_address_to_slave[26 : 25] , 25'b0} == 27'h2000000) & (cpu_instruction_master_read)) & cpu_instruction_master_read;
  //assign custom_dma_burst_3_upstream_waitrequest_from_sa = custom_dma_burst_3_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_3_upstream_waitrequest_from_sa = custom_dma_burst_3_upstream_waitrequest;

  //custom_dma_burst_3_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_3_upstream_arb_share_set_values = 1;

  //custom_dma_burst_3_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_3_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_3_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_3_upstream_any_bursting_master_saved_grant = cpu_instruction_master_saved_grant_custom_dma_burst_3_upstream;

  //custom_dma_burst_3_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_3_upstream_arb_share_counter_next_value = custom_dma_burst_3_upstream_firsttransfer ? (custom_dma_burst_3_upstream_arb_share_set_values - 1) : |custom_dma_burst_3_upstream_arb_share_counter ? (custom_dma_burst_3_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_3_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_3_upstream_allgrants = |custom_dma_burst_3_upstream_grant_vector;

  //custom_dma_burst_3_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_3_upstream_end_xfer = ~(custom_dma_burst_3_upstream_waits_for_read | custom_dma_burst_3_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream = custom_dma_burst_3_upstream_end_xfer & (~custom_dma_burst_3_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_3_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_3_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream & custom_dma_burst_3_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream & ~custom_dma_burst_3_upstream_non_bursting_master_requests);

  //custom_dma_burst_3_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_3_upstream_arb_counter_enable)
          custom_dma_burst_3_upstream_arb_share_counter <= custom_dma_burst_3_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_3_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_3_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_3_upstream & ~custom_dma_burst_3_upstream_non_bursting_master_requests))
          custom_dma_burst_3_upstream_slavearbiterlockenable <= |custom_dma_burst_3_upstream_arb_share_counter_next_value;
    end


  //cpu/instruction_master custom_dma_burst_3/upstream arbiterlock, which is an e_assign
  assign cpu_instruction_master_arbiterlock = custom_dma_burst_3_upstream_slavearbiterlockenable & cpu_instruction_master_continuerequest;

  //custom_dma_burst_3_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_3_upstream_slavearbiterlockenable2 = |custom_dma_burst_3_upstream_arb_share_counter_next_value;

  //cpu/instruction_master custom_dma_burst_3/upstream arbiterlock2, which is an e_assign
  assign cpu_instruction_master_arbiterlock2 = custom_dma_burst_3_upstream_slavearbiterlockenable2 & cpu_instruction_master_continuerequest;

  //custom_dma_burst_3_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_3_upstream_any_continuerequest = 1;

  //cpu_instruction_master_continuerequest continued request, which is an e_assign
  assign cpu_instruction_master_continuerequest = 1;

  assign cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream = cpu_instruction_master_requests_custom_dma_burst_3_upstream & ~((cpu_instruction_master_read & ((cpu_instruction_master_latency_counter != 0) | (1 < cpu_instruction_master_latency_counter) | (|cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register))));
  //unique name for custom_dma_burst_3_upstream_move_on_to_next_transaction, which is an e_assign
  assign custom_dma_burst_3_upstream_move_on_to_next_transaction = custom_dma_burst_3_upstream_this_cycle_is_the_last_burst & custom_dma_burst_3_upstream_load_fifo;

  //the currently selected burstcount for custom_dma_burst_3_upstream, which is an e_mux
  assign custom_dma_burst_3_upstream_selected_burstcount = (cpu_instruction_master_granted_custom_dma_burst_3_upstream)? cpu_instruction_master_burstcount :
    1;

  //burstcount_fifo_for_custom_dma_burst_3_upstream, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_custom_dma_burst_3_upstream_module burstcount_fifo_for_custom_dma_burst_3_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_3_upstream_selected_burstcount),
      .data_out             (custom_dma_burst_3_upstream_transaction_burst_count),
      .empty                (custom_dma_burst_3_upstream_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (custom_dma_burst_3_upstream_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read & custom_dma_burst_3_upstream_load_fifo & ~(custom_dma_burst_3_upstream_this_cycle_is_the_last_burst & custom_dma_burst_3_upstream_burstcount_fifo_empty))
    );

  //custom_dma_burst_3_upstream current burst minus one, which is an e_assign
  assign custom_dma_burst_3_upstream_current_burst_minus_one = custom_dma_burst_3_upstream_current_burst - 1;

  //what to load in current_burst, for custom_dma_burst_3_upstream, which is an e_mux
  assign custom_dma_burst_3_upstream_next_burst_count = (((in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read) & ~custom_dma_burst_3_upstream_load_fifo))? custom_dma_burst_3_upstream_selected_burstcount :
    ((in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read & custom_dma_burst_3_upstream_this_cycle_is_the_last_burst & custom_dma_burst_3_upstream_burstcount_fifo_empty))? custom_dma_burst_3_upstream_selected_burstcount :
    (custom_dma_burst_3_upstream_this_cycle_is_the_last_burst)? custom_dma_burst_3_upstream_transaction_burst_count :
    custom_dma_burst_3_upstream_current_burst_minus_one;

  //the current burst count for custom_dma_burst_3_upstream, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_upstream_current_burst <= 0;
      else if (custom_dma_burst_3_upstream_readdatavalid_from_sa | (~custom_dma_burst_3_upstream_load_fifo & (in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read)))
          custom_dma_burst_3_upstream_current_burst <= custom_dma_burst_3_upstream_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_custom_dma_burst_3_upstream_load_fifo = (~custom_dma_burst_3_upstream_load_fifo)? 1 :
    (((in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read) & custom_dma_burst_3_upstream_load_fifo))? 1 :
    ~custom_dma_burst_3_upstream_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_upstream_load_fifo <= 0;
      else if ((in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read) & ~custom_dma_burst_3_upstream_load_fifo | custom_dma_burst_3_upstream_this_cycle_is_the_last_burst)
          custom_dma_burst_3_upstream_load_fifo <= p0_custom_dma_burst_3_upstream_load_fifo;
    end


  //the last cycle in the burst for custom_dma_burst_3_upstream, which is an e_assign
  assign custom_dma_burst_3_upstream_this_cycle_is_the_last_burst = ~(|custom_dma_burst_3_upstream_current_burst_minus_one) & custom_dma_burst_3_upstream_readdatavalid_from_sa;

  //rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_3_upstream, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_3_upstream_module rdv_fifo_for_cpu_instruction_master_to_custom_dma_burst_3_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (cpu_instruction_master_granted_custom_dma_burst_3_upstream),
      .data_out             (cpu_instruction_master_rdv_fifo_output_from_custom_dma_burst_3_upstream),
      .empty                (),
      .fifo_contains_ones_n (cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_3_upstream),
      .full                 (),
      .read                 (custom_dma_burst_3_upstream_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_3_upstream_waits_for_read)
    );

  assign cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register = ~cpu_instruction_master_rdv_fifo_empty_custom_dma_burst_3_upstream;
  //local readdatavalid cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream, which is an e_mux
  assign cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream = custom_dma_burst_3_upstream_readdatavalid_from_sa;

  //byteaddress mux for custom_dma_burst_3/upstream, which is an e_mux
  assign custom_dma_burst_3_upstream_byteaddress = cpu_instruction_master_address_to_slave;

  //master is always granted when requested
  assign cpu_instruction_master_granted_custom_dma_burst_3_upstream = cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream;

  //cpu/instruction_master saved-grant custom_dma_burst_3/upstream, which is an e_assign
  assign cpu_instruction_master_saved_grant_custom_dma_burst_3_upstream = cpu_instruction_master_requests_custom_dma_burst_3_upstream;

  //allow new arb cycle for custom_dma_burst_3/upstream, which is an e_assign
  assign custom_dma_burst_3_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_3_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_3_upstream_master_qreq_vector = 1;

  //custom_dma_burst_3_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_3_upstream_firsttransfer = custom_dma_burst_3_upstream_begins_xfer ? custom_dma_burst_3_upstream_unreg_firsttransfer : custom_dma_burst_3_upstream_reg_firsttransfer;

  //custom_dma_burst_3_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_3_upstream_unreg_firsttransfer = ~(custom_dma_burst_3_upstream_slavearbiterlockenable & custom_dma_burst_3_upstream_any_continuerequest);

  //custom_dma_burst_3_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_3_upstream_begins_xfer)
          custom_dma_burst_3_upstream_reg_firsttransfer <= custom_dma_burst_3_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_3_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_3_upstream_beginbursttransfer_internal = custom_dma_burst_3_upstream_begins_xfer;

  //custom_dma_burst_3_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_3_upstream_read = cpu_instruction_master_granted_custom_dma_burst_3_upstream & cpu_instruction_master_read;

  //custom_dma_burst_3_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_3_upstream_write = 0;

  //custom_dma_burst_3_upstream_address mux, which is an e_mux
  assign custom_dma_burst_3_upstream_address = cpu_instruction_master_address_to_slave;

  //d1_custom_dma_burst_3_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_3_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_3_upstream_end_xfer <= custom_dma_burst_3_upstream_end_xfer;
    end


  //custom_dma_burst_3_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_3_upstream_waits_for_read = custom_dma_burst_3_upstream_in_a_read_cycle & custom_dma_burst_3_upstream_waitrequest_from_sa;

  //custom_dma_burst_3_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_3_upstream_in_a_read_cycle = cpu_instruction_master_granted_custom_dma_burst_3_upstream & cpu_instruction_master_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_3_upstream_in_a_read_cycle;

  //custom_dma_burst_3_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_3_upstream_waits_for_write = custom_dma_burst_3_upstream_in_a_write_cycle & custom_dma_burst_3_upstream_waitrequest_from_sa;

  //custom_dma_burst_3_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_3_upstream_in_a_write_cycle = 0;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_3_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_3_upstream_counter = 0;
  //custom_dma_burst_3_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_3_upstream_byteenable = -1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_3_upstream_debugaccess = 0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_3/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //cpu/instruction_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (cpu_instruction_master_requests_custom_dma_burst_3_upstream && (cpu_instruction_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: cpu/instruction_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_3/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_3_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_3_downstream_address,
                                                   custom_dma_burst_3_downstream_burstcount,
                                                   custom_dma_burst_3_downstream_byteenable,
                                                   custom_dma_burst_3_downstream_granted_ddr_sdram_s1,
                                                   custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1,
                                                   custom_dma_burst_3_downstream_read,
                                                   custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1,
                                                   custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                                   custom_dma_burst_3_downstream_requests_ddr_sdram_s1,
                                                   custom_dma_burst_3_downstream_write,
                                                   custom_dma_burst_3_downstream_writedata,
                                                   d1_ddr_sdram_s1_end_xfer,
                                                   ddr_sdram_s1_readdata_from_sa,
                                                   ddr_sdram_s1_waitrequest_n_from_sa,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_3_downstream_address_to_slave,
                                                   custom_dma_burst_3_downstream_latency_counter,
                                                   custom_dma_burst_3_downstream_readdata,
                                                   custom_dma_burst_3_downstream_readdatavalid,
                                                   custom_dma_burst_3_downstream_reset_n,
                                                   custom_dma_burst_3_downstream_waitrequest
                                                )
;

  output  [ 24: 0] custom_dma_burst_3_downstream_address_to_slave;
  output           custom_dma_burst_3_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_3_downstream_readdata;
  output           custom_dma_burst_3_downstream_readdatavalid;
  output           custom_dma_burst_3_downstream_reset_n;
  output           custom_dma_burst_3_downstream_waitrequest;
  input            clk;
  input   [ 24: 0] custom_dma_burst_3_downstream_address;
  input   [  2: 0] custom_dma_burst_3_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_3_downstream_byteenable;
  input            custom_dma_burst_3_downstream_granted_ddr_sdram_s1;
  input            custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1;
  input            custom_dma_burst_3_downstream_read;
  input            custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1;
  input            custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  input            custom_dma_burst_3_downstream_requests_ddr_sdram_s1;
  input            custom_dma_burst_3_downstream_write;
  input   [ 31: 0] custom_dma_burst_3_downstream_writedata;
  input            d1_ddr_sdram_s1_end_xfer;
  input   [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  input            ddr_sdram_s1_waitrequest_n_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 24: 0] custom_dma_burst_3_downstream_address_last_time;
  wire    [ 24: 0] custom_dma_burst_3_downstream_address_to_slave;
  reg     [  2: 0] custom_dma_burst_3_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_3_downstream_byteenable_last_time;
  wire             custom_dma_burst_3_downstream_is_granted_some_slave;
  reg              custom_dma_burst_3_downstream_latency_counter;
  reg              custom_dma_burst_3_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_3_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_3_downstream_readdata;
  wire             custom_dma_burst_3_downstream_readdatavalid;
  wire             custom_dma_burst_3_downstream_reset_n;
  wire             custom_dma_burst_3_downstream_run;
  wire             custom_dma_burst_3_downstream_waitrequest;
  reg              custom_dma_burst_3_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_3_downstream_writedata_last_time;
  wire             latency_load_value;
  wire             p1_custom_dma_burst_3_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_3_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1 | ~custom_dma_burst_3_downstream_requests_ddr_sdram_s1) & (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 | ~custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1) & ((~custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write)))) & ((~custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_3_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_3_downstream_address_to_slave = custom_dma_burst_3_downstream_address;

  //custom_dma_burst_3_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_3_downstream_read_but_no_slave_selected <= custom_dma_burst_3_downstream_read & custom_dma_burst_3_downstream_run & ~custom_dma_burst_3_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_3_downstream_is_granted_some_slave = custom_dma_burst_3_downstream_granted_ddr_sdram_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_3_downstream_readdatavalid = custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_3_downstream_readdatavalid = custom_dma_burst_3_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_3_downstream_readdatavalid;

  //custom_dma_burst_3/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_3_downstream_readdata = ddr_sdram_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_3_downstream_waitrequest = ~custom_dma_burst_3_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_3_downstream_latency_counter <= p1_custom_dma_burst_3_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_3_downstream_latency_counter = ((custom_dma_burst_3_downstream_run & custom_dma_burst_3_downstream_read))? latency_load_value :
    (custom_dma_burst_3_downstream_latency_counter)? custom_dma_burst_3_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //custom_dma_burst_3_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_3_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_3_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_address_last_time <= custom_dma_burst_3_downstream_address;
    end


  //custom_dma_burst_3/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_3_downstream_waitrequest & (custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write);
    end


  //custom_dma_burst_3_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_address != custom_dma_burst_3_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_3_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_burstcount_last_time <= custom_dma_burst_3_downstream_burstcount;
    end


  //custom_dma_burst_3_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_burstcount != custom_dma_burst_3_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_3_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_byteenable_last_time <= custom_dma_burst_3_downstream_byteenable;
    end


  //custom_dma_burst_3_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_byteenable != custom_dma_burst_3_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_3_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_read_last_time <= custom_dma_burst_3_downstream_read;
    end


  //custom_dma_burst_3_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_read != custom_dma_burst_3_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_3_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_write_last_time <= custom_dma_burst_3_downstream_write;
    end


  //custom_dma_burst_3_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_write != custom_dma_burst_3_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_3_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_3_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_3_downstream_writedata_last_time <= custom_dma_burst_3_downstream_writedata;
    end


  //custom_dma_burst_3_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_3_downstream_writedata != custom_dma_burst_3_downstream_writedata_last_time) & custom_dma_burst_3_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_3_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_custom_dma_burst_4_upstream_module (
                                                                // inputs:
                                                                 clear_fifo,
                                                                 clk,
                                                                 data_in,
                                                                 read,
                                                                 reset_n,
                                                                 sync_reset,
                                                                 write,

                                                                // outputs:
                                                                 data_out,
                                                                 empty,
                                                                 fifo_contains_ones_n,
                                                                 full
                                                              )
;

  output  [  3: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  3: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  3: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  reg              full_16;
  reg              full_17;
  wire             full_18;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  3: 0] p0_stage_0;
  wire             p10_full_10;
  wire    [  3: 0] p10_stage_10;
  wire             p11_full_11;
  wire    [  3: 0] p11_stage_11;
  wire             p12_full_12;
  wire    [  3: 0] p12_stage_12;
  wire             p13_full_13;
  wire    [  3: 0] p13_stage_13;
  wire             p14_full_14;
  wire    [  3: 0] p14_stage_14;
  wire             p15_full_15;
  wire    [  3: 0] p15_stage_15;
  wire             p16_full_16;
  wire    [  3: 0] p16_stage_16;
  wire             p17_full_17;
  wire    [  3: 0] p17_stage_17;
  wire             p1_full_1;
  wire    [  3: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  3: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  3: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  3: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  3: 0] p5_stage_5;
  wire             p6_full_6;
  wire    [  3: 0] p6_stage_6;
  wire             p7_full_7;
  wire    [  3: 0] p7_stage_7;
  wire             p8_full_8;
  wire    [  3: 0] p8_stage_8;
  wire             p9_full_9;
  wire    [  3: 0] p9_stage_9;
  reg     [  3: 0] stage_0;
  reg     [  3: 0] stage_1;
  reg     [  3: 0] stage_10;
  reg     [  3: 0] stage_11;
  reg     [  3: 0] stage_12;
  reg     [  3: 0] stage_13;
  reg     [  3: 0] stage_14;
  reg     [  3: 0] stage_15;
  reg     [  3: 0] stage_16;
  reg     [  3: 0] stage_17;
  reg     [  3: 0] stage_2;
  reg     [  3: 0] stage_3;
  reg     [  3: 0] stage_4;
  reg     [  3: 0] stage_5;
  reg     [  3: 0] stage_6;
  reg     [  3: 0] stage_7;
  reg     [  3: 0] stage_8;
  reg     [  3: 0] stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_17;
  assign empty = !full_0;
  assign full_18 = 0;
  //data_17, which is an e_mux
  assign p17_stage_17 = ((full_18 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_17 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_17))
          if (sync_reset & full_17 & !((full_18 == 0) & read & write))
              stage_17 <= 0;
          else 
            stage_17 <= p17_stage_17;
    end


  //control_17, which is an e_mux
  assign p17_full_17 = ((read & !write) == 0)? full_16 :
    0;

  //control_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_17 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_17 <= 0;
          else 
            full_17 <= p17_full_17;
    end


  //data_16, which is an e_mux
  assign p16_stage_16 = ((full_17 & ~clear_fifo) == 0)? data_in :
    stage_17;

  //data_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_16 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_16))
          if (sync_reset & full_16 & !((full_17 == 0) & read & write))
              stage_16 <= 0;
          else 
            stage_16 <= p16_stage_16;
    end


  //control_16, which is an e_mux
  assign p16_full_16 = ((read & !write) == 0)? full_15 :
    full_17;

  //control_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_16 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_16 <= 0;
          else 
            full_16 <= p16_full_16;
    end


  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    stage_16;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    full_16;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_4_upstream_module (
                                                                            // inputs:
                                                                             clear_fifo,
                                                                             clk,
                                                                             data_in,
                                                                             read,
                                                                             reset_n,
                                                                             sync_reset,
                                                                             write,

                                                                            // outputs:
                                                                             data_out,
                                                                             empty,
                                                                             fifo_contains_ones_n,
                                                                             full
                                                                          )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  reg              full_16;
  reg              full_17;
  wire             full_18;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p10_full_10;
  wire             p10_stage_10;
  wire             p11_full_11;
  wire             p11_stage_11;
  wire             p12_full_12;
  wire             p12_stage_12;
  wire             p13_full_13;
  wire             p13_stage_13;
  wire             p14_full_14;
  wire             p14_stage_14;
  wire             p15_full_15;
  wire             p15_stage_15;
  wire             p16_full_16;
  wire             p16_stage_16;
  wire             p17_full_17;
  wire             p17_stage_17;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  wire             p6_full_6;
  wire             p6_stage_6;
  wire             p7_full_7;
  wire             p7_stage_7;
  wire             p8_full_8;
  wire             p8_stage_8;
  wire             p9_full_9;
  wire             p9_stage_9;
  reg              stage_0;
  reg              stage_1;
  reg              stage_10;
  reg              stage_11;
  reg              stage_12;
  reg              stage_13;
  reg              stage_14;
  reg              stage_15;
  reg              stage_16;
  reg              stage_17;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  reg              stage_6;
  reg              stage_7;
  reg              stage_8;
  reg              stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_17;
  assign empty = !full_0;
  assign full_18 = 0;
  //data_17, which is an e_mux
  assign p17_stage_17 = ((full_18 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_17 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_17))
          if (sync_reset & full_17 & !((full_18 == 0) & read & write))
              stage_17 <= 0;
          else 
            stage_17 <= p17_stage_17;
    end


  //control_17, which is an e_mux
  assign p17_full_17 = ((read & !write) == 0)? full_16 :
    0;

  //control_reg_17, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_17 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_17 <= 0;
          else 
            full_17 <= p17_full_17;
    end


  //data_16, which is an e_mux
  assign p16_stage_16 = ((full_17 & ~clear_fifo) == 0)? data_in :
    stage_17;

  //data_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_16 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_16))
          if (sync_reset & full_16 & !((full_17 == 0) & read & write))
              stage_16 <= 0;
          else 
            stage_16 <= p16_stage_16;
    end


  //control_16, which is an e_mux
  assign p16_full_16 = ((read & !write) == 0)? full_15 :
    full_17;

  //control_reg_16, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_16 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_16 <= 0;
          else 
            full_16 <= p16_full_16;
    end


  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    stage_16;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    full_16;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_4_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 cpu_data_master_address_to_slave,
                                                 cpu_data_master_burstcount,
                                                 cpu_data_master_byteenable,
                                                 cpu_data_master_debugaccess,
                                                 cpu_data_master_latency_counter,
                                                 cpu_data_master_read,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register,
                                                 cpu_data_master_write,
                                                 cpu_data_master_writedata,
                                                 custom_dma_burst_4_upstream_readdata,
                                                 custom_dma_burst_4_upstream_readdatavalid,
                                                 custom_dma_burst_4_upstream_waitrequest,
                                                 reset_n,

                                                // outputs:
                                                 cpu_data_master_granted_custom_dma_burst_4_upstream,
                                                 cpu_data_master_qualified_request_custom_dma_burst_4_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_4_upstream,
                                                 cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register,
                                                 cpu_data_master_requests_custom_dma_burst_4_upstream,
                                                 custom_dma_burst_4_upstream_address,
                                                 custom_dma_burst_4_upstream_burstcount,
                                                 custom_dma_burst_4_upstream_byteaddress,
                                                 custom_dma_burst_4_upstream_byteenable,
                                                 custom_dma_burst_4_upstream_debugaccess,
                                                 custom_dma_burst_4_upstream_read,
                                                 custom_dma_burst_4_upstream_readdata_from_sa,
                                                 custom_dma_burst_4_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_4_upstream_write,
                                                 custom_dma_burst_4_upstream_writedata,
                                                 d1_custom_dma_burst_4_upstream_end_xfer
                                              )
;

  output           cpu_data_master_granted_custom_dma_burst_4_upstream;
  output           cpu_data_master_qualified_request_custom_dma_burst_4_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_4_upstream;
  output           cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  output           cpu_data_master_requests_custom_dma_burst_4_upstream;
  output  [ 24: 0] custom_dma_burst_4_upstream_address;
  output  [  3: 0] custom_dma_burst_4_upstream_burstcount;
  output  [ 26: 0] custom_dma_burst_4_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_4_upstream_byteenable;
  output           custom_dma_burst_4_upstream_debugaccess;
  output           custom_dma_burst_4_upstream_read;
  output  [ 31: 0] custom_dma_burst_4_upstream_readdata_from_sa;
  output           custom_dma_burst_4_upstream_waitrequest_from_sa;
  output           custom_dma_burst_4_upstream_write;
  output  [ 31: 0] custom_dma_burst_4_upstream_writedata;
  output           d1_custom_dma_burst_4_upstream_end_xfer;
  input            clk;
  input   [ 26: 0] cpu_data_master_address_to_slave;
  input   [  3: 0] cpu_data_master_burstcount;
  input   [  3: 0] cpu_data_master_byteenable;
  input            cpu_data_master_debugaccess;
  input            cpu_data_master_latency_counter;
  input            cpu_data_master_read;
  input            cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  input            cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  input            cpu_data_master_write;
  input   [ 31: 0] cpu_data_master_writedata;
  input   [ 31: 0] custom_dma_burst_4_upstream_readdata;
  input            custom_dma_burst_4_upstream_readdatavalid;
  input            custom_dma_burst_4_upstream_waitrequest;
  input            reset_n;

  wire             cpu_data_master_arbiterlock;
  wire             cpu_data_master_arbiterlock2;
  wire             cpu_data_master_continuerequest;
  wire             cpu_data_master_granted_custom_dma_burst_4_upstream;
  wire             cpu_data_master_qualified_request_custom_dma_burst_4_upstream;
  wire             cpu_data_master_rdv_fifo_empty_custom_dma_burst_4_upstream;
  wire             cpu_data_master_rdv_fifo_output_from_custom_dma_burst_4_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_4_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  wire             cpu_data_master_requests_custom_dma_burst_4_upstream;
  wire             cpu_data_master_saved_grant_custom_dma_burst_4_upstream;
  wire    [ 24: 0] custom_dma_burst_4_upstream_address;
  wire             custom_dma_burst_4_upstream_allgrants;
  wire             custom_dma_burst_4_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_4_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_4_upstream_any_continuerequest;
  wire             custom_dma_burst_4_upstream_arb_counter_enable;
  reg     [  3: 0] custom_dma_burst_4_upstream_arb_share_counter;
  wire    [  3: 0] custom_dma_burst_4_upstream_arb_share_counter_next_value;
  wire    [  3: 0] custom_dma_burst_4_upstream_arb_share_set_values;
  reg     [  2: 0] custom_dma_burst_4_upstream_bbt_burstcounter;
  wire             custom_dma_burst_4_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_4_upstream_begins_xfer;
  wire    [  3: 0] custom_dma_burst_4_upstream_burstcount;
  wire             custom_dma_burst_4_upstream_burstcount_fifo_empty;
  wire    [ 26: 0] custom_dma_burst_4_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_4_upstream_byteenable;
  reg     [  3: 0] custom_dma_burst_4_upstream_current_burst;
  wire    [  3: 0] custom_dma_burst_4_upstream_current_burst_minus_one;
  wire             custom_dma_burst_4_upstream_debugaccess;
  wire             custom_dma_burst_4_upstream_end_xfer;
  wire             custom_dma_burst_4_upstream_firsttransfer;
  wire             custom_dma_burst_4_upstream_grant_vector;
  wire             custom_dma_burst_4_upstream_in_a_read_cycle;
  wire             custom_dma_burst_4_upstream_in_a_write_cycle;
  reg              custom_dma_burst_4_upstream_load_fifo;
  wire             custom_dma_burst_4_upstream_master_qreq_vector;
  wire             custom_dma_burst_4_upstream_move_on_to_next_transaction;
  wire    [  2: 0] custom_dma_burst_4_upstream_next_bbt_burstcount;
  wire    [  3: 0] custom_dma_burst_4_upstream_next_burst_count;
  wire             custom_dma_burst_4_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_4_upstream_read;
  wire    [ 31: 0] custom_dma_burst_4_upstream_readdata_from_sa;
  wire             custom_dma_burst_4_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_4_upstream_reg_firsttransfer;
  wire    [  3: 0] custom_dma_burst_4_upstream_selected_burstcount;
  reg              custom_dma_burst_4_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_4_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_4_upstream_this_cycle_is_the_last_burst;
  wire    [  3: 0] custom_dma_burst_4_upstream_transaction_burst_count;
  wire             custom_dma_burst_4_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_4_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_4_upstream_waits_for_read;
  wire             custom_dma_burst_4_upstream_waits_for_write;
  wire             custom_dma_burst_4_upstream_write;
  wire    [ 31: 0] custom_dma_burst_4_upstream_writedata;
  reg              d1_custom_dma_burst_4_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p0_custom_dma_burst_4_upstream_load_fifo;
  wire             wait_for_custom_dma_burst_4_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_4_upstream_end_xfer;
    end


  assign custom_dma_burst_4_upstream_begins_xfer = ~d1_reasons_to_wait & ((cpu_data_master_qualified_request_custom_dma_burst_4_upstream));
  //assign custom_dma_burst_4_upstream_readdatavalid_from_sa = custom_dma_burst_4_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_4_upstream_readdatavalid_from_sa = custom_dma_burst_4_upstream_readdatavalid;

  //assign custom_dma_burst_4_upstream_readdata_from_sa = custom_dma_burst_4_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_4_upstream_readdata_from_sa = custom_dma_burst_4_upstream_readdata;

  assign cpu_data_master_requests_custom_dma_burst_4_upstream = ({cpu_data_master_address_to_slave[26 : 25] , 25'b0} == 27'h2000000) & (cpu_data_master_read | cpu_data_master_write);
  //assign custom_dma_burst_4_upstream_waitrequest_from_sa = custom_dma_burst_4_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_4_upstream_waitrequest_from_sa = custom_dma_burst_4_upstream_waitrequest;

  //custom_dma_burst_4_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_4_upstream_arb_share_set_values = (cpu_data_master_granted_custom_dma_burst_4_upstream)? (((cpu_data_master_write) ? cpu_data_master_burstcount : 1)) :
    1;

  //custom_dma_burst_4_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_4_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_4_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_4_upstream_any_bursting_master_saved_grant = cpu_data_master_saved_grant_custom_dma_burst_4_upstream;

  //custom_dma_burst_4_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_4_upstream_arb_share_counter_next_value = custom_dma_burst_4_upstream_firsttransfer ? (custom_dma_burst_4_upstream_arb_share_set_values - 1) : |custom_dma_burst_4_upstream_arb_share_counter ? (custom_dma_burst_4_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_4_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_4_upstream_allgrants = |custom_dma_burst_4_upstream_grant_vector;

  //custom_dma_burst_4_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_4_upstream_end_xfer = ~(custom_dma_burst_4_upstream_waits_for_read | custom_dma_burst_4_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream = custom_dma_burst_4_upstream_end_xfer & (~custom_dma_burst_4_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_4_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_4_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream & custom_dma_burst_4_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream & ~custom_dma_burst_4_upstream_non_bursting_master_requests);

  //custom_dma_burst_4_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_4_upstream_arb_counter_enable)
          custom_dma_burst_4_upstream_arb_share_counter <= custom_dma_burst_4_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_4_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_4_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_4_upstream & ~custom_dma_burst_4_upstream_non_bursting_master_requests))
          custom_dma_burst_4_upstream_slavearbiterlockenable <= |custom_dma_burst_4_upstream_arb_share_counter_next_value;
    end


  //cpu/data_master custom_dma_burst_4/upstream arbiterlock, which is an e_assign
  assign cpu_data_master_arbiterlock = custom_dma_burst_4_upstream_slavearbiterlockenable & cpu_data_master_continuerequest;

  //custom_dma_burst_4_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_4_upstream_slavearbiterlockenable2 = |custom_dma_burst_4_upstream_arb_share_counter_next_value;

  //cpu/data_master custom_dma_burst_4/upstream arbiterlock2, which is an e_assign
  assign cpu_data_master_arbiterlock2 = custom_dma_burst_4_upstream_slavearbiterlockenable2 & cpu_data_master_continuerequest;

  //custom_dma_burst_4_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_4_upstream_any_continuerequest = 1;

  //cpu_data_master_continuerequest continued request, which is an e_assign
  assign cpu_data_master_continuerequest = 1;

  assign cpu_data_master_qualified_request_custom_dma_burst_4_upstream = cpu_data_master_requests_custom_dma_burst_4_upstream & ~((cpu_data_master_read & ((cpu_data_master_latency_counter != 0) | (1 < cpu_data_master_latency_counter) | (|cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register) | (|cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register))));
  //unique name for custom_dma_burst_4_upstream_move_on_to_next_transaction, which is an e_assign
  assign custom_dma_burst_4_upstream_move_on_to_next_transaction = custom_dma_burst_4_upstream_this_cycle_is_the_last_burst & custom_dma_burst_4_upstream_load_fifo;

  //the currently selected burstcount for custom_dma_burst_4_upstream, which is an e_mux
  assign custom_dma_burst_4_upstream_selected_burstcount = (cpu_data_master_granted_custom_dma_burst_4_upstream)? cpu_data_master_burstcount :
    1;

  //burstcount_fifo_for_custom_dma_burst_4_upstream, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_custom_dma_burst_4_upstream_module burstcount_fifo_for_custom_dma_burst_4_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_4_upstream_selected_burstcount),
      .data_out             (custom_dma_burst_4_upstream_transaction_burst_count),
      .empty                (custom_dma_burst_4_upstream_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (custom_dma_burst_4_upstream_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read & custom_dma_burst_4_upstream_load_fifo & ~(custom_dma_burst_4_upstream_this_cycle_is_the_last_burst & custom_dma_burst_4_upstream_burstcount_fifo_empty))
    );

  //custom_dma_burst_4_upstream current burst minus one, which is an e_assign
  assign custom_dma_burst_4_upstream_current_burst_minus_one = custom_dma_burst_4_upstream_current_burst - 1;

  //what to load in current_burst, for custom_dma_burst_4_upstream, which is an e_mux
  assign custom_dma_burst_4_upstream_next_burst_count = (((in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read) & ~custom_dma_burst_4_upstream_load_fifo))? custom_dma_burst_4_upstream_selected_burstcount :
    ((in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read & custom_dma_burst_4_upstream_this_cycle_is_the_last_burst & custom_dma_burst_4_upstream_burstcount_fifo_empty))? custom_dma_burst_4_upstream_selected_burstcount :
    (custom_dma_burst_4_upstream_this_cycle_is_the_last_burst)? custom_dma_burst_4_upstream_transaction_burst_count :
    custom_dma_burst_4_upstream_current_burst_minus_one;

  //the current burst count for custom_dma_burst_4_upstream, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_current_burst <= 0;
      else if (custom_dma_burst_4_upstream_readdatavalid_from_sa | (~custom_dma_burst_4_upstream_load_fifo & (in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read)))
          custom_dma_burst_4_upstream_current_burst <= custom_dma_burst_4_upstream_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_custom_dma_burst_4_upstream_load_fifo = (~custom_dma_burst_4_upstream_load_fifo)? 1 :
    (((in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read) & custom_dma_burst_4_upstream_load_fifo))? 1 :
    ~custom_dma_burst_4_upstream_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_load_fifo <= 0;
      else if ((in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read) & ~custom_dma_burst_4_upstream_load_fifo | custom_dma_burst_4_upstream_this_cycle_is_the_last_burst)
          custom_dma_burst_4_upstream_load_fifo <= p0_custom_dma_burst_4_upstream_load_fifo;
    end


  //the last cycle in the burst for custom_dma_burst_4_upstream, which is an e_assign
  assign custom_dma_burst_4_upstream_this_cycle_is_the_last_burst = ~(|custom_dma_burst_4_upstream_current_burst_minus_one) & custom_dma_burst_4_upstream_readdatavalid_from_sa;

  //rdv_fifo_for_cpu_data_master_to_custom_dma_burst_4_upstream, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_cpu_data_master_to_custom_dma_burst_4_upstream_module rdv_fifo_for_cpu_data_master_to_custom_dma_burst_4_upstream
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (cpu_data_master_granted_custom_dma_burst_4_upstream),
      .data_out             (cpu_data_master_rdv_fifo_output_from_custom_dma_burst_4_upstream),
      .empty                (),
      .fifo_contains_ones_n (cpu_data_master_rdv_fifo_empty_custom_dma_burst_4_upstream),
      .full                 (),
      .read                 (custom_dma_burst_4_upstream_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~custom_dma_burst_4_upstream_waits_for_read)
    );

  assign cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register = ~cpu_data_master_rdv_fifo_empty_custom_dma_burst_4_upstream;
  //local readdatavalid cpu_data_master_read_data_valid_custom_dma_burst_4_upstream, which is an e_mux
  assign cpu_data_master_read_data_valid_custom_dma_burst_4_upstream = custom_dma_burst_4_upstream_readdatavalid_from_sa;

  //custom_dma_burst_4_upstream_writedata mux, which is an e_mux
  assign custom_dma_burst_4_upstream_writedata = cpu_data_master_writedata;

  //byteaddress mux for custom_dma_burst_4/upstream, which is an e_mux
  assign custom_dma_burst_4_upstream_byteaddress = cpu_data_master_address_to_slave;

  //master is always granted when requested
  assign cpu_data_master_granted_custom_dma_burst_4_upstream = cpu_data_master_qualified_request_custom_dma_burst_4_upstream;

  //cpu/data_master saved-grant custom_dma_burst_4/upstream, which is an e_assign
  assign cpu_data_master_saved_grant_custom_dma_burst_4_upstream = cpu_data_master_requests_custom_dma_burst_4_upstream;

  //allow new arb cycle for custom_dma_burst_4/upstream, which is an e_assign
  assign custom_dma_burst_4_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_4_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_4_upstream_master_qreq_vector = 1;

  //custom_dma_burst_4_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_4_upstream_firsttransfer = custom_dma_burst_4_upstream_begins_xfer ? custom_dma_burst_4_upstream_unreg_firsttransfer : custom_dma_burst_4_upstream_reg_firsttransfer;

  //custom_dma_burst_4_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_4_upstream_unreg_firsttransfer = ~(custom_dma_burst_4_upstream_slavearbiterlockenable & custom_dma_burst_4_upstream_any_continuerequest);

  //custom_dma_burst_4_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_4_upstream_begins_xfer)
          custom_dma_burst_4_upstream_reg_firsttransfer <= custom_dma_burst_4_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_4_upstream_next_bbt_burstcount next_bbt_burstcount, which is an e_mux
  assign custom_dma_burst_4_upstream_next_bbt_burstcount = ((((custom_dma_burst_4_upstream_write) && (custom_dma_burst_4_upstream_bbt_burstcounter == 0))))? (custom_dma_burst_4_upstream_burstcount - 1) :
    ((((custom_dma_burst_4_upstream_read) && (custom_dma_burst_4_upstream_bbt_burstcounter == 0))))? 0 :
    (custom_dma_burst_4_upstream_bbt_burstcounter - 1);

  //custom_dma_burst_4_upstream_bbt_burstcounter bbt_burstcounter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_upstream_bbt_burstcounter <= 0;
      else if (custom_dma_burst_4_upstream_begins_xfer)
          custom_dma_burst_4_upstream_bbt_burstcounter <= custom_dma_burst_4_upstream_next_bbt_burstcount;
    end


  //custom_dma_burst_4_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_4_upstream_beginbursttransfer_internal = custom_dma_burst_4_upstream_begins_xfer & (custom_dma_burst_4_upstream_bbt_burstcounter == 0);

  //custom_dma_burst_4_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_4_upstream_read = cpu_data_master_granted_custom_dma_burst_4_upstream & cpu_data_master_read;

  //custom_dma_burst_4_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_4_upstream_write = cpu_data_master_granted_custom_dma_burst_4_upstream & cpu_data_master_write;

  //custom_dma_burst_4_upstream_address mux, which is an e_mux
  assign custom_dma_burst_4_upstream_address = cpu_data_master_address_to_slave;

  //d1_custom_dma_burst_4_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_4_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_4_upstream_end_xfer <= custom_dma_burst_4_upstream_end_xfer;
    end


  //custom_dma_burst_4_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_4_upstream_waits_for_read = custom_dma_burst_4_upstream_in_a_read_cycle & custom_dma_burst_4_upstream_waitrequest_from_sa;

  //custom_dma_burst_4_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_4_upstream_in_a_read_cycle = cpu_data_master_granted_custom_dma_burst_4_upstream & cpu_data_master_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_4_upstream_in_a_read_cycle;

  //custom_dma_burst_4_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_4_upstream_waits_for_write = custom_dma_burst_4_upstream_in_a_write_cycle & custom_dma_burst_4_upstream_waitrequest_from_sa;

  //custom_dma_burst_4_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_4_upstream_in_a_write_cycle = cpu_data_master_granted_custom_dma_burst_4_upstream & cpu_data_master_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_4_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_4_upstream_counter = 0;
  //custom_dma_burst_4_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_4_upstream_byteenable = (cpu_data_master_granted_custom_dma_burst_4_upstream)? cpu_data_master_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign custom_dma_burst_4_upstream_burstcount = (cpu_data_master_granted_custom_dma_burst_4_upstream)? cpu_data_master_burstcount :
    1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_4_upstream_debugaccess = (cpu_data_master_granted_custom_dma_burst_4_upstream)? cpu_data_master_debugaccess :
    0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_4/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //cpu/data_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (cpu_data_master_requests_custom_dma_burst_4_upstream && (cpu_data_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: cpu/data_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_4/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_4_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_4_downstream_address,
                                                   custom_dma_burst_4_downstream_burstcount,
                                                   custom_dma_burst_4_downstream_byteenable,
                                                   custom_dma_burst_4_downstream_granted_ddr_sdram_s1,
                                                   custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1,
                                                   custom_dma_burst_4_downstream_read,
                                                   custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1,
                                                   custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                                   custom_dma_burst_4_downstream_requests_ddr_sdram_s1,
                                                   custom_dma_burst_4_downstream_write,
                                                   custom_dma_burst_4_downstream_writedata,
                                                   d1_ddr_sdram_s1_end_xfer,
                                                   ddr_sdram_s1_readdata_from_sa,
                                                   ddr_sdram_s1_waitrequest_n_from_sa,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_4_downstream_address_to_slave,
                                                   custom_dma_burst_4_downstream_latency_counter,
                                                   custom_dma_burst_4_downstream_readdata,
                                                   custom_dma_burst_4_downstream_readdatavalid,
                                                   custom_dma_burst_4_downstream_reset_n,
                                                   custom_dma_burst_4_downstream_waitrequest
                                                )
;

  output  [ 24: 0] custom_dma_burst_4_downstream_address_to_slave;
  output           custom_dma_burst_4_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_4_downstream_readdata;
  output           custom_dma_burst_4_downstream_readdatavalid;
  output           custom_dma_burst_4_downstream_reset_n;
  output           custom_dma_burst_4_downstream_waitrequest;
  input            clk;
  input   [ 24: 0] custom_dma_burst_4_downstream_address;
  input   [  2: 0] custom_dma_burst_4_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_4_downstream_byteenable;
  input            custom_dma_burst_4_downstream_granted_ddr_sdram_s1;
  input            custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1;
  input            custom_dma_burst_4_downstream_read;
  input            custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1;
  input            custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  input            custom_dma_burst_4_downstream_requests_ddr_sdram_s1;
  input            custom_dma_burst_4_downstream_write;
  input   [ 31: 0] custom_dma_burst_4_downstream_writedata;
  input            d1_ddr_sdram_s1_end_xfer;
  input   [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  input            ddr_sdram_s1_waitrequest_n_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 24: 0] custom_dma_burst_4_downstream_address_last_time;
  wire    [ 24: 0] custom_dma_burst_4_downstream_address_to_slave;
  reg     [  2: 0] custom_dma_burst_4_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_4_downstream_byteenable_last_time;
  wire             custom_dma_burst_4_downstream_is_granted_some_slave;
  reg              custom_dma_burst_4_downstream_latency_counter;
  reg              custom_dma_burst_4_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_4_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_4_downstream_readdata;
  wire             custom_dma_burst_4_downstream_readdatavalid;
  wire             custom_dma_burst_4_downstream_reset_n;
  wire             custom_dma_burst_4_downstream_run;
  wire             custom_dma_burst_4_downstream_waitrequest;
  reg              custom_dma_burst_4_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_4_downstream_writedata_last_time;
  wire             latency_load_value;
  wire             p1_custom_dma_burst_4_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_4_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1 | ~custom_dma_burst_4_downstream_requests_ddr_sdram_s1) & (custom_dma_burst_4_downstream_granted_ddr_sdram_s1 | ~custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1) & ((~custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write)))) & ((~custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_4_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_4_downstream_address_to_slave = custom_dma_burst_4_downstream_address;

  //custom_dma_burst_4_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_4_downstream_read_but_no_slave_selected <= custom_dma_burst_4_downstream_read & custom_dma_burst_4_downstream_run & ~custom_dma_burst_4_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_4_downstream_is_granted_some_slave = custom_dma_burst_4_downstream_granted_ddr_sdram_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_4_downstream_readdatavalid = custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_4_downstream_readdatavalid = custom_dma_burst_4_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_4_downstream_readdatavalid;

  //custom_dma_burst_4/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_4_downstream_readdata = ddr_sdram_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_4_downstream_waitrequest = ~custom_dma_burst_4_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_4_downstream_latency_counter <= p1_custom_dma_burst_4_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_4_downstream_latency_counter = ((custom_dma_burst_4_downstream_run & custom_dma_burst_4_downstream_read))? latency_load_value :
    (custom_dma_burst_4_downstream_latency_counter)? custom_dma_burst_4_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //custom_dma_burst_4_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_4_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_4_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_address_last_time <= custom_dma_burst_4_downstream_address;
    end


  //custom_dma_burst_4/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_4_downstream_waitrequest & (custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write);
    end


  //custom_dma_burst_4_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_address != custom_dma_burst_4_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_4_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_burstcount_last_time <= custom_dma_burst_4_downstream_burstcount;
    end


  //custom_dma_burst_4_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_burstcount != custom_dma_burst_4_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_4_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_byteenable_last_time <= custom_dma_burst_4_downstream_byteenable;
    end


  //custom_dma_burst_4_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_byteenable != custom_dma_burst_4_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_4_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_read_last_time <= custom_dma_burst_4_downstream_read;
    end


  //custom_dma_burst_4_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_read != custom_dma_burst_4_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_4_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_write_last_time <= custom_dma_burst_4_downstream_write;
    end


  //custom_dma_burst_4_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_write != custom_dma_burst_4_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_4_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_4_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_4_downstream_writedata_last_time <= custom_dma_burst_4_downstream_writedata;
    end


  //custom_dma_burst_4_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_4_downstream_writedata != custom_dma_burst_4_downstream_writedata_last_time) & custom_dma_burst_4_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_4_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_5_upstream_arbitrator (
                                                // inputs:
                                                 clk,
                                                 custom_dma_burst_5_upstream_readdata,
                                                 custom_dma_burst_5_upstream_readdatavalid,
                                                 custom_dma_burst_5_upstream_waitrequest,
                                                 fir_dma_write_master_address_to_slave,
                                                 fir_dma_write_master_burstcount,
                                                 fir_dma_write_master_byteenable,
                                                 fir_dma_write_master_write,
                                                 fir_dma_write_master_writedata,
                                                 reset_n,

                                                // outputs:
                                                 custom_dma_burst_5_upstream_address,
                                                 custom_dma_burst_5_upstream_burstcount,
                                                 custom_dma_burst_5_upstream_byteaddress,
                                                 custom_dma_burst_5_upstream_byteenable,
                                                 custom_dma_burst_5_upstream_debugaccess,
                                                 custom_dma_burst_5_upstream_read,
                                                 custom_dma_burst_5_upstream_readdata_from_sa,
                                                 custom_dma_burst_5_upstream_readdatavalid_from_sa,
                                                 custom_dma_burst_5_upstream_waitrequest_from_sa,
                                                 custom_dma_burst_5_upstream_write,
                                                 custom_dma_burst_5_upstream_writedata,
                                                 d1_custom_dma_burst_5_upstream_end_xfer,
                                                 fir_dma_write_master_granted_custom_dma_burst_5_upstream,
                                                 fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream,
                                                 fir_dma_write_master_requests_custom_dma_burst_5_upstream
                                              )
;

  output  [ 24: 0] custom_dma_burst_5_upstream_address;
  output  [  2: 0] custom_dma_burst_5_upstream_burstcount;
  output  [ 26: 0] custom_dma_burst_5_upstream_byteaddress;
  output  [  3: 0] custom_dma_burst_5_upstream_byteenable;
  output           custom_dma_burst_5_upstream_debugaccess;
  output           custom_dma_burst_5_upstream_read;
  output  [ 31: 0] custom_dma_burst_5_upstream_readdata_from_sa;
  output           custom_dma_burst_5_upstream_readdatavalid_from_sa;
  output           custom_dma_burst_5_upstream_waitrequest_from_sa;
  output           custom_dma_burst_5_upstream_write;
  output  [ 31: 0] custom_dma_burst_5_upstream_writedata;
  output           d1_custom_dma_burst_5_upstream_end_xfer;
  output           fir_dma_write_master_granted_custom_dma_burst_5_upstream;
  output           fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream;
  output           fir_dma_write_master_requests_custom_dma_burst_5_upstream;
  input            clk;
  input   [ 31: 0] custom_dma_burst_5_upstream_readdata;
  input            custom_dma_burst_5_upstream_readdatavalid;
  input            custom_dma_burst_5_upstream_waitrequest;
  input   [ 31: 0] fir_dma_write_master_address_to_slave;
  input   [  2: 0] fir_dma_write_master_burstcount;
  input   [  3: 0] fir_dma_write_master_byteenable;
  input            fir_dma_write_master_write;
  input   [ 31: 0] fir_dma_write_master_writedata;
  input            reset_n;

  wire    [ 24: 0] custom_dma_burst_5_upstream_address;
  wire             custom_dma_burst_5_upstream_allgrants;
  wire             custom_dma_burst_5_upstream_allow_new_arb_cycle;
  wire             custom_dma_burst_5_upstream_any_bursting_master_saved_grant;
  wire             custom_dma_burst_5_upstream_any_continuerequest;
  wire             custom_dma_burst_5_upstream_arb_counter_enable;
  reg     [  2: 0] custom_dma_burst_5_upstream_arb_share_counter;
  wire    [  2: 0] custom_dma_burst_5_upstream_arb_share_counter_next_value;
  wire    [  2: 0] custom_dma_burst_5_upstream_arb_share_set_values;
  reg     [  1: 0] custom_dma_burst_5_upstream_bbt_burstcounter;
  wire             custom_dma_burst_5_upstream_beginbursttransfer_internal;
  wire             custom_dma_burst_5_upstream_begins_xfer;
  wire    [  2: 0] custom_dma_burst_5_upstream_burstcount;
  wire    [ 26: 0] custom_dma_burst_5_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_5_upstream_byteenable;
  wire             custom_dma_burst_5_upstream_debugaccess;
  wire             custom_dma_burst_5_upstream_end_xfer;
  wire             custom_dma_burst_5_upstream_firsttransfer;
  wire             custom_dma_burst_5_upstream_grant_vector;
  wire             custom_dma_burst_5_upstream_in_a_read_cycle;
  wire             custom_dma_burst_5_upstream_in_a_write_cycle;
  wire             custom_dma_burst_5_upstream_master_qreq_vector;
  wire    [  1: 0] custom_dma_burst_5_upstream_next_bbt_burstcount;
  wire             custom_dma_burst_5_upstream_non_bursting_master_requests;
  wire             custom_dma_burst_5_upstream_read;
  wire    [ 31: 0] custom_dma_burst_5_upstream_readdata_from_sa;
  wire             custom_dma_burst_5_upstream_readdatavalid_from_sa;
  reg              custom_dma_burst_5_upstream_reg_firsttransfer;
  reg              custom_dma_burst_5_upstream_slavearbiterlockenable;
  wire             custom_dma_burst_5_upstream_slavearbiterlockenable2;
  wire             custom_dma_burst_5_upstream_unreg_firsttransfer;
  wire             custom_dma_burst_5_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_5_upstream_waits_for_read;
  wire             custom_dma_burst_5_upstream_waits_for_write;
  wire             custom_dma_burst_5_upstream_write;
  wire    [ 31: 0] custom_dma_burst_5_upstream_writedata;
  reg              d1_custom_dma_burst_5_upstream_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_arbiterlock;
  wire             fir_dma_write_master_arbiterlock2;
  wire             fir_dma_write_master_continuerequest;
  wire             fir_dma_write_master_granted_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_requests_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_saved_grant_custom_dma_burst_5_upstream;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             wait_for_custom_dma_burst_5_upstream_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_burst_5_upstream_end_xfer;
    end


  assign custom_dma_burst_5_upstream_begins_xfer = ~d1_reasons_to_wait & ((fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream));
  //assign custom_dma_burst_5_upstream_readdata_from_sa = custom_dma_burst_5_upstream_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_5_upstream_readdata_from_sa = custom_dma_burst_5_upstream_readdata;

  assign fir_dma_write_master_requests_custom_dma_burst_5_upstream = (({fir_dma_write_master_address_to_slave[31 : 25] , 25'b0} == 32'h2000000) & (fir_dma_write_master_write)) & fir_dma_write_master_write;
  //assign custom_dma_burst_5_upstream_waitrequest_from_sa = custom_dma_burst_5_upstream_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_5_upstream_waitrequest_from_sa = custom_dma_burst_5_upstream_waitrequest;

  //custom_dma_burst_5_upstream_arb_share_counter set values, which is an e_mux
  assign custom_dma_burst_5_upstream_arb_share_set_values = (fir_dma_write_master_granted_custom_dma_burst_5_upstream)? fir_dma_write_master_burstcount :
    1;

  //custom_dma_burst_5_upstream_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_burst_5_upstream_non_bursting_master_requests = 0;

  //custom_dma_burst_5_upstream_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_burst_5_upstream_any_bursting_master_saved_grant = fir_dma_write_master_saved_grant_custom_dma_burst_5_upstream;

  //custom_dma_burst_5_upstream_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_burst_5_upstream_arb_share_counter_next_value = custom_dma_burst_5_upstream_firsttransfer ? (custom_dma_burst_5_upstream_arb_share_set_values - 1) : |custom_dma_burst_5_upstream_arb_share_counter ? (custom_dma_burst_5_upstream_arb_share_counter - 1) : 0;

  //custom_dma_burst_5_upstream_allgrants all slave grants, which is an e_mux
  assign custom_dma_burst_5_upstream_allgrants = |custom_dma_burst_5_upstream_grant_vector;

  //custom_dma_burst_5_upstream_end_xfer assignment, which is an e_assign
  assign custom_dma_burst_5_upstream_end_xfer = ~(custom_dma_burst_5_upstream_waits_for_read | custom_dma_burst_5_upstream_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream = custom_dma_burst_5_upstream_end_xfer & (~custom_dma_burst_5_upstream_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_burst_5_upstream_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_burst_5_upstream_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream & custom_dma_burst_5_upstream_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream & ~custom_dma_burst_5_upstream_non_bursting_master_requests);

  //custom_dma_burst_5_upstream_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_upstream_arb_share_counter <= 0;
      else if (custom_dma_burst_5_upstream_arb_counter_enable)
          custom_dma_burst_5_upstream_arb_share_counter <= custom_dma_burst_5_upstream_arb_share_counter_next_value;
    end


  //custom_dma_burst_5_upstream_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_upstream_slavearbiterlockenable <= 0;
      else if ((|custom_dma_burst_5_upstream_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream) | (end_xfer_arb_share_counter_term_custom_dma_burst_5_upstream & ~custom_dma_burst_5_upstream_non_bursting_master_requests))
          custom_dma_burst_5_upstream_slavearbiterlockenable <= |custom_dma_burst_5_upstream_arb_share_counter_next_value;
    end


  //fir_dma/write_master custom_dma_burst_5/upstream arbiterlock, which is an e_assign
  assign fir_dma_write_master_arbiterlock = custom_dma_burst_5_upstream_slavearbiterlockenable & fir_dma_write_master_continuerequest;

  //custom_dma_burst_5_upstream_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_burst_5_upstream_slavearbiterlockenable2 = |custom_dma_burst_5_upstream_arb_share_counter_next_value;

  //fir_dma/write_master custom_dma_burst_5/upstream arbiterlock2, which is an e_assign
  assign fir_dma_write_master_arbiterlock2 = custom_dma_burst_5_upstream_slavearbiterlockenable2 & fir_dma_write_master_continuerequest;

  //custom_dma_burst_5_upstream_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_burst_5_upstream_any_continuerequest = 1;

  //fir_dma_write_master_continuerequest continued request, which is an e_assign
  assign fir_dma_write_master_continuerequest = 1;

  assign fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream = fir_dma_write_master_requests_custom_dma_burst_5_upstream;
  //custom_dma_burst_5_upstream_writedata mux, which is an e_mux
  assign custom_dma_burst_5_upstream_writedata = fir_dma_write_master_writedata;

  //byteaddress mux for custom_dma_burst_5/upstream, which is an e_mux
  assign custom_dma_burst_5_upstream_byteaddress = fir_dma_write_master_address_to_slave;

  //master is always granted when requested
  assign fir_dma_write_master_granted_custom_dma_burst_5_upstream = fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream;

  //fir_dma/write_master saved-grant custom_dma_burst_5/upstream, which is an e_assign
  assign fir_dma_write_master_saved_grant_custom_dma_burst_5_upstream = fir_dma_write_master_requests_custom_dma_burst_5_upstream;

  //allow new arb cycle for custom_dma_burst_5/upstream, which is an e_assign
  assign custom_dma_burst_5_upstream_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_burst_5_upstream_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_burst_5_upstream_master_qreq_vector = 1;

  //custom_dma_burst_5_upstream_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_5_upstream_firsttransfer = custom_dma_burst_5_upstream_begins_xfer ? custom_dma_burst_5_upstream_unreg_firsttransfer : custom_dma_burst_5_upstream_reg_firsttransfer;

  //custom_dma_burst_5_upstream_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_burst_5_upstream_unreg_firsttransfer = ~(custom_dma_burst_5_upstream_slavearbiterlockenable & custom_dma_burst_5_upstream_any_continuerequest);

  //custom_dma_burst_5_upstream_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_upstream_reg_firsttransfer <= 1'b1;
      else if (custom_dma_burst_5_upstream_begins_xfer)
          custom_dma_burst_5_upstream_reg_firsttransfer <= custom_dma_burst_5_upstream_unreg_firsttransfer;
    end


  //custom_dma_burst_5_upstream_next_bbt_burstcount next_bbt_burstcount, which is an e_mux
  assign custom_dma_burst_5_upstream_next_bbt_burstcount = ((((custom_dma_burst_5_upstream_write) && (custom_dma_burst_5_upstream_bbt_burstcounter == 0))))? (custom_dma_burst_5_upstream_burstcount - 1) :
    ((((custom_dma_burst_5_upstream_read) && (custom_dma_burst_5_upstream_bbt_burstcounter == 0))))? 0 :
    (custom_dma_burst_5_upstream_bbt_burstcounter - 1);

  //custom_dma_burst_5_upstream_bbt_burstcounter bbt_burstcounter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_upstream_bbt_burstcounter <= 0;
      else if (custom_dma_burst_5_upstream_begins_xfer)
          custom_dma_burst_5_upstream_bbt_burstcounter <= custom_dma_burst_5_upstream_next_bbt_burstcount;
    end


  //custom_dma_burst_5_upstream_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_burst_5_upstream_beginbursttransfer_internal = custom_dma_burst_5_upstream_begins_xfer & (custom_dma_burst_5_upstream_bbt_burstcounter == 0);

  //custom_dma_burst_5_upstream_read assignment, which is an e_mux
  assign custom_dma_burst_5_upstream_read = 0;

  //custom_dma_burst_5_upstream_write assignment, which is an e_mux
  assign custom_dma_burst_5_upstream_write = fir_dma_write_master_granted_custom_dma_burst_5_upstream & fir_dma_write_master_write;

  //custom_dma_burst_5_upstream_address mux, which is an e_mux
  assign custom_dma_burst_5_upstream_address = fir_dma_write_master_address_to_slave;

  //d1_custom_dma_burst_5_upstream_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_burst_5_upstream_end_xfer <= 1;
      else 
        d1_custom_dma_burst_5_upstream_end_xfer <= custom_dma_burst_5_upstream_end_xfer;
    end


  //custom_dma_burst_5_upstream_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_burst_5_upstream_waits_for_read = custom_dma_burst_5_upstream_in_a_read_cycle & custom_dma_burst_5_upstream_waitrequest_from_sa;

  //custom_dma_burst_5_upstream_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_burst_5_upstream_in_a_read_cycle = 0;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_burst_5_upstream_in_a_read_cycle;

  //custom_dma_burst_5_upstream_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_burst_5_upstream_waits_for_write = custom_dma_burst_5_upstream_in_a_write_cycle & custom_dma_burst_5_upstream_waitrequest_from_sa;

  //assign custom_dma_burst_5_upstream_readdatavalid_from_sa = custom_dma_burst_5_upstream_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_burst_5_upstream_readdatavalid_from_sa = custom_dma_burst_5_upstream_readdatavalid;

  //custom_dma_burst_5_upstream_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_burst_5_upstream_in_a_write_cycle = fir_dma_write_master_granted_custom_dma_burst_5_upstream & fir_dma_write_master_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_burst_5_upstream_in_a_write_cycle;

  assign wait_for_custom_dma_burst_5_upstream_counter = 0;
  //custom_dma_burst_5_upstream_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_burst_5_upstream_byteenable = (fir_dma_write_master_granted_custom_dma_burst_5_upstream)? fir_dma_write_master_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign custom_dma_burst_5_upstream_burstcount = (fir_dma_write_master_granted_custom_dma_burst_5_upstream)? fir_dma_write_master_burstcount :
    1;

  //debugaccess mux, which is an e_mux
  assign custom_dma_burst_5_upstream_debugaccess = 0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_5/upstream enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //fir_dma/write_master non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (fir_dma_write_master_requests_custom_dma_burst_5_upstream && (fir_dma_write_master_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: fir_dma/write_master drove 0 on its 'burstcount' port while accessing slave custom_dma_burst_5/upstream", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_burst_5_downstream_arbitrator (
                                                  // inputs:
                                                   clk,
                                                   custom_dma_burst_5_downstream_address,
                                                   custom_dma_burst_5_downstream_burstcount,
                                                   custom_dma_burst_5_downstream_byteenable,
                                                   custom_dma_burst_5_downstream_granted_ddr_sdram_s1,
                                                   custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1,
                                                   custom_dma_burst_5_downstream_read,
                                                   custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1,
                                                   custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                                   custom_dma_burst_5_downstream_requests_ddr_sdram_s1,
                                                   custom_dma_burst_5_downstream_write,
                                                   custom_dma_burst_5_downstream_writedata,
                                                   d1_ddr_sdram_s1_end_xfer,
                                                   ddr_sdram_s1_readdata_from_sa,
                                                   ddr_sdram_s1_waitrequest_n_from_sa,
                                                   reset_n,

                                                  // outputs:
                                                   custom_dma_burst_5_downstream_address_to_slave,
                                                   custom_dma_burst_5_downstream_latency_counter,
                                                   custom_dma_burst_5_downstream_readdata,
                                                   custom_dma_burst_5_downstream_readdatavalid,
                                                   custom_dma_burst_5_downstream_reset_n,
                                                   custom_dma_burst_5_downstream_waitrequest
                                                )
;

  output  [ 24: 0] custom_dma_burst_5_downstream_address_to_slave;
  output           custom_dma_burst_5_downstream_latency_counter;
  output  [ 31: 0] custom_dma_burst_5_downstream_readdata;
  output           custom_dma_burst_5_downstream_readdatavalid;
  output           custom_dma_burst_5_downstream_reset_n;
  output           custom_dma_burst_5_downstream_waitrequest;
  input            clk;
  input   [ 24: 0] custom_dma_burst_5_downstream_address;
  input   [  2: 0] custom_dma_burst_5_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_5_downstream_byteenable;
  input            custom_dma_burst_5_downstream_granted_ddr_sdram_s1;
  input            custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1;
  input            custom_dma_burst_5_downstream_read;
  input            custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1;
  input            custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  input            custom_dma_burst_5_downstream_requests_ddr_sdram_s1;
  input            custom_dma_burst_5_downstream_write;
  input   [ 31: 0] custom_dma_burst_5_downstream_writedata;
  input            d1_ddr_sdram_s1_end_xfer;
  input   [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  input            ddr_sdram_s1_waitrequest_n_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 24: 0] custom_dma_burst_5_downstream_address_last_time;
  wire    [ 24: 0] custom_dma_burst_5_downstream_address_to_slave;
  reg     [  2: 0] custom_dma_burst_5_downstream_burstcount_last_time;
  reg     [  3: 0] custom_dma_burst_5_downstream_byteenable_last_time;
  wire             custom_dma_burst_5_downstream_is_granted_some_slave;
  reg              custom_dma_burst_5_downstream_latency_counter;
  reg              custom_dma_burst_5_downstream_read_but_no_slave_selected;
  reg              custom_dma_burst_5_downstream_read_last_time;
  wire    [ 31: 0] custom_dma_burst_5_downstream_readdata;
  wire             custom_dma_burst_5_downstream_readdatavalid;
  wire             custom_dma_burst_5_downstream_reset_n;
  wire             custom_dma_burst_5_downstream_run;
  wire             custom_dma_burst_5_downstream_waitrequest;
  reg              custom_dma_burst_5_downstream_write_last_time;
  reg     [ 31: 0] custom_dma_burst_5_downstream_writedata_last_time;
  wire             latency_load_value;
  wire             p1_custom_dma_burst_5_downstream_latency_counter;
  wire             pre_flush_custom_dma_burst_5_downstream_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1 | ~custom_dma_burst_5_downstream_requests_ddr_sdram_s1) & (custom_dma_burst_5_downstream_granted_ddr_sdram_s1 | ~custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1) & ((~custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write)))) & ((~custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1 | ~(custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write) | (1 & ddr_sdram_s1_waitrequest_n_from_sa & (custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write))));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_burst_5_downstream_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_burst_5_downstream_address_to_slave = custom_dma_burst_5_downstream_address;

  //custom_dma_burst_5_downstream_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_read_but_no_slave_selected <= 0;
      else 
        custom_dma_burst_5_downstream_read_but_no_slave_selected <= custom_dma_burst_5_downstream_read & custom_dma_burst_5_downstream_run & ~custom_dma_burst_5_downstream_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign custom_dma_burst_5_downstream_is_granted_some_slave = custom_dma_burst_5_downstream_granted_ddr_sdram_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_custom_dma_burst_5_downstream_readdatavalid = custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign custom_dma_burst_5_downstream_readdatavalid = custom_dma_burst_5_downstream_read_but_no_slave_selected |
    pre_flush_custom_dma_burst_5_downstream_readdatavalid;

  //custom_dma_burst_5/downstream readdata mux, which is an e_mux
  assign custom_dma_burst_5_downstream_readdata = ddr_sdram_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_burst_5_downstream_waitrequest = ~custom_dma_burst_5_downstream_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_latency_counter <= 0;
      else 
        custom_dma_burst_5_downstream_latency_counter <= p1_custom_dma_burst_5_downstream_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_custom_dma_burst_5_downstream_latency_counter = ((custom_dma_burst_5_downstream_run & custom_dma_burst_5_downstream_read))? latency_load_value :
    (custom_dma_burst_5_downstream_latency_counter)? custom_dma_burst_5_downstream_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = 0;

  //custom_dma_burst_5_downstream_reset_n assignment, which is an e_assign
  assign custom_dma_burst_5_downstream_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_burst_5_downstream_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_address_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_address_last_time <= custom_dma_burst_5_downstream_address;
    end


  //custom_dma_burst_5/downstream waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_burst_5_downstream_waitrequest & (custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write);
    end


  //custom_dma_burst_5_downstream_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_address != custom_dma_burst_5_downstream_address_last_time))
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_5_downstream_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_burstcount_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_burstcount_last_time <= custom_dma_burst_5_downstream_burstcount;
    end


  //custom_dma_burst_5_downstream_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_burstcount != custom_dma_burst_5_downstream_burstcount_last_time))
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_5_downstream_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_byteenable_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_byteenable_last_time <= custom_dma_burst_5_downstream_byteenable;
    end


  //custom_dma_burst_5_downstream_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_byteenable != custom_dma_burst_5_downstream_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_5_downstream_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_read_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_read_last_time <= custom_dma_burst_5_downstream_read;
    end


  //custom_dma_burst_5_downstream_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_read != custom_dma_burst_5_downstream_read_last_time))
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_5_downstream_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_write_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_write_last_time <= custom_dma_burst_5_downstream_write;
    end


  //custom_dma_burst_5_downstream_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_write != custom_dma_burst_5_downstream_write_last_time))
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_burst_5_downstream_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_5_downstream_writedata_last_time <= 0;
      else 
        custom_dma_burst_5_downstream_writedata_last_time <= custom_dma_burst_5_downstream_writedata;
    end


  //custom_dma_burst_5_downstream_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_burst_5_downstream_writedata != custom_dma_burst_5_downstream_writedata_last_time) & custom_dma_burst_5_downstream_write)
        begin
          $write("%0d ns: custom_dma_burst_5_downstream_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_clock_0_in_arbitrator (
                                          // inputs:
                                           clk,
                                           custom_dma_clock_0_in_endofpacket,
                                           custom_dma_clock_0_in_readdata,
                                           custom_dma_clock_0_in_waitrequest,
                                           pipeline_bridge_m1_address_to_slave,
                                           pipeline_bridge_m1_burstcount,
                                           pipeline_bridge_m1_byteenable,
                                           pipeline_bridge_m1_chipselect,
                                           pipeline_bridge_m1_latency_counter,
                                           pipeline_bridge_m1_read,
                                           pipeline_bridge_m1_write,
                                           pipeline_bridge_m1_writedata,
                                           reset_n,

                                          // outputs:
                                           custom_dma_clock_0_in_address,
                                           custom_dma_clock_0_in_byteenable,
                                           custom_dma_clock_0_in_endofpacket_from_sa,
                                           custom_dma_clock_0_in_nativeaddress,
                                           custom_dma_clock_0_in_read,
                                           custom_dma_clock_0_in_readdata_from_sa,
                                           custom_dma_clock_0_in_reset_n,
                                           custom_dma_clock_0_in_waitrequest_from_sa,
                                           custom_dma_clock_0_in_write,
                                           custom_dma_clock_0_in_writedata,
                                           d1_custom_dma_clock_0_in_end_xfer,
                                           pipeline_bridge_m1_granted_custom_dma_clock_0_in,
                                           pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in,
                                           pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in,
                                           pipeline_bridge_m1_requests_custom_dma_clock_0_in
                                        )
;

  output  [  3: 0] custom_dma_clock_0_in_address;
  output  [  1: 0] custom_dma_clock_0_in_byteenable;
  output           custom_dma_clock_0_in_endofpacket_from_sa;
  output  [  2: 0] custom_dma_clock_0_in_nativeaddress;
  output           custom_dma_clock_0_in_read;
  output  [ 15: 0] custom_dma_clock_0_in_readdata_from_sa;
  output           custom_dma_clock_0_in_reset_n;
  output           custom_dma_clock_0_in_waitrequest_from_sa;
  output           custom_dma_clock_0_in_write;
  output  [ 15: 0] custom_dma_clock_0_in_writedata;
  output           d1_custom_dma_clock_0_in_end_xfer;
  output           pipeline_bridge_m1_granted_custom_dma_clock_0_in;
  output           pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in;
  output           pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in;
  output           pipeline_bridge_m1_requests_custom_dma_clock_0_in;
  input            clk;
  input            custom_dma_clock_0_in_endofpacket;
  input   [ 15: 0] custom_dma_clock_0_in_readdata;
  input            custom_dma_clock_0_in_waitrequest;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input   [  3: 0] pipeline_bridge_m1_byteenable;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;

  wire    [  3: 0] custom_dma_clock_0_in_address;
  wire             custom_dma_clock_0_in_allgrants;
  wire             custom_dma_clock_0_in_allow_new_arb_cycle;
  wire             custom_dma_clock_0_in_any_bursting_master_saved_grant;
  wire             custom_dma_clock_0_in_any_continuerequest;
  wire             custom_dma_clock_0_in_arb_counter_enable;
  reg              custom_dma_clock_0_in_arb_share_counter;
  wire             custom_dma_clock_0_in_arb_share_counter_next_value;
  wire             custom_dma_clock_0_in_arb_share_set_values;
  wire             custom_dma_clock_0_in_beginbursttransfer_internal;
  wire             custom_dma_clock_0_in_begins_xfer;
  wire    [  1: 0] custom_dma_clock_0_in_byteenable;
  wire             custom_dma_clock_0_in_end_xfer;
  wire             custom_dma_clock_0_in_endofpacket_from_sa;
  wire             custom_dma_clock_0_in_firsttransfer;
  wire             custom_dma_clock_0_in_grant_vector;
  wire             custom_dma_clock_0_in_in_a_read_cycle;
  wire             custom_dma_clock_0_in_in_a_write_cycle;
  wire             custom_dma_clock_0_in_master_qreq_vector;
  wire    [  2: 0] custom_dma_clock_0_in_nativeaddress;
  wire             custom_dma_clock_0_in_non_bursting_master_requests;
  wire             custom_dma_clock_0_in_read;
  wire    [ 15: 0] custom_dma_clock_0_in_readdata_from_sa;
  reg              custom_dma_clock_0_in_reg_firsttransfer;
  wire             custom_dma_clock_0_in_reset_n;
  reg              custom_dma_clock_0_in_slavearbiterlockenable;
  wire             custom_dma_clock_0_in_slavearbiterlockenable2;
  wire             custom_dma_clock_0_in_unreg_firsttransfer;
  wire             custom_dma_clock_0_in_waitrequest_from_sa;
  wire             custom_dma_clock_0_in_waits_for_read;
  wire             custom_dma_clock_0_in_waits_for_write;
  wire             custom_dma_clock_0_in_write;
  wire    [ 15: 0] custom_dma_clock_0_in_writedata;
  reg              d1_custom_dma_clock_0_in_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_custom_dma_clock_0_in;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_requests_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_saved_grant_custom_dma_clock_0_in;
  wire    [ 11: 0] shifted_address_to_custom_dma_clock_0_in_from_pipeline_bridge_m1;
  wire             wait_for_custom_dma_clock_0_in_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~custom_dma_clock_0_in_end_xfer;
    end


  assign custom_dma_clock_0_in_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in));
  //assign custom_dma_clock_0_in_readdata_from_sa = custom_dma_clock_0_in_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_clock_0_in_readdata_from_sa = custom_dma_clock_0_in_readdata;

  assign pipeline_bridge_m1_requests_custom_dma_clock_0_in = ({pipeline_bridge_m1_address_to_slave[11 : 5] , 5'b0} == 12'h820) & pipeline_bridge_m1_chipselect;
  //assign custom_dma_clock_0_in_waitrequest_from_sa = custom_dma_clock_0_in_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_clock_0_in_waitrequest_from_sa = custom_dma_clock_0_in_waitrequest;

  //custom_dma_clock_0_in_arb_share_counter set values, which is an e_mux
  assign custom_dma_clock_0_in_arb_share_set_values = 1;

  //custom_dma_clock_0_in_non_bursting_master_requests mux, which is an e_mux
  assign custom_dma_clock_0_in_non_bursting_master_requests = pipeline_bridge_m1_requests_custom_dma_clock_0_in;

  //custom_dma_clock_0_in_any_bursting_master_saved_grant mux, which is an e_mux
  assign custom_dma_clock_0_in_any_bursting_master_saved_grant = 0;

  //custom_dma_clock_0_in_arb_share_counter_next_value assignment, which is an e_assign
  assign custom_dma_clock_0_in_arb_share_counter_next_value = custom_dma_clock_0_in_firsttransfer ? (custom_dma_clock_0_in_arb_share_set_values - 1) : |custom_dma_clock_0_in_arb_share_counter ? (custom_dma_clock_0_in_arb_share_counter - 1) : 0;

  //custom_dma_clock_0_in_allgrants all slave grants, which is an e_mux
  assign custom_dma_clock_0_in_allgrants = |custom_dma_clock_0_in_grant_vector;

  //custom_dma_clock_0_in_end_xfer assignment, which is an e_assign
  assign custom_dma_clock_0_in_end_xfer = ~(custom_dma_clock_0_in_waits_for_read | custom_dma_clock_0_in_waits_for_write);

  //end_xfer_arb_share_counter_term_custom_dma_clock_0_in arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_custom_dma_clock_0_in = custom_dma_clock_0_in_end_xfer & (~custom_dma_clock_0_in_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //custom_dma_clock_0_in_arb_share_counter arbitration counter enable, which is an e_assign
  assign custom_dma_clock_0_in_arb_counter_enable = (end_xfer_arb_share_counter_term_custom_dma_clock_0_in & custom_dma_clock_0_in_allgrants) | (end_xfer_arb_share_counter_term_custom_dma_clock_0_in & ~custom_dma_clock_0_in_non_bursting_master_requests);

  //custom_dma_clock_0_in_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_in_arb_share_counter <= 0;
      else if (custom_dma_clock_0_in_arb_counter_enable)
          custom_dma_clock_0_in_arb_share_counter <= custom_dma_clock_0_in_arb_share_counter_next_value;
    end


  //custom_dma_clock_0_in_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_in_slavearbiterlockenable <= 0;
      else if ((|custom_dma_clock_0_in_master_qreq_vector & end_xfer_arb_share_counter_term_custom_dma_clock_0_in) | (end_xfer_arb_share_counter_term_custom_dma_clock_0_in & ~custom_dma_clock_0_in_non_bursting_master_requests))
          custom_dma_clock_0_in_slavearbiterlockenable <= |custom_dma_clock_0_in_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 custom_dma_clock_0/in arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = custom_dma_clock_0_in_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //custom_dma_clock_0_in_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign custom_dma_clock_0_in_slavearbiterlockenable2 = |custom_dma_clock_0_in_arb_share_counter_next_value;

  //pipeline_bridge/m1 custom_dma_clock_0/in arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = custom_dma_clock_0_in_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //custom_dma_clock_0_in_any_continuerequest at least one master continues requesting, which is an e_assign
  assign custom_dma_clock_0_in_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in = pipeline_bridge_m1_requests_custom_dma_clock_0_in & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((pipeline_bridge_m1_latency_counter != 0))));
  //local readdatavalid pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in = pipeline_bridge_m1_granted_custom_dma_clock_0_in & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~custom_dma_clock_0_in_waits_for_read;

  //custom_dma_clock_0_in_writedata mux, which is an e_mux
  assign custom_dma_clock_0_in_writedata = pipeline_bridge_m1_writedata;

  //assign custom_dma_clock_0_in_endofpacket_from_sa = custom_dma_clock_0_in_endofpacket so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign custom_dma_clock_0_in_endofpacket_from_sa = custom_dma_clock_0_in_endofpacket;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_custom_dma_clock_0_in = pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in;

  //pipeline_bridge/m1 saved-grant custom_dma_clock_0/in, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_custom_dma_clock_0_in = pipeline_bridge_m1_requests_custom_dma_clock_0_in;

  //allow new arb cycle for custom_dma_clock_0/in, which is an e_assign
  assign custom_dma_clock_0_in_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign custom_dma_clock_0_in_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign custom_dma_clock_0_in_master_qreq_vector = 1;

  //custom_dma_clock_0_in_reset_n assignment, which is an e_assign
  assign custom_dma_clock_0_in_reset_n = reset_n;

  //custom_dma_clock_0_in_firsttransfer first transaction, which is an e_assign
  assign custom_dma_clock_0_in_firsttransfer = custom_dma_clock_0_in_begins_xfer ? custom_dma_clock_0_in_unreg_firsttransfer : custom_dma_clock_0_in_reg_firsttransfer;

  //custom_dma_clock_0_in_unreg_firsttransfer first transaction, which is an e_assign
  assign custom_dma_clock_0_in_unreg_firsttransfer = ~(custom_dma_clock_0_in_slavearbiterlockenable & custom_dma_clock_0_in_any_continuerequest);

  //custom_dma_clock_0_in_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_in_reg_firsttransfer <= 1'b1;
      else if (custom_dma_clock_0_in_begins_xfer)
          custom_dma_clock_0_in_reg_firsttransfer <= custom_dma_clock_0_in_unreg_firsttransfer;
    end


  //custom_dma_clock_0_in_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign custom_dma_clock_0_in_beginbursttransfer_internal = custom_dma_clock_0_in_begins_xfer;

  //custom_dma_clock_0_in_read assignment, which is an e_mux
  assign custom_dma_clock_0_in_read = pipeline_bridge_m1_granted_custom_dma_clock_0_in & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //custom_dma_clock_0_in_write assignment, which is an e_mux
  assign custom_dma_clock_0_in_write = pipeline_bridge_m1_granted_custom_dma_clock_0_in & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  assign shifted_address_to_custom_dma_clock_0_in_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //custom_dma_clock_0_in_address mux, which is an e_mux
  assign custom_dma_clock_0_in_address = shifted_address_to_custom_dma_clock_0_in_from_pipeline_bridge_m1 >> 2;

  //slaveid custom_dma_clock_0_in_nativeaddress nativeaddress mux, which is an e_mux
  assign custom_dma_clock_0_in_nativeaddress = pipeline_bridge_m1_address_to_slave >> 2;

  //d1_custom_dma_clock_0_in_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_custom_dma_clock_0_in_end_xfer <= 1;
      else 
        d1_custom_dma_clock_0_in_end_xfer <= custom_dma_clock_0_in_end_xfer;
    end


  //custom_dma_clock_0_in_waits_for_read in a cycle, which is an e_mux
  assign custom_dma_clock_0_in_waits_for_read = custom_dma_clock_0_in_in_a_read_cycle & custom_dma_clock_0_in_waitrequest_from_sa;

  //custom_dma_clock_0_in_in_a_read_cycle assignment, which is an e_assign
  assign custom_dma_clock_0_in_in_a_read_cycle = pipeline_bridge_m1_granted_custom_dma_clock_0_in & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = custom_dma_clock_0_in_in_a_read_cycle;

  //custom_dma_clock_0_in_waits_for_write in a cycle, which is an e_mux
  assign custom_dma_clock_0_in_waits_for_write = custom_dma_clock_0_in_in_a_write_cycle & custom_dma_clock_0_in_waitrequest_from_sa;

  //custom_dma_clock_0_in_in_a_write_cycle assignment, which is an e_assign
  assign custom_dma_clock_0_in_in_a_write_cycle = pipeline_bridge_m1_granted_custom_dma_clock_0_in & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = custom_dma_clock_0_in_in_a_write_cycle;

  assign wait_for_custom_dma_clock_0_in_counter = 0;
  //custom_dma_clock_0_in_byteenable byte enable port mux, which is an e_mux
  assign custom_dma_clock_0_in_byteenable = (pipeline_bridge_m1_granted_custom_dma_clock_0_in)? pipeline_bridge_m1_byteenable :
    -1;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_clock_0/in enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_custom_dma_clock_0_in && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave custom_dma_clock_0/in", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_clock_0_out_arbitrator (
                                           // inputs:
                                            clk,
                                            custom_dma_clock_0_out_address,
                                            custom_dma_clock_0_out_byteenable,
                                            custom_dma_clock_0_out_granted_pll_s1,
                                            custom_dma_clock_0_out_qualified_request_pll_s1,
                                            custom_dma_clock_0_out_read,
                                            custom_dma_clock_0_out_read_data_valid_pll_s1,
                                            custom_dma_clock_0_out_requests_pll_s1,
                                            custom_dma_clock_0_out_write,
                                            custom_dma_clock_0_out_writedata,
                                            d1_pll_s1_end_xfer,
                                            pll_s1_readdata_from_sa,
                                            reset_n,

                                           // outputs:
                                            custom_dma_clock_0_out_address_to_slave,
                                            custom_dma_clock_0_out_readdata,
                                            custom_dma_clock_0_out_reset_n,
                                            custom_dma_clock_0_out_waitrequest
                                         )
;

  output  [  3: 0] custom_dma_clock_0_out_address_to_slave;
  output  [ 15: 0] custom_dma_clock_0_out_readdata;
  output           custom_dma_clock_0_out_reset_n;
  output           custom_dma_clock_0_out_waitrequest;
  input            clk;
  input   [  3: 0] custom_dma_clock_0_out_address;
  input   [  1: 0] custom_dma_clock_0_out_byteenable;
  input            custom_dma_clock_0_out_granted_pll_s1;
  input            custom_dma_clock_0_out_qualified_request_pll_s1;
  input            custom_dma_clock_0_out_read;
  input            custom_dma_clock_0_out_read_data_valid_pll_s1;
  input            custom_dma_clock_0_out_requests_pll_s1;
  input            custom_dma_clock_0_out_write;
  input   [ 15: 0] custom_dma_clock_0_out_writedata;
  input            d1_pll_s1_end_xfer;
  input   [ 15: 0] pll_s1_readdata_from_sa;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [  3: 0] custom_dma_clock_0_out_address_last_time;
  wire    [  3: 0] custom_dma_clock_0_out_address_to_slave;
  reg     [  1: 0] custom_dma_clock_0_out_byteenable_last_time;
  reg              custom_dma_clock_0_out_read_last_time;
  wire    [ 15: 0] custom_dma_clock_0_out_readdata;
  wire             custom_dma_clock_0_out_reset_n;
  wire             custom_dma_clock_0_out_run;
  wire             custom_dma_clock_0_out_waitrequest;
  reg              custom_dma_clock_0_out_write_last_time;
  reg     [ 15: 0] custom_dma_clock_0_out_writedata_last_time;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & ((~custom_dma_clock_0_out_qualified_request_pll_s1 | ~custom_dma_clock_0_out_read | (1 & ~d1_pll_s1_end_xfer & custom_dma_clock_0_out_read))) & ((~custom_dma_clock_0_out_qualified_request_pll_s1 | ~custom_dma_clock_0_out_write | (1 & custom_dma_clock_0_out_write)));

  //cascaded wait assignment, which is an e_assign
  assign custom_dma_clock_0_out_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign custom_dma_clock_0_out_address_to_slave = custom_dma_clock_0_out_address;

  //custom_dma_clock_0/out readdata mux, which is an e_mux
  assign custom_dma_clock_0_out_readdata = pll_s1_readdata_from_sa;

  //actual waitrequest port, which is an e_assign
  assign custom_dma_clock_0_out_waitrequest = ~custom_dma_clock_0_out_run;

  //custom_dma_clock_0_out_reset_n assignment, which is an e_assign
  assign custom_dma_clock_0_out_reset_n = reset_n;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //custom_dma_clock_0_out_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_out_address_last_time <= 0;
      else 
        custom_dma_clock_0_out_address_last_time <= custom_dma_clock_0_out_address;
    end


  //custom_dma_clock_0/out waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= custom_dma_clock_0_out_waitrequest & (custom_dma_clock_0_out_read | custom_dma_clock_0_out_write);
    end


  //custom_dma_clock_0_out_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_clock_0_out_address != custom_dma_clock_0_out_address_last_time))
        begin
          $write("%0d ns: custom_dma_clock_0_out_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_clock_0_out_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_out_byteenable_last_time <= 0;
      else 
        custom_dma_clock_0_out_byteenable_last_time <= custom_dma_clock_0_out_byteenable;
    end


  //custom_dma_clock_0_out_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_clock_0_out_byteenable != custom_dma_clock_0_out_byteenable_last_time))
        begin
          $write("%0d ns: custom_dma_clock_0_out_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_clock_0_out_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_out_read_last_time <= 0;
      else 
        custom_dma_clock_0_out_read_last_time <= custom_dma_clock_0_out_read;
    end


  //custom_dma_clock_0_out_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_clock_0_out_read != custom_dma_clock_0_out_read_last_time))
        begin
          $write("%0d ns: custom_dma_clock_0_out_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_clock_0_out_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_out_write_last_time <= 0;
      else 
        custom_dma_clock_0_out_write_last_time <= custom_dma_clock_0_out_write;
    end


  //custom_dma_clock_0_out_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_clock_0_out_write != custom_dma_clock_0_out_write_last_time))
        begin
          $write("%0d ns: custom_dma_clock_0_out_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //custom_dma_clock_0_out_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_clock_0_out_writedata_last_time <= 0;
      else 
        custom_dma_clock_0_out_writedata_last_time <= custom_dma_clock_0_out_writedata;
    end


  //custom_dma_clock_0_out_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (custom_dma_clock_0_out_writedata != custom_dma_clock_0_out_writedata_last_time) & custom_dma_clock_0_out_write)
        begin
          $write("%0d ns: custom_dma_clock_0_out_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module burstcount_fifo_for_ddr_sdram_s1_module (
                                                 // inputs:
                                                  clear_fifo,
                                                  clk,
                                                  data_in,
                                                  read,
                                                  reset_n,
                                                  sync_reset,
                                                  write,

                                                 // outputs:
                                                  data_out,
                                                  empty,
                                                  fifo_contains_ones_n,
                                                  full
                                               )
;

  output  [  2: 0] data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input   [  2: 0] data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire    [  2: 0] data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  wire             full_16;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire    [  2: 0] p0_stage_0;
  wire             p10_full_10;
  wire    [  2: 0] p10_stage_10;
  wire             p11_full_11;
  wire    [  2: 0] p11_stage_11;
  wire             p12_full_12;
  wire    [  2: 0] p12_stage_12;
  wire             p13_full_13;
  wire    [  2: 0] p13_stage_13;
  wire             p14_full_14;
  wire    [  2: 0] p14_stage_14;
  wire             p15_full_15;
  wire    [  2: 0] p15_stage_15;
  wire             p1_full_1;
  wire    [  2: 0] p1_stage_1;
  wire             p2_full_2;
  wire    [  2: 0] p2_stage_2;
  wire             p3_full_3;
  wire    [  2: 0] p3_stage_3;
  wire             p4_full_4;
  wire    [  2: 0] p4_stage_4;
  wire             p5_full_5;
  wire    [  2: 0] p5_stage_5;
  wire             p6_full_6;
  wire    [  2: 0] p6_stage_6;
  wire             p7_full_7;
  wire    [  2: 0] p7_stage_7;
  wire             p8_full_8;
  wire    [  2: 0] p8_stage_8;
  wire             p9_full_9;
  wire    [  2: 0] p9_stage_9;
  reg     [  2: 0] stage_0;
  reg     [  2: 0] stage_1;
  reg     [  2: 0] stage_10;
  reg     [  2: 0] stage_11;
  reg     [  2: 0] stage_12;
  reg     [  2: 0] stage_13;
  reg     [  2: 0] stage_14;
  reg     [  2: 0] stage_15;
  reg     [  2: 0] stage_2;
  reg     [  2: 0] stage_3;
  reg     [  2: 0] stage_4;
  reg     [  2: 0] stage_5;
  reg     [  2: 0] stage_6;
  reg     [  2: 0] stage_7;
  reg     [  2: 0] stage_8;
  reg     [  2: 0] stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_15;
  assign empty = !full_0;
  assign full_16 = 0;
  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    0;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_custom_dma_burst_3_downstream_to_ddr_sdram_s1_module (
                                                                           // inputs:
                                                                            clear_fifo,
                                                                            clk,
                                                                            data_in,
                                                                            read,
                                                                            reset_n,
                                                                            sync_reset,
                                                                            write,

                                                                           // outputs:
                                                                            data_out,
                                                                            empty,
                                                                            fifo_contains_ones_n,
                                                                            full
                                                                         )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  wire             full_16;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p10_full_10;
  wire             p10_stage_10;
  wire             p11_full_11;
  wire             p11_stage_11;
  wire             p12_full_12;
  wire             p12_stage_12;
  wire             p13_full_13;
  wire             p13_stage_13;
  wire             p14_full_14;
  wire             p14_stage_14;
  wire             p15_full_15;
  wire             p15_stage_15;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  wire             p6_full_6;
  wire             p6_stage_6;
  wire             p7_full_7;
  wire             p7_stage_7;
  wire             p8_full_8;
  wire             p8_stage_8;
  wire             p9_full_9;
  wire             p9_stage_9;
  reg              stage_0;
  reg              stage_1;
  reg              stage_10;
  reg              stage_11;
  reg              stage_12;
  reg              stage_13;
  reg              stage_14;
  reg              stage_15;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  reg              stage_6;
  reg              stage_7;
  reg              stage_8;
  reg              stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_15;
  assign empty = !full_0;
  assign full_16 = 0;
  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    0;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_custom_dma_burst_4_downstream_to_ddr_sdram_s1_module (
                                                                           // inputs:
                                                                            clear_fifo,
                                                                            clk,
                                                                            data_in,
                                                                            read,
                                                                            reset_n,
                                                                            sync_reset,
                                                                            write,

                                                                           // outputs:
                                                                            data_out,
                                                                            empty,
                                                                            fifo_contains_ones_n,
                                                                            full
                                                                         )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  wire             full_16;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p10_full_10;
  wire             p10_stage_10;
  wire             p11_full_11;
  wire             p11_stage_11;
  wire             p12_full_12;
  wire             p12_stage_12;
  wire             p13_full_13;
  wire             p13_stage_13;
  wire             p14_full_14;
  wire             p14_stage_14;
  wire             p15_full_15;
  wire             p15_stage_15;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  wire             p6_full_6;
  wire             p6_stage_6;
  wire             p7_full_7;
  wire             p7_stage_7;
  wire             p8_full_8;
  wire             p8_stage_8;
  wire             p9_full_9;
  wire             p9_stage_9;
  reg              stage_0;
  reg              stage_1;
  reg              stage_10;
  reg              stage_11;
  reg              stage_12;
  reg              stage_13;
  reg              stage_14;
  reg              stage_15;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  reg              stage_6;
  reg              stage_7;
  reg              stage_8;
  reg              stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_15;
  assign empty = !full_0;
  assign full_16 = 0;
  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    0;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_custom_dma_burst_5_downstream_to_ddr_sdram_s1_module (
                                                                           // inputs:
                                                                            clear_fifo,
                                                                            clk,
                                                                            data_in,
                                                                            read,
                                                                            reset_n,
                                                                            sync_reset,
                                                                            write,

                                                                           // outputs:
                                                                            data_out,
                                                                            empty,
                                                                            fifo_contains_ones_n,
                                                                            full
                                                                         )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_10;
  reg              full_11;
  reg              full_12;
  reg              full_13;
  reg              full_14;
  reg              full_15;
  wire             full_16;
  reg              full_2;
  reg              full_3;
  reg              full_4;
  reg              full_5;
  reg              full_6;
  reg              full_7;
  reg              full_8;
  reg              full_9;
  reg     [  5: 0] how_many_ones;
  wire    [  5: 0] one_count_minus_one;
  wire    [  5: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p10_full_10;
  wire             p10_stage_10;
  wire             p11_full_11;
  wire             p11_stage_11;
  wire             p12_full_12;
  wire             p12_stage_12;
  wire             p13_full_13;
  wire             p13_stage_13;
  wire             p14_full_14;
  wire             p14_stage_14;
  wire             p15_full_15;
  wire             p15_stage_15;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  wire             p4_full_4;
  wire             p4_stage_4;
  wire             p5_full_5;
  wire             p5_stage_5;
  wire             p6_full_6;
  wire             p6_stage_6;
  wire             p7_full_7;
  wire             p7_stage_7;
  wire             p8_full_8;
  wire             p8_stage_8;
  wire             p9_full_9;
  wire             p9_stage_9;
  reg              stage_0;
  reg              stage_1;
  reg              stage_10;
  reg              stage_11;
  reg              stage_12;
  reg              stage_13;
  reg              stage_14;
  reg              stage_15;
  reg              stage_2;
  reg              stage_3;
  reg              stage_4;
  reg              stage_5;
  reg              stage_6;
  reg              stage_7;
  reg              stage_8;
  reg              stage_9;
  wire    [  5: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_15;
  assign empty = !full_0;
  assign full_16 = 0;
  //data_15, which is an e_mux
  assign p15_stage_15 = ((full_16 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_15 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_15))
          if (sync_reset & full_15 & !((full_16 == 0) & read & write))
              stage_15 <= 0;
          else 
            stage_15 <= p15_stage_15;
    end


  //control_15, which is an e_mux
  assign p15_full_15 = ((read & !write) == 0)? full_14 :
    0;

  //control_reg_15, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_15 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_15 <= 0;
          else 
            full_15 <= p15_full_15;
    end


  //data_14, which is an e_mux
  assign p14_stage_14 = ((full_15 & ~clear_fifo) == 0)? data_in :
    stage_15;

  //data_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_14 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_14))
          if (sync_reset & full_14 & !((full_15 == 0) & read & write))
              stage_14 <= 0;
          else 
            stage_14 <= p14_stage_14;
    end


  //control_14, which is an e_mux
  assign p14_full_14 = ((read & !write) == 0)? full_13 :
    full_15;

  //control_reg_14, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_14 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_14 <= 0;
          else 
            full_14 <= p14_full_14;
    end


  //data_13, which is an e_mux
  assign p13_stage_13 = ((full_14 & ~clear_fifo) == 0)? data_in :
    stage_14;

  //data_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_13 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_13))
          if (sync_reset & full_13 & !((full_14 == 0) & read & write))
              stage_13 <= 0;
          else 
            stage_13 <= p13_stage_13;
    end


  //control_13, which is an e_mux
  assign p13_full_13 = ((read & !write) == 0)? full_12 :
    full_14;

  //control_reg_13, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_13 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_13 <= 0;
          else 
            full_13 <= p13_full_13;
    end


  //data_12, which is an e_mux
  assign p12_stage_12 = ((full_13 & ~clear_fifo) == 0)? data_in :
    stage_13;

  //data_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_12 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_12))
          if (sync_reset & full_12 & !((full_13 == 0) & read & write))
              stage_12 <= 0;
          else 
            stage_12 <= p12_stage_12;
    end


  //control_12, which is an e_mux
  assign p12_full_12 = ((read & !write) == 0)? full_11 :
    full_13;

  //control_reg_12, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_12 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_12 <= 0;
          else 
            full_12 <= p12_full_12;
    end


  //data_11, which is an e_mux
  assign p11_stage_11 = ((full_12 & ~clear_fifo) == 0)? data_in :
    stage_12;

  //data_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_11 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_11))
          if (sync_reset & full_11 & !((full_12 == 0) & read & write))
              stage_11 <= 0;
          else 
            stage_11 <= p11_stage_11;
    end


  //control_11, which is an e_mux
  assign p11_full_11 = ((read & !write) == 0)? full_10 :
    full_12;

  //control_reg_11, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_11 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_11 <= 0;
          else 
            full_11 <= p11_full_11;
    end


  //data_10, which is an e_mux
  assign p10_stage_10 = ((full_11 & ~clear_fifo) == 0)? data_in :
    stage_11;

  //data_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_10 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_10))
          if (sync_reset & full_10 & !((full_11 == 0) & read & write))
              stage_10 <= 0;
          else 
            stage_10 <= p10_stage_10;
    end


  //control_10, which is an e_mux
  assign p10_full_10 = ((read & !write) == 0)? full_9 :
    full_11;

  //control_reg_10, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_10 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_10 <= 0;
          else 
            full_10 <= p10_full_10;
    end


  //data_9, which is an e_mux
  assign p9_stage_9 = ((full_10 & ~clear_fifo) == 0)? data_in :
    stage_10;

  //data_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_9 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_9))
          if (sync_reset & full_9 & !((full_10 == 0) & read & write))
              stage_9 <= 0;
          else 
            stage_9 <= p9_stage_9;
    end


  //control_9, which is an e_mux
  assign p9_full_9 = ((read & !write) == 0)? full_8 :
    full_10;

  //control_reg_9, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_9 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_9 <= 0;
          else 
            full_9 <= p9_full_9;
    end


  //data_8, which is an e_mux
  assign p8_stage_8 = ((full_9 & ~clear_fifo) == 0)? data_in :
    stage_9;

  //data_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_8 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_8))
          if (sync_reset & full_8 & !((full_9 == 0) & read & write))
              stage_8 <= 0;
          else 
            stage_8 <= p8_stage_8;
    end


  //control_8, which is an e_mux
  assign p8_full_8 = ((read & !write) == 0)? full_7 :
    full_9;

  //control_reg_8, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_8 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_8 <= 0;
          else 
            full_8 <= p8_full_8;
    end


  //data_7, which is an e_mux
  assign p7_stage_7 = ((full_8 & ~clear_fifo) == 0)? data_in :
    stage_8;

  //data_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_7 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_7))
          if (sync_reset & full_7 & !((full_8 == 0) & read & write))
              stage_7 <= 0;
          else 
            stage_7 <= p7_stage_7;
    end


  //control_7, which is an e_mux
  assign p7_full_7 = ((read & !write) == 0)? full_6 :
    full_8;

  //control_reg_7, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_7 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_7 <= 0;
          else 
            full_7 <= p7_full_7;
    end


  //data_6, which is an e_mux
  assign p6_stage_6 = ((full_7 & ~clear_fifo) == 0)? data_in :
    stage_7;

  //data_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_6 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_6))
          if (sync_reset & full_6 & !((full_7 == 0) & read & write))
              stage_6 <= 0;
          else 
            stage_6 <= p6_stage_6;
    end


  //control_6, which is an e_mux
  assign p6_full_6 = ((read & !write) == 0)? full_5 :
    full_7;

  //control_reg_6, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_6 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_6 <= 0;
          else 
            full_6 <= p6_full_6;
    end


  //data_5, which is an e_mux
  assign p5_stage_5 = ((full_6 & ~clear_fifo) == 0)? data_in :
    stage_6;

  //data_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_5 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_5))
          if (sync_reset & full_5 & !((full_6 == 0) & read & write))
              stage_5 <= 0;
          else 
            stage_5 <= p5_stage_5;
    end


  //control_5, which is an e_mux
  assign p5_full_5 = ((read & !write) == 0)? full_4 :
    full_6;

  //control_reg_5, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_5 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_5 <= 0;
          else 
            full_5 <= p5_full_5;
    end


  //data_4, which is an e_mux
  assign p4_stage_4 = ((full_5 & ~clear_fifo) == 0)? data_in :
    stage_5;

  //data_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_4 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_4))
          if (sync_reset & full_4 & !((full_5 == 0) & read & write))
              stage_4 <= 0;
          else 
            stage_4 <= p4_stage_4;
    end


  //control_4, which is an e_mux
  assign p4_full_4 = ((read & !write) == 0)? full_3 :
    full_5;

  //control_reg_4, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_4 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_4 <= 0;
          else 
            full_4 <= p4_full_4;
    end


  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    stage_4;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    full_4;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ddr_sdram_s1_arbitrator (
                                 // inputs:
                                  clk,
                                  custom_dma_burst_3_downstream_address_to_slave,
                                  custom_dma_burst_3_downstream_arbitrationshare,
                                  custom_dma_burst_3_downstream_burstcount,
                                  custom_dma_burst_3_downstream_byteenable,
                                  custom_dma_burst_3_downstream_latency_counter,
                                  custom_dma_burst_3_downstream_read,
                                  custom_dma_burst_3_downstream_write,
                                  custom_dma_burst_3_downstream_writedata,
                                  custom_dma_burst_4_downstream_address_to_slave,
                                  custom_dma_burst_4_downstream_arbitrationshare,
                                  custom_dma_burst_4_downstream_burstcount,
                                  custom_dma_burst_4_downstream_byteenable,
                                  custom_dma_burst_4_downstream_latency_counter,
                                  custom_dma_burst_4_downstream_read,
                                  custom_dma_burst_4_downstream_write,
                                  custom_dma_burst_4_downstream_writedata,
                                  custom_dma_burst_5_downstream_address_to_slave,
                                  custom_dma_burst_5_downstream_arbitrationshare,
                                  custom_dma_burst_5_downstream_burstcount,
                                  custom_dma_burst_5_downstream_byteenable,
                                  custom_dma_burst_5_downstream_latency_counter,
                                  custom_dma_burst_5_downstream_read,
                                  custom_dma_burst_5_downstream_write,
                                  custom_dma_burst_5_downstream_writedata,
                                  ddr_sdram_s1_readdata,
                                  ddr_sdram_s1_readdatavalid,
                                  ddr_sdram_s1_waitrequest_n,
                                  reset_n,

                                 // outputs:
                                  custom_dma_burst_3_downstream_granted_ddr_sdram_s1,
                                  custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1,
                                  custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1,
                                  custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                  custom_dma_burst_3_downstream_requests_ddr_sdram_s1,
                                  custom_dma_burst_4_downstream_granted_ddr_sdram_s1,
                                  custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1,
                                  custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1,
                                  custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                  custom_dma_burst_4_downstream_requests_ddr_sdram_s1,
                                  custom_dma_burst_5_downstream_granted_ddr_sdram_s1,
                                  custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1,
                                  custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1,
                                  custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register,
                                  custom_dma_burst_5_downstream_requests_ddr_sdram_s1,
                                  d1_ddr_sdram_s1_end_xfer,
                                  ddr_sdram_s1_address,
                                  ddr_sdram_s1_beginbursttransfer,
                                  ddr_sdram_s1_burstcount,
                                  ddr_sdram_s1_byteenable,
                                  ddr_sdram_s1_read,
                                  ddr_sdram_s1_readdata_from_sa,
                                  ddr_sdram_s1_reset_n,
                                  ddr_sdram_s1_waitrequest_n_from_sa,
                                  ddr_sdram_s1_write,
                                  ddr_sdram_s1_writedata
                               )
;

  output           custom_dma_burst_3_downstream_granted_ddr_sdram_s1;
  output           custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1;
  output           custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1;
  output           custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  output           custom_dma_burst_3_downstream_requests_ddr_sdram_s1;
  output           custom_dma_burst_4_downstream_granted_ddr_sdram_s1;
  output           custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1;
  output           custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1;
  output           custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  output           custom_dma_burst_4_downstream_requests_ddr_sdram_s1;
  output           custom_dma_burst_5_downstream_granted_ddr_sdram_s1;
  output           custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1;
  output           custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1;
  output           custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  output           custom_dma_burst_5_downstream_requests_ddr_sdram_s1;
  output           d1_ddr_sdram_s1_end_xfer;
  output  [ 22: 0] ddr_sdram_s1_address;
  output           ddr_sdram_s1_beginbursttransfer;
  output  [  2: 0] ddr_sdram_s1_burstcount;
  output  [  3: 0] ddr_sdram_s1_byteenable;
  output           ddr_sdram_s1_read;
  output  [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  output           ddr_sdram_s1_reset_n;
  output           ddr_sdram_s1_waitrequest_n_from_sa;
  output           ddr_sdram_s1_write;
  output  [ 31: 0] ddr_sdram_s1_writedata;
  input            clk;
  input   [ 24: 0] custom_dma_burst_3_downstream_address_to_slave;
  input   [  3: 0] custom_dma_burst_3_downstream_arbitrationshare;
  input   [  2: 0] custom_dma_burst_3_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_3_downstream_byteenable;
  input            custom_dma_burst_3_downstream_latency_counter;
  input            custom_dma_burst_3_downstream_read;
  input            custom_dma_burst_3_downstream_write;
  input   [ 31: 0] custom_dma_burst_3_downstream_writedata;
  input   [ 24: 0] custom_dma_burst_4_downstream_address_to_slave;
  input   [  3: 0] custom_dma_burst_4_downstream_arbitrationshare;
  input   [  2: 0] custom_dma_burst_4_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_4_downstream_byteenable;
  input            custom_dma_burst_4_downstream_latency_counter;
  input            custom_dma_burst_4_downstream_read;
  input            custom_dma_burst_4_downstream_write;
  input   [ 31: 0] custom_dma_burst_4_downstream_writedata;
  input   [ 24: 0] custom_dma_burst_5_downstream_address_to_slave;
  input   [  2: 0] custom_dma_burst_5_downstream_arbitrationshare;
  input   [  2: 0] custom_dma_burst_5_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_5_downstream_byteenable;
  input            custom_dma_burst_5_downstream_latency_counter;
  input            custom_dma_burst_5_downstream_read;
  input            custom_dma_burst_5_downstream_write;
  input   [ 31: 0] custom_dma_burst_5_downstream_writedata;
  input   [ 31: 0] ddr_sdram_s1_readdata;
  input            ddr_sdram_s1_readdatavalid;
  input            ddr_sdram_s1_waitrequest_n;
  input            reset_n;

  wire             custom_dma_burst_3_downstream_arbiterlock;
  wire             custom_dma_burst_3_downstream_arbiterlock2;
  wire             custom_dma_burst_3_downstream_continuerequest;
  wire             custom_dma_burst_3_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_rdv_fifo_empty_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_rdv_fifo_output_from_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire             custom_dma_burst_3_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_arbiterlock;
  wire             custom_dma_burst_4_downstream_arbiterlock2;
  wire             custom_dma_burst_4_downstream_continuerequest;
  wire             custom_dma_burst_4_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_rdv_fifo_empty_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_rdv_fifo_output_from_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire             custom_dma_burst_4_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_arbiterlock;
  wire             custom_dma_burst_5_downstream_arbiterlock2;
  wire             custom_dma_burst_5_downstream_continuerequest;
  wire             custom_dma_burst_5_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_rdv_fifo_empty_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_rdv_fifo_output_from_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire             custom_dma_burst_5_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1;
  reg              d1_ddr_sdram_s1_end_xfer;
  reg              d1_reasons_to_wait;
  wire    [ 22: 0] ddr_sdram_s1_address;
  wire             ddr_sdram_s1_allgrants;
  wire             ddr_sdram_s1_allow_new_arb_cycle;
  wire             ddr_sdram_s1_any_bursting_master_saved_grant;
  wire             ddr_sdram_s1_any_continuerequest;
  reg     [  2: 0] ddr_sdram_s1_arb_addend;
  wire             ddr_sdram_s1_arb_counter_enable;
  reg     [  3: 0] ddr_sdram_s1_arb_share_counter;
  wire    [  3: 0] ddr_sdram_s1_arb_share_counter_next_value;
  wire    [  3: 0] ddr_sdram_s1_arb_share_set_values;
  wire    [  2: 0] ddr_sdram_s1_arb_winner;
  wire             ddr_sdram_s1_arbitration_holdoff_internal;
  reg     [  1: 0] ddr_sdram_s1_bbt_burstcounter;
  wire             ddr_sdram_s1_beginbursttransfer;
  wire             ddr_sdram_s1_beginbursttransfer_internal;
  wire             ddr_sdram_s1_begins_xfer;
  wire    [  2: 0] ddr_sdram_s1_burstcount;
  wire             ddr_sdram_s1_burstcount_fifo_empty;
  wire    [  3: 0] ddr_sdram_s1_byteenable;
  wire    [  5: 0] ddr_sdram_s1_chosen_master_double_vector;
  wire    [  2: 0] ddr_sdram_s1_chosen_master_rot_left;
  reg     [  2: 0] ddr_sdram_s1_current_burst;
  wire    [  2: 0] ddr_sdram_s1_current_burst_minus_one;
  wire             ddr_sdram_s1_end_xfer;
  wire             ddr_sdram_s1_firsttransfer;
  wire    [  2: 0] ddr_sdram_s1_grant_vector;
  wire             ddr_sdram_s1_in_a_read_cycle;
  wire             ddr_sdram_s1_in_a_write_cycle;
  reg              ddr_sdram_s1_load_fifo;
  wire    [  2: 0] ddr_sdram_s1_master_qreq_vector;
  wire             ddr_sdram_s1_move_on_to_next_transaction;
  wire    [  1: 0] ddr_sdram_s1_next_bbt_burstcount;
  wire    [  2: 0] ddr_sdram_s1_next_burst_count;
  wire             ddr_sdram_s1_non_bursting_master_requests;
  wire             ddr_sdram_s1_read;
  wire    [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  wire             ddr_sdram_s1_readdatavalid_from_sa;
  reg              ddr_sdram_s1_reg_firsttransfer;
  wire             ddr_sdram_s1_reset_n;
  reg     [  2: 0] ddr_sdram_s1_saved_chosen_master_vector;
  wire    [  2: 0] ddr_sdram_s1_selected_burstcount;
  reg              ddr_sdram_s1_slavearbiterlockenable;
  wire             ddr_sdram_s1_slavearbiterlockenable2;
  wire             ddr_sdram_s1_this_cycle_is_the_last_burst;
  wire    [  2: 0] ddr_sdram_s1_transaction_burst_count;
  wire             ddr_sdram_s1_unreg_firsttransfer;
  wire             ddr_sdram_s1_waitrequest_n_from_sa;
  wire             ddr_sdram_s1_waits_for_read;
  wire             ddr_sdram_s1_waits_for_write;
  wire             ddr_sdram_s1_write;
  wire    [ 31: 0] ddr_sdram_s1_writedata;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_ddr_sdram_s1;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  reg              last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1;
  reg              last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1;
  reg              last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1;
  wire             p0_ddr_sdram_s1_load_fifo;
  wire    [ 24: 0] shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_3_downstream;
  wire    [ 24: 0] shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_4_downstream;
  wire    [ 24: 0] shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_5_downstream;
  wire             wait_for_ddr_sdram_s1_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~ddr_sdram_s1_end_xfer;
    end


  assign ddr_sdram_s1_begins_xfer = ~d1_reasons_to_wait & ((custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1 | custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1 | custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1));
  //assign ddr_sdram_s1_readdata_from_sa = ddr_sdram_s1_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign ddr_sdram_s1_readdata_from_sa = ddr_sdram_s1_readdata;

  assign custom_dma_burst_3_downstream_requests_ddr_sdram_s1 = (1) & (custom_dma_burst_3_downstream_read | custom_dma_burst_3_downstream_write);
  //assign ddr_sdram_s1_waitrequest_n_from_sa = ddr_sdram_s1_waitrequest_n so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign ddr_sdram_s1_waitrequest_n_from_sa = ddr_sdram_s1_waitrequest_n;

  //assign ddr_sdram_s1_readdatavalid_from_sa = ddr_sdram_s1_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign ddr_sdram_s1_readdatavalid_from_sa = ddr_sdram_s1_readdatavalid;

  //ddr_sdram_s1_arb_share_counter set values, which is an e_mux
  assign ddr_sdram_s1_arb_share_set_values = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_arbitrationshare :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_arbitrationshare :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_arbitrationshare :
    (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_arbitrationshare :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_arbitrationshare :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_arbitrationshare :
    (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_arbitrationshare :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_arbitrationshare :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_arbitrationshare :
    1;

  //ddr_sdram_s1_non_bursting_master_requests mux, which is an e_mux
  assign ddr_sdram_s1_non_bursting_master_requests = 0;

  //ddr_sdram_s1_any_bursting_master_saved_grant mux, which is an e_mux
  assign ddr_sdram_s1_any_bursting_master_saved_grant = custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 |
    custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1;

  //ddr_sdram_s1_arb_share_counter_next_value assignment, which is an e_assign
  assign ddr_sdram_s1_arb_share_counter_next_value = ddr_sdram_s1_firsttransfer ? (ddr_sdram_s1_arb_share_set_values - 1) : |ddr_sdram_s1_arb_share_counter ? (ddr_sdram_s1_arb_share_counter - 1) : 0;

  //ddr_sdram_s1_allgrants all slave grants, which is an e_mux
  assign ddr_sdram_s1_allgrants = (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector) |
    (|ddr_sdram_s1_grant_vector);

  //ddr_sdram_s1_end_xfer assignment, which is an e_assign
  assign ddr_sdram_s1_end_xfer = ~(ddr_sdram_s1_waits_for_read | ddr_sdram_s1_waits_for_write);

  //end_xfer_arb_share_counter_term_ddr_sdram_s1 arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_ddr_sdram_s1 = ddr_sdram_s1_end_xfer & (~ddr_sdram_s1_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //ddr_sdram_s1_arb_share_counter arbitration counter enable, which is an e_assign
  assign ddr_sdram_s1_arb_counter_enable = (end_xfer_arb_share_counter_term_ddr_sdram_s1 & ddr_sdram_s1_allgrants) | (end_xfer_arb_share_counter_term_ddr_sdram_s1 & ~ddr_sdram_s1_non_bursting_master_requests);

  //ddr_sdram_s1_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_arb_share_counter <= 0;
      else if (ddr_sdram_s1_arb_counter_enable)
          ddr_sdram_s1_arb_share_counter <= ddr_sdram_s1_arb_share_counter_next_value;
    end


  //ddr_sdram_s1_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_slavearbiterlockenable <= 0;
      else if ((|ddr_sdram_s1_master_qreq_vector & end_xfer_arb_share_counter_term_ddr_sdram_s1) | (end_xfer_arb_share_counter_term_ddr_sdram_s1 & ~ddr_sdram_s1_non_bursting_master_requests))
          ddr_sdram_s1_slavearbiterlockenable <= |ddr_sdram_s1_arb_share_counter_next_value;
    end


  //custom_dma_burst_3/downstream ddr_sdram/s1 arbiterlock, which is an e_assign
  assign custom_dma_burst_3_downstream_arbiterlock = ddr_sdram_s1_slavearbiterlockenable & custom_dma_burst_3_downstream_continuerequest;

  //ddr_sdram_s1_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign ddr_sdram_s1_slavearbiterlockenable2 = |ddr_sdram_s1_arb_share_counter_next_value;

  //custom_dma_burst_3/downstream ddr_sdram/s1 arbiterlock2, which is an e_assign
  assign custom_dma_burst_3_downstream_arbiterlock2 = ddr_sdram_s1_slavearbiterlockenable2 & custom_dma_burst_3_downstream_continuerequest;

  //custom_dma_burst_4/downstream ddr_sdram/s1 arbiterlock, which is an e_assign
  assign custom_dma_burst_4_downstream_arbiterlock = ddr_sdram_s1_slavearbiterlockenable & custom_dma_burst_4_downstream_continuerequest;

  //custom_dma_burst_4/downstream ddr_sdram/s1 arbiterlock2, which is an e_assign
  assign custom_dma_burst_4_downstream_arbiterlock2 = ddr_sdram_s1_slavearbiterlockenable2 & custom_dma_burst_4_downstream_continuerequest;

  //custom_dma_burst_4/downstream granted ddr_sdram/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1 <= custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 ? 1 : (ddr_sdram_s1_arbitration_holdoff_internal | 0) ? 0 : last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1;
    end


  //custom_dma_burst_4_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_4_downstream_continuerequest = (last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1 & 1) |
    (last_cycle_custom_dma_burst_4_downstream_granted_slave_ddr_sdram_s1 & 1);

  //ddr_sdram_s1_any_continuerequest at least one master continues requesting, which is an e_mux
  assign ddr_sdram_s1_any_continuerequest = custom_dma_burst_4_downstream_continuerequest |
    custom_dma_burst_5_downstream_continuerequest |
    custom_dma_burst_3_downstream_continuerequest |
    custom_dma_burst_5_downstream_continuerequest |
    custom_dma_burst_3_downstream_continuerequest |
    custom_dma_burst_4_downstream_continuerequest;

  //custom_dma_burst_5/downstream ddr_sdram/s1 arbiterlock, which is an e_assign
  assign custom_dma_burst_5_downstream_arbiterlock = ddr_sdram_s1_slavearbiterlockenable & custom_dma_burst_5_downstream_continuerequest;

  //custom_dma_burst_5/downstream ddr_sdram/s1 arbiterlock2, which is an e_assign
  assign custom_dma_burst_5_downstream_arbiterlock2 = ddr_sdram_s1_slavearbiterlockenable2 & custom_dma_burst_5_downstream_continuerequest;

  //custom_dma_burst_5/downstream granted ddr_sdram/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1 <= custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1 ? 1 : (ddr_sdram_s1_arbitration_holdoff_internal | 0) ? 0 : last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1;
    end


  //custom_dma_burst_5_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_5_downstream_continuerequest = (last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1 & 1) |
    (last_cycle_custom_dma_burst_5_downstream_granted_slave_ddr_sdram_s1 & 1);

  assign custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1 = custom_dma_burst_3_downstream_requests_ddr_sdram_s1 & ~((custom_dma_burst_3_downstream_read & ((custom_dma_burst_3_downstream_latency_counter != 0) | (1 < custom_dma_burst_3_downstream_latency_counter))) | custom_dma_burst_4_downstream_arbiterlock | custom_dma_burst_5_downstream_arbiterlock);
  //unique name for ddr_sdram_s1_move_on_to_next_transaction, which is an e_assign
  assign ddr_sdram_s1_move_on_to_next_transaction = ddr_sdram_s1_this_cycle_is_the_last_burst & ddr_sdram_s1_load_fifo;

  //the currently selected burstcount for ddr_sdram_s1, which is an e_mux
  assign ddr_sdram_s1_selected_burstcount = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_burstcount :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_burstcount :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_burstcount :
    1;

  //burstcount_fifo_for_ddr_sdram_s1, which is an e_fifo_with_registered_outputs
  burstcount_fifo_for_ddr_sdram_s1_module burstcount_fifo_for_ddr_sdram_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (ddr_sdram_s1_selected_burstcount),
      .data_out             (ddr_sdram_s1_transaction_burst_count),
      .empty                (ddr_sdram_s1_burstcount_fifo_empty),
      .fifo_contains_ones_n (),
      .full                 (),
      .read                 (ddr_sdram_s1_this_cycle_is_the_last_burst),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~ddr_sdram_s1_waits_for_read & ddr_sdram_s1_load_fifo & ~(ddr_sdram_s1_this_cycle_is_the_last_burst & ddr_sdram_s1_burstcount_fifo_empty))
    );

  //ddr_sdram_s1 current burst minus one, which is an e_assign
  assign ddr_sdram_s1_current_burst_minus_one = ddr_sdram_s1_current_burst - 1;

  //what to load in current_burst, for ddr_sdram_s1, which is an e_mux
  assign ddr_sdram_s1_next_burst_count = (((in_a_read_cycle & ~ddr_sdram_s1_waits_for_read) & ~ddr_sdram_s1_load_fifo))? ddr_sdram_s1_selected_burstcount :
    ((in_a_read_cycle & ~ddr_sdram_s1_waits_for_read & ddr_sdram_s1_this_cycle_is_the_last_burst & ddr_sdram_s1_burstcount_fifo_empty))? ddr_sdram_s1_selected_burstcount :
    (ddr_sdram_s1_this_cycle_is_the_last_burst)? ddr_sdram_s1_transaction_burst_count :
    ddr_sdram_s1_current_burst_minus_one;

  //the current burst count for ddr_sdram_s1, to be decremented, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_current_burst <= 0;
      else if (ddr_sdram_s1_readdatavalid_from_sa | (~ddr_sdram_s1_load_fifo & (in_a_read_cycle & ~ddr_sdram_s1_waits_for_read)))
          ddr_sdram_s1_current_burst <= ddr_sdram_s1_next_burst_count;
    end


  //a 1 or burstcount fifo empty, to initialize the counter, which is an e_mux
  assign p0_ddr_sdram_s1_load_fifo = (~ddr_sdram_s1_load_fifo)? 1 :
    (((in_a_read_cycle & ~ddr_sdram_s1_waits_for_read) & ddr_sdram_s1_load_fifo))? 1 :
    ~ddr_sdram_s1_burstcount_fifo_empty;

  //whether to load directly to the counter or to the fifo, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_load_fifo <= 0;
      else if ((in_a_read_cycle & ~ddr_sdram_s1_waits_for_read) & ~ddr_sdram_s1_load_fifo | ddr_sdram_s1_this_cycle_is_the_last_burst)
          ddr_sdram_s1_load_fifo <= p0_ddr_sdram_s1_load_fifo;
    end


  //the last cycle in the burst for ddr_sdram_s1, which is an e_assign
  assign ddr_sdram_s1_this_cycle_is_the_last_burst = ~(|ddr_sdram_s1_current_burst_minus_one) & ddr_sdram_s1_readdatavalid_from_sa;

  //rdv_fifo_for_custom_dma_burst_3_downstream_to_ddr_sdram_s1, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_custom_dma_burst_3_downstream_to_ddr_sdram_s1_module rdv_fifo_for_custom_dma_burst_3_downstream_to_ddr_sdram_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_3_downstream_granted_ddr_sdram_s1),
      .data_out             (custom_dma_burst_3_downstream_rdv_fifo_output_from_ddr_sdram_s1),
      .empty                (),
      .fifo_contains_ones_n (custom_dma_burst_3_downstream_rdv_fifo_empty_ddr_sdram_s1),
      .full                 (),
      .read                 (ddr_sdram_s1_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~ddr_sdram_s1_waits_for_read)
    );

  assign custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register = ~custom_dma_burst_3_downstream_rdv_fifo_empty_ddr_sdram_s1;
  //local readdatavalid custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1, which is an e_mux
  assign custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1 = (ddr_sdram_s1_readdatavalid_from_sa & custom_dma_burst_3_downstream_rdv_fifo_output_from_ddr_sdram_s1) & ~ custom_dma_burst_3_downstream_rdv_fifo_empty_ddr_sdram_s1;

  //ddr_sdram_s1_writedata mux, which is an e_mux
  assign ddr_sdram_s1_writedata = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_writedata :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_writedata :
    custom_dma_burst_5_downstream_writedata;

  assign custom_dma_burst_4_downstream_requests_ddr_sdram_s1 = (1) & (custom_dma_burst_4_downstream_read | custom_dma_burst_4_downstream_write);
  //custom_dma_burst_3/downstream granted ddr_sdram/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1 <= custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 ? 1 : (ddr_sdram_s1_arbitration_holdoff_internal | 0) ? 0 : last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1;
    end


  //custom_dma_burst_3_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_3_downstream_continuerequest = (last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1 & 1) |
    (last_cycle_custom_dma_burst_3_downstream_granted_slave_ddr_sdram_s1 & 1);

  assign custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1 = custom_dma_burst_4_downstream_requests_ddr_sdram_s1 & ~((custom_dma_burst_4_downstream_read & ((custom_dma_burst_4_downstream_latency_counter != 0) | (1 < custom_dma_burst_4_downstream_latency_counter))) | custom_dma_burst_3_downstream_arbiterlock | custom_dma_burst_5_downstream_arbiterlock);
  //rdv_fifo_for_custom_dma_burst_4_downstream_to_ddr_sdram_s1, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_custom_dma_burst_4_downstream_to_ddr_sdram_s1_module rdv_fifo_for_custom_dma_burst_4_downstream_to_ddr_sdram_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_4_downstream_granted_ddr_sdram_s1),
      .data_out             (custom_dma_burst_4_downstream_rdv_fifo_output_from_ddr_sdram_s1),
      .empty                (),
      .fifo_contains_ones_n (custom_dma_burst_4_downstream_rdv_fifo_empty_ddr_sdram_s1),
      .full                 (),
      .read                 (ddr_sdram_s1_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~ddr_sdram_s1_waits_for_read)
    );

  assign custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register = ~custom_dma_burst_4_downstream_rdv_fifo_empty_ddr_sdram_s1;
  //local readdatavalid custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1, which is an e_mux
  assign custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1 = (ddr_sdram_s1_readdatavalid_from_sa & custom_dma_burst_4_downstream_rdv_fifo_output_from_ddr_sdram_s1) & ~ custom_dma_burst_4_downstream_rdv_fifo_empty_ddr_sdram_s1;

  assign custom_dma_burst_5_downstream_requests_ddr_sdram_s1 = (1) & (custom_dma_burst_5_downstream_read | custom_dma_burst_5_downstream_write);
  assign custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1 = custom_dma_burst_5_downstream_requests_ddr_sdram_s1 & ~((custom_dma_burst_5_downstream_read & ((custom_dma_burst_5_downstream_latency_counter != 0) | (1 < custom_dma_burst_5_downstream_latency_counter))) | custom_dma_burst_3_downstream_arbiterlock | custom_dma_burst_4_downstream_arbiterlock);
  //rdv_fifo_for_custom_dma_burst_5_downstream_to_ddr_sdram_s1, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_custom_dma_burst_5_downstream_to_ddr_sdram_s1_module rdv_fifo_for_custom_dma_burst_5_downstream_to_ddr_sdram_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_5_downstream_granted_ddr_sdram_s1),
      .data_out             (custom_dma_burst_5_downstream_rdv_fifo_output_from_ddr_sdram_s1),
      .empty                (),
      .fifo_contains_ones_n (custom_dma_burst_5_downstream_rdv_fifo_empty_ddr_sdram_s1),
      .full                 (),
      .read                 (ddr_sdram_s1_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~ddr_sdram_s1_waits_for_read)
    );

  assign custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register = ~custom_dma_burst_5_downstream_rdv_fifo_empty_ddr_sdram_s1;
  //local readdatavalid custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1, which is an e_mux
  assign custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1 = (ddr_sdram_s1_readdatavalid_from_sa & custom_dma_burst_5_downstream_rdv_fifo_output_from_ddr_sdram_s1) & ~ custom_dma_burst_5_downstream_rdv_fifo_empty_ddr_sdram_s1;

  //allow new arb cycle for ddr_sdram/s1, which is an e_assign
  assign ddr_sdram_s1_allow_new_arb_cycle = ~custom_dma_burst_3_downstream_arbiterlock & ~custom_dma_burst_4_downstream_arbiterlock & ~custom_dma_burst_5_downstream_arbiterlock;

  //custom_dma_burst_5/downstream assignment into master qualified-requests vector for ddr_sdram/s1, which is an e_assign
  assign ddr_sdram_s1_master_qreq_vector[0] = custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1;

  //custom_dma_burst_5/downstream grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_5_downstream_granted_ddr_sdram_s1 = ddr_sdram_s1_grant_vector[0];

  //custom_dma_burst_5/downstream saved-grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1 = ddr_sdram_s1_arb_winner[0];

  //custom_dma_burst_4/downstream assignment into master qualified-requests vector for ddr_sdram/s1, which is an e_assign
  assign ddr_sdram_s1_master_qreq_vector[1] = custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1;

  //custom_dma_burst_4/downstream grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_4_downstream_granted_ddr_sdram_s1 = ddr_sdram_s1_grant_vector[1];

  //custom_dma_burst_4/downstream saved-grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 = ddr_sdram_s1_arb_winner[1];

  //custom_dma_burst_3/downstream assignment into master qualified-requests vector for ddr_sdram/s1, which is an e_assign
  assign ddr_sdram_s1_master_qreq_vector[2] = custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1;

  //custom_dma_burst_3/downstream grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_3_downstream_granted_ddr_sdram_s1 = ddr_sdram_s1_grant_vector[2];

  //custom_dma_burst_3/downstream saved-grant ddr_sdram/s1, which is an e_assign
  assign custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 = ddr_sdram_s1_arb_winner[2];

  //ddr_sdram/s1 chosen-master double-vector, which is an e_assign
  assign ddr_sdram_s1_chosen_master_double_vector = {ddr_sdram_s1_master_qreq_vector, ddr_sdram_s1_master_qreq_vector} & ({~ddr_sdram_s1_master_qreq_vector, ~ddr_sdram_s1_master_qreq_vector} + ddr_sdram_s1_arb_addend);

  //stable onehot encoding of arb winner
  assign ddr_sdram_s1_arb_winner = (ddr_sdram_s1_allow_new_arb_cycle & | ddr_sdram_s1_grant_vector) ? ddr_sdram_s1_grant_vector : ddr_sdram_s1_saved_chosen_master_vector;

  //saved ddr_sdram_s1_grant_vector, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_saved_chosen_master_vector <= 0;
      else if (ddr_sdram_s1_allow_new_arb_cycle)
          ddr_sdram_s1_saved_chosen_master_vector <= |ddr_sdram_s1_grant_vector ? ddr_sdram_s1_grant_vector : ddr_sdram_s1_saved_chosen_master_vector;
    end


  //onehot encoding of chosen master
  assign ddr_sdram_s1_grant_vector = {(ddr_sdram_s1_chosen_master_double_vector[2] | ddr_sdram_s1_chosen_master_double_vector[5]),
    (ddr_sdram_s1_chosen_master_double_vector[1] | ddr_sdram_s1_chosen_master_double_vector[4]),
    (ddr_sdram_s1_chosen_master_double_vector[0] | ddr_sdram_s1_chosen_master_double_vector[3])};

  //ddr_sdram/s1 chosen master rotated left, which is an e_assign
  assign ddr_sdram_s1_chosen_master_rot_left = (ddr_sdram_s1_arb_winner << 1) ? (ddr_sdram_s1_arb_winner << 1) : 1;

  //ddr_sdram/s1's addend for next-master-grant
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_arb_addend <= 1;
      else if (|ddr_sdram_s1_grant_vector)
          ddr_sdram_s1_arb_addend <= ddr_sdram_s1_end_xfer? ddr_sdram_s1_chosen_master_rot_left : ddr_sdram_s1_grant_vector;
    end


  //ddr_sdram_s1_reset_n assignment, which is an e_assign
  assign ddr_sdram_s1_reset_n = reset_n;

  //ddr_sdram_s1_firsttransfer first transaction, which is an e_assign
  assign ddr_sdram_s1_firsttransfer = ddr_sdram_s1_begins_xfer ? ddr_sdram_s1_unreg_firsttransfer : ddr_sdram_s1_reg_firsttransfer;

  //ddr_sdram_s1_unreg_firsttransfer first transaction, which is an e_assign
  assign ddr_sdram_s1_unreg_firsttransfer = ~(ddr_sdram_s1_slavearbiterlockenable & ddr_sdram_s1_any_continuerequest);

  //ddr_sdram_s1_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_reg_firsttransfer <= 1'b1;
      else if (ddr_sdram_s1_begins_xfer)
          ddr_sdram_s1_reg_firsttransfer <= ddr_sdram_s1_unreg_firsttransfer;
    end


  //ddr_sdram_s1_next_bbt_burstcount next_bbt_burstcount, which is an e_mux
  assign ddr_sdram_s1_next_bbt_burstcount = ((((ddr_sdram_s1_write) && (ddr_sdram_s1_bbt_burstcounter == 0))))? (ddr_sdram_s1_burstcount - 1) :
    ((((ddr_sdram_s1_read) && (ddr_sdram_s1_bbt_burstcounter == 0))))? 0 :
    (ddr_sdram_s1_bbt_burstcounter - 1);

  //ddr_sdram_s1_bbt_burstcounter bbt_burstcounter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ddr_sdram_s1_bbt_burstcounter <= 0;
      else if (ddr_sdram_s1_begins_xfer)
          ddr_sdram_s1_bbt_burstcounter <= ddr_sdram_s1_next_bbt_burstcount;
    end


  //ddr_sdram_s1_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign ddr_sdram_s1_beginbursttransfer_internal = ddr_sdram_s1_begins_xfer & (ddr_sdram_s1_bbt_burstcounter == 0);

  //ddr_sdram/s1 begin burst transfer to slave, which is an e_assign
  assign ddr_sdram_s1_beginbursttransfer = ddr_sdram_s1_beginbursttransfer_internal;

  //ddr_sdram_s1_arbitration_holdoff_internal arbitration_holdoff, which is an e_assign
  assign ddr_sdram_s1_arbitration_holdoff_internal = ddr_sdram_s1_begins_xfer & ddr_sdram_s1_firsttransfer;

  //ddr_sdram_s1_read assignment, which is an e_mux
  assign ddr_sdram_s1_read = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 & custom_dma_burst_3_downstream_read) | (custom_dma_burst_4_downstream_granted_ddr_sdram_s1 & custom_dma_burst_4_downstream_read) | (custom_dma_burst_5_downstream_granted_ddr_sdram_s1 & custom_dma_burst_5_downstream_read);

  //ddr_sdram_s1_write assignment, which is an e_mux
  assign ddr_sdram_s1_write = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 & custom_dma_burst_3_downstream_write) | (custom_dma_burst_4_downstream_granted_ddr_sdram_s1 & custom_dma_burst_4_downstream_write) | (custom_dma_burst_5_downstream_granted_ddr_sdram_s1 & custom_dma_burst_5_downstream_write);

  assign shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_3_downstream = custom_dma_burst_3_downstream_address_to_slave;
  //ddr_sdram_s1_address mux, which is an e_mux
  assign ddr_sdram_s1_address = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? (shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_3_downstream >> 2) :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? (shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_4_downstream >> 2) :
    (shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_5_downstream >> 2);

  assign shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_4_downstream = custom_dma_burst_4_downstream_address_to_slave;
  assign shifted_address_to_ddr_sdram_s1_from_custom_dma_burst_5_downstream = custom_dma_burst_5_downstream_address_to_slave;
  //d1_ddr_sdram_s1_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_ddr_sdram_s1_end_xfer <= 1;
      else 
        d1_ddr_sdram_s1_end_xfer <= ddr_sdram_s1_end_xfer;
    end


  //ddr_sdram_s1_waits_for_read in a cycle, which is an e_mux
  assign ddr_sdram_s1_waits_for_read = ddr_sdram_s1_in_a_read_cycle & ~ddr_sdram_s1_waitrequest_n_from_sa;

  //ddr_sdram_s1_in_a_read_cycle assignment, which is an e_assign
  assign ddr_sdram_s1_in_a_read_cycle = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 & custom_dma_burst_3_downstream_read) | (custom_dma_burst_4_downstream_granted_ddr_sdram_s1 & custom_dma_burst_4_downstream_read) | (custom_dma_burst_5_downstream_granted_ddr_sdram_s1 & custom_dma_burst_5_downstream_read);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = ddr_sdram_s1_in_a_read_cycle;

  //ddr_sdram_s1_waits_for_write in a cycle, which is an e_mux
  assign ddr_sdram_s1_waits_for_write = ddr_sdram_s1_in_a_write_cycle & ~ddr_sdram_s1_waitrequest_n_from_sa;

  //ddr_sdram_s1_in_a_write_cycle assignment, which is an e_assign
  assign ddr_sdram_s1_in_a_write_cycle = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 & custom_dma_burst_3_downstream_write) | (custom_dma_burst_4_downstream_granted_ddr_sdram_s1 & custom_dma_burst_4_downstream_write) | (custom_dma_burst_5_downstream_granted_ddr_sdram_s1 & custom_dma_burst_5_downstream_write);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = ddr_sdram_s1_in_a_write_cycle;

  assign wait_for_ddr_sdram_s1_counter = 0;
  //ddr_sdram_s1_byteenable byte enable port mux, which is an e_mux
  assign ddr_sdram_s1_byteenable = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_byteenable :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_byteenable :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign ddr_sdram_s1_burstcount = (custom_dma_burst_3_downstream_granted_ddr_sdram_s1)? custom_dma_burst_3_downstream_burstcount :
    (custom_dma_burst_4_downstream_granted_ddr_sdram_s1)? custom_dma_burst_4_downstream_burstcount :
    (custom_dma_burst_5_downstream_granted_ddr_sdram_s1)? custom_dma_burst_5_downstream_burstcount :
    1;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //ddr_sdram/s1 enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //custom_dma_burst_3/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_3_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_3_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_3/downstream drove 0 on its 'arbitrationshare' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_3/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_3_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_3_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_3/downstream drove 0 on its 'burstcount' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_4/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_4_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_4_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_4/downstream drove 0 on its 'arbitrationshare' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_4/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_4_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_4_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_4/downstream drove 0 on its 'burstcount' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_5/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_5_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_5_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_5/downstream drove 0 on its 'arbitrationshare' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_5/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_5_downstream_requests_ddr_sdram_s1 && (custom_dma_burst_5_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_5/downstream drove 0 on its 'burstcount' port while accessing slave ddr_sdram/s1", $time);
          $stop;
        end
    end


  //grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_3_downstream_granted_ddr_sdram_s1 + custom_dma_burst_4_downstream_granted_ddr_sdram_s1 + custom_dma_burst_5_downstream_granted_ddr_sdram_s1 > 1)
        begin
          $write("%0d ns: > 1 of grant signals are active simultaneously", $time);
          $stop;
        end
    end


  //saved_grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_3_downstream_saved_grant_ddr_sdram_s1 + custom_dma_burst_4_downstream_saved_grant_ddr_sdram_s1 + custom_dma_burst_5_downstream_saved_grant_ddr_sdram_s1 > 1)
        begin
          $write("%0d ns: > 1 of saved_grant signals are active simultaneously", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_bus_avalon_slave_arbitrator (
                                               // inputs:
                                                clk,
                                                custom_dma_burst_0_downstream_address_to_slave,
                                                custom_dma_burst_0_downstream_arbitrationshare,
                                                custom_dma_burst_0_downstream_burstcount,
                                                custom_dma_burst_0_downstream_byteenable,
                                                custom_dma_burst_0_downstream_latency_counter,
                                                custom_dma_burst_0_downstream_read,
                                                custom_dma_burst_0_downstream_write,
                                                custom_dma_burst_0_downstream_writedata,
                                                fir_dma_read_master_address_to_slave,
                                                fir_dma_read_master_latency_counter,
                                                fir_dma_read_master_read,
                                                reset_n,

                                               // outputs:
                                                adsc_n_to_the_ext_ssram,
                                                bw_n_to_the_ext_ssram,
                                                bwe_n_to_the_ext_ssram,
                                                chipenable1_n_to_the_ext_ssram,
                                                custom_dma_burst_0_downstream_granted_ext_ssram_s1,
                                                custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1,
                                                custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1,
                                                custom_dma_burst_0_downstream_requests_ext_ssram_s1,
                                                d1_ext_ssram_bus_avalon_slave_end_xfer,
                                                ext_ssram_bus_address,
                                                ext_ssram_bus_data,
                                                fir_dma_read_master_granted_ext_ssram_s1,
                                                fir_dma_read_master_qualified_request_ext_ssram_s1,
                                                fir_dma_read_master_read_data_valid_ext_ssram_s1,
                                                fir_dma_read_master_requests_ext_ssram_s1,
                                                incoming_ext_ssram_bus_data,
                                                outputenable_n_to_the_ext_ssram
                                             )
;

  output           adsc_n_to_the_ext_ssram;
  output  [  3: 0] bw_n_to_the_ext_ssram;
  output           bwe_n_to_the_ext_ssram;
  output           chipenable1_n_to_the_ext_ssram;
  output           custom_dma_burst_0_downstream_granted_ext_ssram_s1;
  output           custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1;
  output           custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1;
  output           custom_dma_burst_0_downstream_requests_ext_ssram_s1;
  output           d1_ext_ssram_bus_avalon_slave_end_xfer;
  output  [ 20: 0] ext_ssram_bus_address;
  inout   [ 31: 0] ext_ssram_bus_data;
  output           fir_dma_read_master_granted_ext_ssram_s1;
  output           fir_dma_read_master_qualified_request_ext_ssram_s1;
  output           fir_dma_read_master_read_data_valid_ext_ssram_s1;
  output           fir_dma_read_master_requests_ext_ssram_s1;
  output  [ 31: 0] incoming_ext_ssram_bus_data;
  output           outputenable_n_to_the_ext_ssram;
  input            clk;
  input   [ 20: 0] custom_dma_burst_0_downstream_address_to_slave;
  input   [  3: 0] custom_dma_burst_0_downstream_arbitrationshare;
  input            custom_dma_burst_0_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_0_downstream_byteenable;
  input   [  2: 0] custom_dma_burst_0_downstream_latency_counter;
  input            custom_dma_burst_0_downstream_read;
  input            custom_dma_burst_0_downstream_write;
  input   [ 31: 0] custom_dma_burst_0_downstream_writedata;
  input   [ 31: 0] fir_dma_read_master_address_to_slave;
  input   [  2: 0] fir_dma_read_master_latency_counter;
  input            fir_dma_read_master_read;
  input            reset_n;

  reg              adsc_n_to_the_ext_ssram /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  reg     [  3: 0] bw_n_to_the_ext_ssram /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  reg              bwe_n_to_the_ext_ssram /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  reg              chipenable1_n_to_the_ext_ssram /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  wire             custom_dma_burst_0_downstream_arbiterlock;
  wire             custom_dma_burst_0_downstream_arbiterlock2;
  wire             custom_dma_burst_0_downstream_continuerequest;
  wire             custom_dma_burst_0_downstream_granted_ext_ssram_s1;
  wire             custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1;
  wire             custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1;
  reg     [  3: 0] custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register;
  wire             custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register_in;
  wire             custom_dma_burst_0_downstream_requests_ext_ssram_s1;
  wire             custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1;
  reg              d1_ext_ssram_bus_avalon_slave_end_xfer;
  reg              d1_in_a_write_cycle /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_ENABLE_REGISTER=ON"  */;
  reg     [ 31: 0] d1_outgoing_ext_ssram_bus_data /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave;
  reg     [ 20: 0] ext_ssram_bus_address /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  wire             ext_ssram_bus_avalon_slave_allgrants;
  wire             ext_ssram_bus_avalon_slave_allow_new_arb_cycle;
  wire             ext_ssram_bus_avalon_slave_any_bursting_master_saved_grant;
  wire             ext_ssram_bus_avalon_slave_any_continuerequest;
  reg     [  1: 0] ext_ssram_bus_avalon_slave_arb_addend;
  wire             ext_ssram_bus_avalon_slave_arb_counter_enable;
  reg     [  3: 0] ext_ssram_bus_avalon_slave_arb_share_counter;
  wire    [  3: 0] ext_ssram_bus_avalon_slave_arb_share_counter_next_value;
  wire    [  3: 0] ext_ssram_bus_avalon_slave_arb_share_set_values;
  wire    [  1: 0] ext_ssram_bus_avalon_slave_arb_winner;
  wire             ext_ssram_bus_avalon_slave_arbitration_holdoff_internal;
  wire             ext_ssram_bus_avalon_slave_beginbursttransfer_internal;
  wire             ext_ssram_bus_avalon_slave_begins_xfer;
  wire    [  3: 0] ext_ssram_bus_avalon_slave_chosen_master_double_vector;
  wire    [  1: 0] ext_ssram_bus_avalon_slave_chosen_master_rot_left;
  wire             ext_ssram_bus_avalon_slave_end_xfer;
  wire             ext_ssram_bus_avalon_slave_firsttransfer;
  wire    [  1: 0] ext_ssram_bus_avalon_slave_grant_vector;
  wire    [  1: 0] ext_ssram_bus_avalon_slave_master_qreq_vector;
  wire             ext_ssram_bus_avalon_slave_non_bursting_master_requests;
  wire             ext_ssram_bus_avalon_slave_read_pending;
  reg              ext_ssram_bus_avalon_slave_reg_firsttransfer;
  reg     [  1: 0] ext_ssram_bus_avalon_slave_saved_chosen_master_vector;
  reg              ext_ssram_bus_avalon_slave_slavearbiterlockenable;
  wire             ext_ssram_bus_avalon_slave_slavearbiterlockenable2;
  wire             ext_ssram_bus_avalon_slave_unreg_firsttransfer;
  wire             ext_ssram_bus_avalon_slave_write_pending;
  wire    [ 31: 0] ext_ssram_bus_data;
  wire             ext_ssram_s1_in_a_read_cycle;
  wire             ext_ssram_s1_in_a_write_cycle;
  wire             ext_ssram_s1_waits_for_read;
  wire             ext_ssram_s1_waits_for_write;
  wire             ext_ssram_s1_with_write_latency;
  wire             fir_dma_read_master_arbiterlock;
  wire             fir_dma_read_master_arbiterlock2;
  wire             fir_dma_read_master_continuerequest;
  wire             fir_dma_read_master_granted_ext_ssram_s1;
  wire             fir_dma_read_master_qualified_request_ext_ssram_s1;
  wire             fir_dma_read_master_read_data_valid_ext_ssram_s1;
  reg     [  3: 0] fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register;
  wire             fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register_in;
  wire             fir_dma_read_master_requests_ext_ssram_s1;
  wire             fir_dma_read_master_saved_grant_ext_ssram_s1;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  reg     [ 31: 0] incoming_ext_ssram_bus_data /* synthesis ALTERA_ATTRIBUTE = "FAST_INPUT_REGISTER=ON"  */;
  reg              last_cycle_custom_dma_burst_0_downstream_granted_slave_ext_ssram_s1;
  reg              last_cycle_fir_dma_read_master_granted_slave_ext_ssram_s1;
  wire    [ 31: 0] outgoing_ext_ssram_bus_data;
  reg              outputenable_n_to_the_ext_ssram /* synthesis ALTERA_ATTRIBUTE = "FAST_OUTPUT_REGISTER=ON"  */;
  wire             p1_adsc_n_to_the_ext_ssram;
  wire    [  3: 0] p1_bw_n_to_the_ext_ssram;
  wire             p1_bwe_n_to_the_ext_ssram;
  wire             p1_chipenable1_n_to_the_ext_ssram;
  wire    [  3: 0] p1_custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register;
  wire    [ 20: 0] p1_ext_ssram_bus_address;
  wire    [  3: 0] p1_fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register;
  wire             p1_outputenable_n_to_the_ext_ssram;
  wire             time_to_write;
  wire             wait_for_ext_ssram_s1_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~ext_ssram_bus_avalon_slave_end_xfer;
    end


  assign ext_ssram_bus_avalon_slave_begins_xfer = ~d1_reasons_to_wait & ((custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 | fir_dma_read_master_qualified_request_ext_ssram_s1));
  assign custom_dma_burst_0_downstream_requests_ext_ssram_s1 = (1) & (custom_dma_burst_0_downstream_read | custom_dma_burst_0_downstream_write);
  //~chipenable1_n_to_the_ext_ssram of type chipselect to ~p1_chipenable1_n_to_the_ext_ssram, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          chipenable1_n_to_the_ext_ssram <= ~0;
      else 
        chipenable1_n_to_the_ext_ssram <= p1_chipenable1_n_to_the_ext_ssram;
    end


  assign ext_ssram_bus_avalon_slave_write_pending = 0;
  //ext_ssram_bus/avalon_slave read pending calc, which is an e_assign
  assign ext_ssram_bus_avalon_slave_read_pending = (|custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | (|fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[1 : 0]);

  //ext_ssram_bus_avalon_slave_arb_share_counter set values, which is an e_mux
  assign ext_ssram_bus_avalon_slave_arb_share_set_values = (custom_dma_burst_0_downstream_granted_ext_ssram_s1)? custom_dma_burst_0_downstream_arbitrationshare :
    (custom_dma_burst_0_downstream_granted_ext_ssram_s1)? custom_dma_burst_0_downstream_arbitrationshare :
    1;

  //ext_ssram_bus_avalon_slave_non_bursting_master_requests mux, which is an e_mux
  assign ext_ssram_bus_avalon_slave_non_bursting_master_requests = 0 |
    fir_dma_read_master_requests_ext_ssram_s1 |
    fir_dma_read_master_requests_ext_ssram_s1;

  //ext_ssram_bus_avalon_slave_any_bursting_master_saved_grant mux, which is an e_mux
  assign ext_ssram_bus_avalon_slave_any_bursting_master_saved_grant = custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1 |
    custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1;

  //ext_ssram_bus_avalon_slave_arb_share_counter_next_value assignment, which is an e_assign
  assign ext_ssram_bus_avalon_slave_arb_share_counter_next_value = ext_ssram_bus_avalon_slave_firsttransfer ? (ext_ssram_bus_avalon_slave_arb_share_set_values - 1) : |ext_ssram_bus_avalon_slave_arb_share_counter ? (ext_ssram_bus_avalon_slave_arb_share_counter - 1) : 0;

  //ext_ssram_bus_avalon_slave_allgrants all slave grants, which is an e_mux
  assign ext_ssram_bus_avalon_slave_allgrants = (|ext_ssram_bus_avalon_slave_grant_vector) |
    (|ext_ssram_bus_avalon_slave_grant_vector) |
    (|ext_ssram_bus_avalon_slave_grant_vector) |
    (|ext_ssram_bus_avalon_slave_grant_vector);

  //ext_ssram_bus_avalon_slave_end_xfer assignment, which is an e_assign
  assign ext_ssram_bus_avalon_slave_end_xfer = ~(ext_ssram_s1_waits_for_read | ext_ssram_s1_waits_for_write);

  //end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave = ext_ssram_bus_avalon_slave_end_xfer & (~ext_ssram_bus_avalon_slave_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //ext_ssram_bus_avalon_slave_arb_share_counter arbitration counter enable, which is an e_assign
  assign ext_ssram_bus_avalon_slave_arb_counter_enable = (end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave & ext_ssram_bus_avalon_slave_allgrants) | (end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave & ~ext_ssram_bus_avalon_slave_non_bursting_master_requests);

  //ext_ssram_bus_avalon_slave_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_avalon_slave_arb_share_counter <= 0;
      else if (ext_ssram_bus_avalon_slave_arb_counter_enable)
          ext_ssram_bus_avalon_slave_arb_share_counter <= ext_ssram_bus_avalon_slave_arb_share_counter_next_value;
    end


  //ext_ssram_bus_avalon_slave_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_avalon_slave_slavearbiterlockenable <= 0;
      else if ((|ext_ssram_bus_avalon_slave_master_qreq_vector & end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave) | (end_xfer_arb_share_counter_term_ext_ssram_bus_avalon_slave & ~ext_ssram_bus_avalon_slave_non_bursting_master_requests))
          ext_ssram_bus_avalon_slave_slavearbiterlockenable <= |ext_ssram_bus_avalon_slave_arb_share_counter_next_value;
    end


  //custom_dma_burst_0/downstream ext_ssram_bus/avalon_slave arbiterlock, which is an e_assign
  assign custom_dma_burst_0_downstream_arbiterlock = ext_ssram_bus_avalon_slave_slavearbiterlockenable & custom_dma_burst_0_downstream_continuerequest;

  //ext_ssram_bus_avalon_slave_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign ext_ssram_bus_avalon_slave_slavearbiterlockenable2 = |ext_ssram_bus_avalon_slave_arb_share_counter_next_value;

  //custom_dma_burst_0/downstream ext_ssram_bus/avalon_slave arbiterlock2, which is an e_assign
  assign custom_dma_burst_0_downstream_arbiterlock2 = ext_ssram_bus_avalon_slave_slavearbiterlockenable2 & custom_dma_burst_0_downstream_continuerequest;

  //fir_dma/read_master ext_ssram_bus/avalon_slave arbiterlock, which is an e_assign
  assign fir_dma_read_master_arbiterlock = ext_ssram_bus_avalon_slave_slavearbiterlockenable & fir_dma_read_master_continuerequest;

  //fir_dma/read_master ext_ssram_bus/avalon_slave arbiterlock2, which is an e_assign
  assign fir_dma_read_master_arbiterlock2 = ext_ssram_bus_avalon_slave_slavearbiterlockenable2 & fir_dma_read_master_continuerequest;

  //fir_dma/read_master granted ext_ssram/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_fir_dma_read_master_granted_slave_ext_ssram_s1 <= 0;
      else 
        last_cycle_fir_dma_read_master_granted_slave_ext_ssram_s1 <= fir_dma_read_master_saved_grant_ext_ssram_s1 ? 1 : (ext_ssram_bus_avalon_slave_arbitration_holdoff_internal | 0) ? 0 : last_cycle_fir_dma_read_master_granted_slave_ext_ssram_s1;
    end


  //fir_dma_read_master_continuerequest continued request, which is an e_mux
  assign fir_dma_read_master_continuerequest = last_cycle_fir_dma_read_master_granted_slave_ext_ssram_s1 & fir_dma_read_master_requests_ext_ssram_s1;

  //ext_ssram_bus_avalon_slave_any_continuerequest at least one master continues requesting, which is an e_mux
  assign ext_ssram_bus_avalon_slave_any_continuerequest = fir_dma_read_master_continuerequest |
    custom_dma_burst_0_downstream_continuerequest;

  assign custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 = custom_dma_burst_0_downstream_requests_ext_ssram_s1 & ~((custom_dma_burst_0_downstream_read & (ext_ssram_bus_avalon_slave_write_pending | (ext_ssram_bus_avalon_slave_read_pending & !((((|custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | (|fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[1 : 0]))))))) | ((ext_ssram_bus_avalon_slave_read_pending) & custom_dma_burst_0_downstream_write) | fir_dma_read_master_arbiterlock);
  //custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register_in mux for readlatency shift register, which is an e_mux
  assign custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register_in = custom_dma_burst_0_downstream_granted_ext_ssram_s1 & custom_dma_burst_0_downstream_read & ~ext_ssram_s1_waits_for_read;

  //shift register p1 custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register in if flush, otherwise shift left, which is an e_mux
  assign p1_custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register = {custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register, custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register_in};

  //custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register for remembering which master asked for a fixed latency read, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register <= 0;
      else 
        custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register <= p1_custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register;
    end


  //local readdatavalid custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1, which is an e_mux
  assign custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1 = custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[3];

  //ext_ssram_bus_data register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          incoming_ext_ssram_bus_data <= 0;
      else 
        incoming_ext_ssram_bus_data <= ext_ssram_bus_data;
    end


  //ext_ssram_s1_with_write_latency assignment, which is an e_assign
  assign ext_ssram_s1_with_write_latency = in_a_write_cycle & (custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 | fir_dma_read_master_qualified_request_ext_ssram_s1);

  //time to write the data, which is an e_mux
  assign time_to_write = (ext_ssram_s1_with_write_latency)? 1 :
    0;

  //d1_outgoing_ext_ssram_bus_data register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_outgoing_ext_ssram_bus_data <= 0;
      else 
        d1_outgoing_ext_ssram_bus_data <= outgoing_ext_ssram_bus_data;
    end


  //write cycle delayed by 1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_in_a_write_cycle <= 0;
      else 
        d1_in_a_write_cycle <= time_to_write;
    end


  //d1_outgoing_ext_ssram_bus_data tristate driver, which is an e_assign
  assign ext_ssram_bus_data = (d1_in_a_write_cycle)? d1_outgoing_ext_ssram_bus_data:{32{1'bz}};

  //outgoing_ext_ssram_bus_data mux, which is an e_mux
  assign outgoing_ext_ssram_bus_data = custom_dma_burst_0_downstream_writedata;

  assign fir_dma_read_master_requests_ext_ssram_s1 = (({fir_dma_read_master_address_to_slave[31 : 21] , 21'b0} == 32'h6000000) & (fir_dma_read_master_read)) & fir_dma_read_master_read;
  //custom_dma_burst_0/downstream granted ext_ssram/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_0_downstream_granted_slave_ext_ssram_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_0_downstream_granted_slave_ext_ssram_s1 <= custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1 ? 1 : (ext_ssram_bus_avalon_slave_arbitration_holdoff_internal | ~custom_dma_burst_0_downstream_requests_ext_ssram_s1) ? 0 : last_cycle_custom_dma_burst_0_downstream_granted_slave_ext_ssram_s1;
    end


  //custom_dma_burst_0_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_0_downstream_continuerequest = last_cycle_custom_dma_burst_0_downstream_granted_slave_ext_ssram_s1 & 1;

  assign fir_dma_read_master_qualified_request_ext_ssram_s1 = fir_dma_read_master_requests_ext_ssram_s1 & ~((fir_dma_read_master_read & (ext_ssram_bus_avalon_slave_write_pending | (ext_ssram_bus_avalon_slave_read_pending & !((((|custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | (|fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[1 : 0]))))))) | custom_dma_burst_0_downstream_arbiterlock);
  //fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register_in mux for readlatency shift register, which is an e_mux
  assign fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register_in = fir_dma_read_master_granted_ext_ssram_s1 & fir_dma_read_master_read & ~ext_ssram_s1_waits_for_read;

  //shift register p1 fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register in if flush, otherwise shift left, which is an e_mux
  assign p1_fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register = {fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register, fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register_in};

  //fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register for remembering which master asked for a fixed latency read, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register <= 0;
      else 
        fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register <= p1_fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register;
    end


  //local readdatavalid fir_dma_read_master_read_data_valid_ext_ssram_s1, which is an e_mux
  assign fir_dma_read_master_read_data_valid_ext_ssram_s1 = fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[3];

  //allow new arb cycle for ext_ssram_bus/avalon_slave, which is an e_assign
  assign ext_ssram_bus_avalon_slave_allow_new_arb_cycle = ~custom_dma_burst_0_downstream_arbiterlock & ~fir_dma_read_master_arbiterlock;

  //fir_dma/read_master assignment into master qualified-requests vector for ext_ssram/s1, which is an e_assign
  assign ext_ssram_bus_avalon_slave_master_qreq_vector[0] = fir_dma_read_master_qualified_request_ext_ssram_s1;

  //fir_dma/read_master grant ext_ssram/s1, which is an e_assign
  assign fir_dma_read_master_granted_ext_ssram_s1 = ext_ssram_bus_avalon_slave_grant_vector[0];

  //fir_dma/read_master saved-grant ext_ssram/s1, which is an e_assign
  assign fir_dma_read_master_saved_grant_ext_ssram_s1 = ext_ssram_bus_avalon_slave_arb_winner[0] && fir_dma_read_master_requests_ext_ssram_s1;

  //custom_dma_burst_0/downstream assignment into master qualified-requests vector for ext_ssram/s1, which is an e_assign
  assign ext_ssram_bus_avalon_slave_master_qreq_vector[1] = custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1;

  //custom_dma_burst_0/downstream grant ext_ssram/s1, which is an e_assign
  assign custom_dma_burst_0_downstream_granted_ext_ssram_s1 = ext_ssram_bus_avalon_slave_grant_vector[1];

  //custom_dma_burst_0/downstream saved-grant ext_ssram/s1, which is an e_assign
  assign custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1 = ext_ssram_bus_avalon_slave_arb_winner[1];

  //ext_ssram_bus/avalon_slave chosen-master double-vector, which is an e_assign
  assign ext_ssram_bus_avalon_slave_chosen_master_double_vector = {ext_ssram_bus_avalon_slave_master_qreq_vector, ext_ssram_bus_avalon_slave_master_qreq_vector} & ({~ext_ssram_bus_avalon_slave_master_qreq_vector, ~ext_ssram_bus_avalon_slave_master_qreq_vector} + ext_ssram_bus_avalon_slave_arb_addend);

  //stable onehot encoding of arb winner
  assign ext_ssram_bus_avalon_slave_arb_winner = (ext_ssram_bus_avalon_slave_allow_new_arb_cycle & | ext_ssram_bus_avalon_slave_grant_vector) ? ext_ssram_bus_avalon_slave_grant_vector : ext_ssram_bus_avalon_slave_saved_chosen_master_vector;

  //saved ext_ssram_bus_avalon_slave_grant_vector, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_avalon_slave_saved_chosen_master_vector <= 0;
      else if (ext_ssram_bus_avalon_slave_allow_new_arb_cycle)
          ext_ssram_bus_avalon_slave_saved_chosen_master_vector <= |ext_ssram_bus_avalon_slave_grant_vector ? ext_ssram_bus_avalon_slave_grant_vector : ext_ssram_bus_avalon_slave_saved_chosen_master_vector;
    end


  //onehot encoding of chosen master
  assign ext_ssram_bus_avalon_slave_grant_vector = {(ext_ssram_bus_avalon_slave_chosen_master_double_vector[1] | ext_ssram_bus_avalon_slave_chosen_master_double_vector[3]),
    (ext_ssram_bus_avalon_slave_chosen_master_double_vector[0] | ext_ssram_bus_avalon_slave_chosen_master_double_vector[2])};

  //ext_ssram_bus/avalon_slave chosen master rotated left, which is an e_assign
  assign ext_ssram_bus_avalon_slave_chosen_master_rot_left = (ext_ssram_bus_avalon_slave_arb_winner << 1) ? (ext_ssram_bus_avalon_slave_arb_winner << 1) : 1;

  //ext_ssram_bus/avalon_slave's addend for next-master-grant
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_avalon_slave_arb_addend <= 1;
      else if (|ext_ssram_bus_avalon_slave_grant_vector)
          ext_ssram_bus_avalon_slave_arb_addend <= ext_ssram_bus_avalon_slave_end_xfer? ext_ssram_bus_avalon_slave_chosen_master_rot_left : ext_ssram_bus_avalon_slave_grant_vector;
    end


  //~adsc_n_to_the_ext_ssram of type begintransfer to ~p1_adsc_n_to_the_ext_ssram, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          adsc_n_to_the_ext_ssram <= ~0;
      else 
        adsc_n_to_the_ext_ssram <= p1_adsc_n_to_the_ext_ssram;
    end


  assign p1_adsc_n_to_the_ext_ssram = ~ext_ssram_bus_avalon_slave_begins_xfer;
  //~outputenable_n_to_the_ext_ssram of type outputenable to ~p1_outputenable_n_to_the_ext_ssram, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          outputenable_n_to_the_ext_ssram <= ~0;
      else 
        outputenable_n_to_the_ext_ssram <= p1_outputenable_n_to_the_ext_ssram;
    end


  //~p1_outputenable_n_to_the_ext_ssram assignment, which is an e_mux
  assign p1_outputenable_n_to_the_ext_ssram = ~((|custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | (|fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | ext_ssram_s1_in_a_read_cycle);

  assign p1_chipenable1_n_to_the_ext_ssram = ~(custom_dma_burst_0_downstream_granted_ext_ssram_s1 | fir_dma_read_master_granted_ext_ssram_s1 | (|custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1_shift_register[1 : 0]) | (|fir_dma_read_master_read_data_valid_ext_ssram_s1_shift_register[1 : 0]));
  //ext_ssram_bus_avalon_slave_firsttransfer first transaction, which is an e_assign
  assign ext_ssram_bus_avalon_slave_firsttransfer = ext_ssram_bus_avalon_slave_begins_xfer ? ext_ssram_bus_avalon_slave_unreg_firsttransfer : ext_ssram_bus_avalon_slave_reg_firsttransfer;

  //ext_ssram_bus_avalon_slave_unreg_firsttransfer first transaction, which is an e_assign
  assign ext_ssram_bus_avalon_slave_unreg_firsttransfer = ~(ext_ssram_bus_avalon_slave_slavearbiterlockenable & ext_ssram_bus_avalon_slave_any_continuerequest);

  //ext_ssram_bus_avalon_slave_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_avalon_slave_reg_firsttransfer <= 1'b1;
      else if (ext_ssram_bus_avalon_slave_begins_xfer)
          ext_ssram_bus_avalon_slave_reg_firsttransfer <= ext_ssram_bus_avalon_slave_unreg_firsttransfer;
    end


  //ext_ssram_bus_avalon_slave_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign ext_ssram_bus_avalon_slave_beginbursttransfer_internal = ext_ssram_bus_avalon_slave_begins_xfer;

  //ext_ssram_bus_avalon_slave_arbitration_holdoff_internal arbitration_holdoff, which is an e_assign
  assign ext_ssram_bus_avalon_slave_arbitration_holdoff_internal = ext_ssram_bus_avalon_slave_begins_xfer & ext_ssram_bus_avalon_slave_firsttransfer;

  //~bwe_n_to_the_ext_ssram of type write to ~p1_bwe_n_to_the_ext_ssram, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          bwe_n_to_the_ext_ssram <= ~0;
      else 
        bwe_n_to_the_ext_ssram <= p1_bwe_n_to_the_ext_ssram;
    end


  //~bw_n_to_the_ext_ssram of type byteenable to ~p1_bw_n_to_the_ext_ssram, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          bw_n_to_the_ext_ssram <= ~0;
      else 
        bw_n_to_the_ext_ssram <= p1_bw_n_to_the_ext_ssram;
    end


  //~p1_bwe_n_to_the_ext_ssram assignment, which is an e_mux
  assign p1_bwe_n_to_the_ext_ssram = ~(custom_dma_burst_0_downstream_granted_ext_ssram_s1 & custom_dma_burst_0_downstream_write);

  //ext_ssram_bus_address of type address to p1_ext_ssram_bus_address, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          ext_ssram_bus_address <= 0;
      else 
        ext_ssram_bus_address <= p1_ext_ssram_bus_address;
    end


  //p1_ext_ssram_bus_address mux, which is an e_mux
  assign p1_ext_ssram_bus_address = (custom_dma_burst_0_downstream_granted_ext_ssram_s1)? custom_dma_burst_0_downstream_address_to_slave :
    fir_dma_read_master_address_to_slave;

  //d1_ext_ssram_bus_avalon_slave_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_ext_ssram_bus_avalon_slave_end_xfer <= 1;
      else 
        d1_ext_ssram_bus_avalon_slave_end_xfer <= ext_ssram_bus_avalon_slave_end_xfer;
    end


  //ext_ssram_s1_waits_for_read in a cycle, which is an e_mux
  assign ext_ssram_s1_waits_for_read = ext_ssram_s1_in_a_read_cycle & 0;

  //ext_ssram_s1_in_a_read_cycle assignment, which is an e_assign
  assign ext_ssram_s1_in_a_read_cycle = (custom_dma_burst_0_downstream_granted_ext_ssram_s1 & custom_dma_burst_0_downstream_read) | (fir_dma_read_master_granted_ext_ssram_s1 & fir_dma_read_master_read);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = ext_ssram_s1_in_a_read_cycle;

  //ext_ssram_s1_waits_for_write in a cycle, which is an e_mux
  assign ext_ssram_s1_waits_for_write = ext_ssram_s1_in_a_write_cycle & 0;

  //ext_ssram_s1_in_a_write_cycle assignment, which is an e_assign
  assign ext_ssram_s1_in_a_write_cycle = custom_dma_burst_0_downstream_granted_ext_ssram_s1 & custom_dma_burst_0_downstream_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = ext_ssram_s1_in_a_write_cycle;

  assign wait_for_ext_ssram_s1_counter = 0;
  //~p1_bw_n_to_the_ext_ssram byte enable port mux, which is an e_mux
  assign p1_bw_n_to_the_ext_ssram = ~((custom_dma_burst_0_downstream_granted_ext_ssram_s1)? custom_dma_burst_0_downstream_byteenable :
    -1);


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //ext_ssram/s1 enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //custom_dma_burst_0/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_0_downstream_requests_ext_ssram_s1 && (custom_dma_burst_0_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_0/downstream drove 0 on its 'arbitrationshare' port while accessing slave ext_ssram/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_0/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_0_downstream_requests_ext_ssram_s1 && (custom_dma_burst_0_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_0/downstream drove 0 on its 'burstcount' port while accessing slave ext_ssram/s1", $time);
          $stop;
        end
    end


  //grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_0_downstream_granted_ext_ssram_s1 + fir_dma_read_master_granted_ext_ssram_s1 > 1)
        begin
          $write("%0d ns: > 1 of grant signals are active simultaneously", $time);
          $stop;
        end
    end


  //saved_grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_0_downstream_saved_grant_ext_ssram_s1 + fir_dma_read_master_saved_grant_ext_ssram_s1 > 1)
        begin
          $write("%0d ns: > 1 of saved_grant signals are active simultaneously", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_bus_bridge_arbitrator 
;



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module fir_dma_control_arbitrator (
                                    // inputs:
                                     clk,
                                     fir_dma_control_irq,
                                     fir_dma_control_readdata,
                                     pipeline_bridge_m1_address_to_slave,
                                     pipeline_bridge_m1_burstcount,
                                     pipeline_bridge_m1_byteenable,
                                     pipeline_bridge_m1_chipselect,
                                     pipeline_bridge_m1_latency_counter,
                                     pipeline_bridge_m1_read,
                                     pipeline_bridge_m1_write,
                                     pipeline_bridge_m1_writedata,
                                     reset_n,

                                    // outputs:
                                     d1_fir_dma_control_end_xfer,
                                     fir_dma_control_address,
                                     fir_dma_control_byteenable,
                                     fir_dma_control_irq_from_sa,
                                     fir_dma_control_read,
                                     fir_dma_control_readdata_from_sa,
                                     fir_dma_control_reset,
                                     fir_dma_control_write,
                                     fir_dma_control_writedata,
                                     pipeline_bridge_m1_granted_fir_dma_control,
                                     pipeline_bridge_m1_qualified_request_fir_dma_control,
                                     pipeline_bridge_m1_read_data_valid_fir_dma_control,
                                     pipeline_bridge_m1_requests_fir_dma_control
                                  )
;

  output           d1_fir_dma_control_end_xfer;
  output  [  2: 0] fir_dma_control_address;
  output  [  3: 0] fir_dma_control_byteenable;
  output           fir_dma_control_irq_from_sa;
  output           fir_dma_control_read;
  output  [ 31: 0] fir_dma_control_readdata_from_sa;
  output           fir_dma_control_reset;
  output           fir_dma_control_write;
  output  [ 31: 0] fir_dma_control_writedata;
  output           pipeline_bridge_m1_granted_fir_dma_control;
  output           pipeline_bridge_m1_qualified_request_fir_dma_control;
  output           pipeline_bridge_m1_read_data_valid_fir_dma_control;
  output           pipeline_bridge_m1_requests_fir_dma_control;
  input            clk;
  input            fir_dma_control_irq;
  input   [ 31: 0] fir_dma_control_readdata;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input   [  3: 0] pipeline_bridge_m1_byteenable;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;

  reg              d1_fir_dma_control_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_fir_dma_control;
  wire    [  2: 0] fir_dma_control_address;
  wire             fir_dma_control_allgrants;
  wire             fir_dma_control_allow_new_arb_cycle;
  wire             fir_dma_control_any_bursting_master_saved_grant;
  wire             fir_dma_control_any_continuerequest;
  wire             fir_dma_control_arb_counter_enable;
  reg              fir_dma_control_arb_share_counter;
  wire             fir_dma_control_arb_share_counter_next_value;
  wire             fir_dma_control_arb_share_set_values;
  wire             fir_dma_control_beginbursttransfer_internal;
  wire             fir_dma_control_begins_xfer;
  wire    [  3: 0] fir_dma_control_byteenable;
  wire             fir_dma_control_end_xfer;
  wire             fir_dma_control_firsttransfer;
  wire             fir_dma_control_grant_vector;
  wire             fir_dma_control_in_a_read_cycle;
  wire             fir_dma_control_in_a_write_cycle;
  wire             fir_dma_control_irq_from_sa;
  wire             fir_dma_control_master_qreq_vector;
  wire             fir_dma_control_non_bursting_master_requests;
  wire             fir_dma_control_read;
  wire    [ 31: 0] fir_dma_control_readdata_from_sa;
  reg              fir_dma_control_reg_firsttransfer;
  wire             fir_dma_control_reset;
  reg              fir_dma_control_slavearbiterlockenable;
  wire             fir_dma_control_slavearbiterlockenable2;
  wire             fir_dma_control_unreg_firsttransfer;
  wire             fir_dma_control_waits_for_read;
  wire             fir_dma_control_waits_for_write;
  wire             fir_dma_control_write;
  wire    [ 31: 0] fir_dma_control_writedata;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             p1_pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_fir_dma_control;
  wire             pipeline_bridge_m1_qualified_request_fir_dma_control;
  wire             pipeline_bridge_m1_read_data_valid_fir_dma_control;
  reg              pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register;
  wire             pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register_in;
  wire             pipeline_bridge_m1_requests_fir_dma_control;
  wire             pipeline_bridge_m1_saved_grant_fir_dma_control;
  wire    [ 11: 0] shifted_address_to_fir_dma_control_from_pipeline_bridge_m1;
  wire             wait_for_fir_dma_control_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~fir_dma_control_end_xfer;
    end


  assign fir_dma_control_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_fir_dma_control));
  //assign fir_dma_control_readdata_from_sa = fir_dma_control_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign fir_dma_control_readdata_from_sa = fir_dma_control_readdata;

  assign pipeline_bridge_m1_requests_fir_dma_control = ({pipeline_bridge_m1_address_to_slave[11 : 5] , 5'b0} == 12'h840) & pipeline_bridge_m1_chipselect;
  //fir_dma_control_arb_share_counter set values, which is an e_mux
  assign fir_dma_control_arb_share_set_values = 1;

  //fir_dma_control_non_bursting_master_requests mux, which is an e_mux
  assign fir_dma_control_non_bursting_master_requests = pipeline_bridge_m1_requests_fir_dma_control;

  //fir_dma_control_any_bursting_master_saved_grant mux, which is an e_mux
  assign fir_dma_control_any_bursting_master_saved_grant = 0;

  //fir_dma_control_arb_share_counter_next_value assignment, which is an e_assign
  assign fir_dma_control_arb_share_counter_next_value = fir_dma_control_firsttransfer ? (fir_dma_control_arb_share_set_values - 1) : |fir_dma_control_arb_share_counter ? (fir_dma_control_arb_share_counter - 1) : 0;

  //fir_dma_control_allgrants all slave grants, which is an e_mux
  assign fir_dma_control_allgrants = |fir_dma_control_grant_vector;

  //fir_dma_control_end_xfer assignment, which is an e_assign
  assign fir_dma_control_end_xfer = ~(fir_dma_control_waits_for_read | fir_dma_control_waits_for_write);

  //end_xfer_arb_share_counter_term_fir_dma_control arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_fir_dma_control = fir_dma_control_end_xfer & (~fir_dma_control_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //fir_dma_control_arb_share_counter arbitration counter enable, which is an e_assign
  assign fir_dma_control_arb_counter_enable = (end_xfer_arb_share_counter_term_fir_dma_control & fir_dma_control_allgrants) | (end_xfer_arb_share_counter_term_fir_dma_control & ~fir_dma_control_non_bursting_master_requests);

  //fir_dma_control_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_control_arb_share_counter <= 0;
      else if (fir_dma_control_arb_counter_enable)
          fir_dma_control_arb_share_counter <= fir_dma_control_arb_share_counter_next_value;
    end


  //fir_dma_control_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_control_slavearbiterlockenable <= 0;
      else if ((|fir_dma_control_master_qreq_vector & end_xfer_arb_share_counter_term_fir_dma_control) | (end_xfer_arb_share_counter_term_fir_dma_control & ~fir_dma_control_non_bursting_master_requests))
          fir_dma_control_slavearbiterlockenable <= |fir_dma_control_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 fir_dma/control arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = fir_dma_control_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //fir_dma_control_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign fir_dma_control_slavearbiterlockenable2 = |fir_dma_control_arb_share_counter_next_value;

  //pipeline_bridge/m1 fir_dma/control arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = fir_dma_control_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //fir_dma_control_any_continuerequest at least one master continues requesting, which is an e_assign
  assign fir_dma_control_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_fir_dma_control = pipeline_bridge_m1_requests_fir_dma_control & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((1 < pipeline_bridge_m1_latency_counter))));
  //pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register_in mux for readlatency shift register, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register_in = pipeline_bridge_m1_granted_fir_dma_control & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~fir_dma_control_waits_for_read;

  //shift register p1 pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register in if flush, otherwise shift left, which is an e_mux
  assign p1_pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register = {pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register, pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register_in};

  //pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register for remembering which master asked for a fixed latency read, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register <= 0;
      else 
        pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register <= p1_pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register;
    end


  //local readdatavalid pipeline_bridge_m1_read_data_valid_fir_dma_control, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_fir_dma_control = pipeline_bridge_m1_read_data_valid_fir_dma_control_shift_register;

  //fir_dma_control_writedata mux, which is an e_mux
  assign fir_dma_control_writedata = pipeline_bridge_m1_writedata;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_fir_dma_control = pipeline_bridge_m1_qualified_request_fir_dma_control;

  //pipeline_bridge/m1 saved-grant fir_dma/control, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_fir_dma_control = pipeline_bridge_m1_requests_fir_dma_control;

  //allow new arb cycle for fir_dma/control, which is an e_assign
  assign fir_dma_control_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign fir_dma_control_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign fir_dma_control_master_qreq_vector = 1;

  //~fir_dma_control_reset assignment, which is an e_assign
  assign fir_dma_control_reset = ~reset_n;

  //fir_dma_control_firsttransfer first transaction, which is an e_assign
  assign fir_dma_control_firsttransfer = fir_dma_control_begins_xfer ? fir_dma_control_unreg_firsttransfer : fir_dma_control_reg_firsttransfer;

  //fir_dma_control_unreg_firsttransfer first transaction, which is an e_assign
  assign fir_dma_control_unreg_firsttransfer = ~(fir_dma_control_slavearbiterlockenable & fir_dma_control_any_continuerequest);

  //fir_dma_control_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_control_reg_firsttransfer <= 1'b1;
      else if (fir_dma_control_begins_xfer)
          fir_dma_control_reg_firsttransfer <= fir_dma_control_unreg_firsttransfer;
    end


  //fir_dma_control_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign fir_dma_control_beginbursttransfer_internal = fir_dma_control_begins_xfer;

  //fir_dma_control_read assignment, which is an e_mux
  assign fir_dma_control_read = pipeline_bridge_m1_granted_fir_dma_control & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //fir_dma_control_write assignment, which is an e_mux
  assign fir_dma_control_write = pipeline_bridge_m1_granted_fir_dma_control & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  assign shifted_address_to_fir_dma_control_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //fir_dma_control_address mux, which is an e_mux
  assign fir_dma_control_address = shifted_address_to_fir_dma_control_from_pipeline_bridge_m1 >> 2;

  //d1_fir_dma_control_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_fir_dma_control_end_xfer <= 1;
      else 
        d1_fir_dma_control_end_xfer <= fir_dma_control_end_xfer;
    end


  //fir_dma_control_waits_for_read in a cycle, which is an e_mux
  assign fir_dma_control_waits_for_read = fir_dma_control_in_a_read_cycle & 0;

  //fir_dma_control_in_a_read_cycle assignment, which is an e_assign
  assign fir_dma_control_in_a_read_cycle = pipeline_bridge_m1_granted_fir_dma_control & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = fir_dma_control_in_a_read_cycle;

  //fir_dma_control_waits_for_write in a cycle, which is an e_mux
  assign fir_dma_control_waits_for_write = fir_dma_control_in_a_write_cycle & 0;

  //fir_dma_control_in_a_write_cycle assignment, which is an e_assign
  assign fir_dma_control_in_a_write_cycle = pipeline_bridge_m1_granted_fir_dma_control & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = fir_dma_control_in_a_write_cycle;

  assign wait_for_fir_dma_control_counter = 0;
  //fir_dma_control_byteenable byte enable port mux, which is an e_mux
  assign fir_dma_control_byteenable = (pipeline_bridge_m1_granted_fir_dma_control)? pipeline_bridge_m1_byteenable :
    -1;

  //assign fir_dma_control_irq_from_sa = fir_dma_control_irq so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign fir_dma_control_irq_from_sa = fir_dma_control_irq;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //fir_dma/control enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_fir_dma_control && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave fir_dma/control", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module fir_dma_read_master_arbitrator (
                                        // inputs:
                                         clk,
                                         d1_ext_ssram_bus_avalon_slave_end_xfer,
                                         fir_dma_read_master_address,
                                         fir_dma_read_master_byteenable,
                                         fir_dma_read_master_granted_ext_ssram_s1,
                                         fir_dma_read_master_qualified_request_ext_ssram_s1,
                                         fir_dma_read_master_read,
                                         fir_dma_read_master_read_data_valid_ext_ssram_s1,
                                         fir_dma_read_master_requests_ext_ssram_s1,
                                         incoming_ext_ssram_bus_data,
                                         reset_n,

                                        // outputs:
                                         fir_dma_read_master_address_to_slave,
                                         fir_dma_read_master_latency_counter,
                                         fir_dma_read_master_readdata,
                                         fir_dma_read_master_readdatavalid,
                                         fir_dma_read_master_waitrequest
                                      )
;

  output  [ 31: 0] fir_dma_read_master_address_to_slave;
  output  [  2: 0] fir_dma_read_master_latency_counter;
  output  [ 31: 0] fir_dma_read_master_readdata;
  output           fir_dma_read_master_readdatavalid;
  output           fir_dma_read_master_waitrequest;
  input            clk;
  input            d1_ext_ssram_bus_avalon_slave_end_xfer;
  input   [ 31: 0] fir_dma_read_master_address;
  input   [  3: 0] fir_dma_read_master_byteenable;
  input            fir_dma_read_master_granted_ext_ssram_s1;
  input            fir_dma_read_master_qualified_request_ext_ssram_s1;
  input            fir_dma_read_master_read;
  input            fir_dma_read_master_read_data_valid_ext_ssram_s1;
  input            fir_dma_read_master_requests_ext_ssram_s1;
  input   [ 31: 0] incoming_ext_ssram_bus_data;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 31: 0] fir_dma_read_master_address_last_time;
  wire    [ 31: 0] fir_dma_read_master_address_to_slave;
  reg     [  3: 0] fir_dma_read_master_byteenable_last_time;
  wire             fir_dma_read_master_is_granted_some_slave;
  reg     [  2: 0] fir_dma_read_master_latency_counter;
  reg              fir_dma_read_master_read_but_no_slave_selected;
  reg              fir_dma_read_master_read_last_time;
  wire    [ 31: 0] fir_dma_read_master_readdata;
  wire             fir_dma_read_master_readdatavalid;
  wire             fir_dma_read_master_run;
  wire             fir_dma_read_master_waitrequest;
  wire    [  2: 0] latency_load_value;
  wire    [  2: 0] p1_fir_dma_read_master_latency_counter;
  wire             pre_flush_fir_dma_read_master_readdatavalid;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (fir_dma_read_master_qualified_request_ext_ssram_s1 | ~fir_dma_read_master_requests_ext_ssram_s1) & (fir_dma_read_master_granted_ext_ssram_s1 | ~fir_dma_read_master_qualified_request_ext_ssram_s1) & ((~fir_dma_read_master_qualified_request_ext_ssram_s1 | ~(fir_dma_read_master_read) | (1 & (fir_dma_read_master_read))));

  //cascaded wait assignment, which is an e_assign
  assign fir_dma_read_master_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign fir_dma_read_master_address_to_slave = {11'b110000,
    fir_dma_read_master_address[20 : 0]};

  //fir_dma_read_master_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_read_but_no_slave_selected <= 0;
      else 
        fir_dma_read_master_read_but_no_slave_selected <= fir_dma_read_master_read & fir_dma_read_master_run & ~fir_dma_read_master_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign fir_dma_read_master_is_granted_some_slave = fir_dma_read_master_granted_ext_ssram_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_fir_dma_read_master_readdatavalid = fir_dma_read_master_read_data_valid_ext_ssram_s1;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign fir_dma_read_master_readdatavalid = fir_dma_read_master_read_but_no_slave_selected |
    pre_flush_fir_dma_read_master_readdatavalid;

  //fir_dma/read_master readdata mux, which is an e_mux
  assign fir_dma_read_master_readdata = incoming_ext_ssram_bus_data;

  //actual waitrequest port, which is an e_assign
  assign fir_dma_read_master_waitrequest = ~fir_dma_read_master_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_latency_counter <= 0;
      else 
        fir_dma_read_master_latency_counter <= p1_fir_dma_read_master_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_fir_dma_read_master_latency_counter = ((fir_dma_read_master_run & fir_dma_read_master_read))? latency_load_value :
    (fir_dma_read_master_latency_counter)? fir_dma_read_master_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = {3 {fir_dma_read_master_requests_ext_ssram_s1}} & 4;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //fir_dma_read_master_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_address_last_time <= 0;
      else 
        fir_dma_read_master_address_last_time <= fir_dma_read_master_address;
    end


  //fir_dma/read_master waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= fir_dma_read_master_waitrequest & (fir_dma_read_master_read);
    end


  //fir_dma_read_master_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_read_master_address != fir_dma_read_master_address_last_time))
        begin
          $write("%0d ns: fir_dma_read_master_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_read_master_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_byteenable_last_time <= 0;
      else 
        fir_dma_read_master_byteenable_last_time <= fir_dma_read_master_byteenable;
    end


  //fir_dma_read_master_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_read_master_byteenable != fir_dma_read_master_byteenable_last_time))
        begin
          $write("%0d ns: fir_dma_read_master_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_read_master_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_read_master_read_last_time <= 0;
      else 
        fir_dma_read_master_read_last_time <= fir_dma_read_master_read;
    end


  //fir_dma_read_master_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_read_master_read != fir_dma_read_master_read_last_time))
        begin
          $write("%0d ns: fir_dma_read_master_read did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module fir_dma_write_master_arbitrator (
                                         // inputs:
                                          clk,
                                          custom_dma_burst_5_upstream_waitrequest_from_sa,
                                          d1_custom_dma_burst_5_upstream_end_xfer,
                                          fir_dma_write_master_address,
                                          fir_dma_write_master_burstcount,
                                          fir_dma_write_master_byteenable,
                                          fir_dma_write_master_granted_custom_dma_burst_5_upstream,
                                          fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream,
                                          fir_dma_write_master_requests_custom_dma_burst_5_upstream,
                                          fir_dma_write_master_write,
                                          fir_dma_write_master_writedata,
                                          reset_n,

                                         // outputs:
                                          fir_dma_write_master_address_to_slave,
                                          fir_dma_write_master_waitrequest
                                       )
;

  output  [ 31: 0] fir_dma_write_master_address_to_slave;
  output           fir_dma_write_master_waitrequest;
  input            clk;
  input            custom_dma_burst_5_upstream_waitrequest_from_sa;
  input            d1_custom_dma_burst_5_upstream_end_xfer;
  input   [ 31: 0] fir_dma_write_master_address;
  input   [  2: 0] fir_dma_write_master_burstcount;
  input   [  3: 0] fir_dma_write_master_byteenable;
  input            fir_dma_write_master_granted_custom_dma_burst_5_upstream;
  input            fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream;
  input            fir_dma_write_master_requests_custom_dma_burst_5_upstream;
  input            fir_dma_write_master_write;
  input   [ 31: 0] fir_dma_write_master_writedata;
  input            reset_n;

  reg              active_and_waiting_last_time;
  reg     [ 31: 0] fir_dma_write_master_address_last_time;
  wire    [ 31: 0] fir_dma_write_master_address_to_slave;
  reg     [  2: 0] fir_dma_write_master_burstcount_last_time;
  reg     [  3: 0] fir_dma_write_master_byteenable_last_time;
  wire             fir_dma_write_master_run;
  wire             fir_dma_write_master_waitrequest;
  reg              fir_dma_write_master_write_last_time;
  reg     [ 31: 0] fir_dma_write_master_writedata_last_time;
  wire             r_0;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & ((~fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream | ~(fir_dma_write_master_write) | (1 & ~custom_dma_burst_5_upstream_waitrequest_from_sa & (fir_dma_write_master_write))));

  //cascaded wait assignment, which is an e_assign
  assign fir_dma_write_master_run = r_0;

  //optimize select-logic by passing only those address bits which matter.
  assign fir_dma_write_master_address_to_slave = {7'b1,
    fir_dma_write_master_address[24 : 0]};

  //actual waitrequest port, which is an e_assign
  assign fir_dma_write_master_waitrequest = ~fir_dma_write_master_run;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //fir_dma_write_master_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_write_master_address_last_time <= 0;
      else 
        fir_dma_write_master_address_last_time <= fir_dma_write_master_address;
    end


  //fir_dma/write_master waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= fir_dma_write_master_waitrequest & (fir_dma_write_master_write);
    end


  //fir_dma_write_master_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_write_master_address != fir_dma_write_master_address_last_time))
        begin
          $write("%0d ns: fir_dma_write_master_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_write_master_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_write_master_burstcount_last_time <= 0;
      else 
        fir_dma_write_master_burstcount_last_time <= fir_dma_write_master_burstcount;
    end


  //fir_dma_write_master_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_write_master_burstcount != fir_dma_write_master_burstcount_last_time))
        begin
          $write("%0d ns: fir_dma_write_master_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_write_master_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_write_master_byteenable_last_time <= 0;
      else 
        fir_dma_write_master_byteenable_last_time <= fir_dma_write_master_byteenable;
    end


  //fir_dma_write_master_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_write_master_byteenable != fir_dma_write_master_byteenable_last_time))
        begin
          $write("%0d ns: fir_dma_write_master_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_write_master_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_write_master_write_last_time <= 0;
      else 
        fir_dma_write_master_write_last_time <= fir_dma_write_master_write;
    end


  //fir_dma_write_master_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_write_master_write != fir_dma_write_master_write_last_time))
        begin
          $write("%0d ns: fir_dma_write_master_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //fir_dma_write_master_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fir_dma_write_master_writedata_last_time <= 0;
      else 
        fir_dma_write_master_writedata_last_time <= fir_dma_write_master_writedata;
    end


  //fir_dma_write_master_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (fir_dma_write_master_writedata != fir_dma_write_master_writedata_last_time) & fir_dma_write_master_write)
        begin
          $write("%0d ns: fir_dma_write_master_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module jtag_uart_avalon_jtag_slave_arbitrator (
                                                // inputs:
                                                 clk,
                                                 jtag_uart_avalon_jtag_slave_dataavailable,
                                                 jtag_uart_avalon_jtag_slave_irq,
                                                 jtag_uart_avalon_jtag_slave_readdata,
                                                 jtag_uart_avalon_jtag_slave_readyfordata,
                                                 jtag_uart_avalon_jtag_slave_waitrequest,
                                                 pipeline_bridge_m1_address_to_slave,
                                                 pipeline_bridge_m1_burstcount,
                                                 pipeline_bridge_m1_chipselect,
                                                 pipeline_bridge_m1_latency_counter,
                                                 pipeline_bridge_m1_read,
                                                 pipeline_bridge_m1_write,
                                                 pipeline_bridge_m1_writedata,
                                                 reset_n,

                                                // outputs:
                                                 d1_jtag_uart_avalon_jtag_slave_end_xfer,
                                                 jtag_uart_avalon_jtag_slave_address,
                                                 jtag_uart_avalon_jtag_slave_chipselect,
                                                 jtag_uart_avalon_jtag_slave_dataavailable_from_sa,
                                                 jtag_uart_avalon_jtag_slave_irq_from_sa,
                                                 jtag_uart_avalon_jtag_slave_read_n,
                                                 jtag_uart_avalon_jtag_slave_readdata_from_sa,
                                                 jtag_uart_avalon_jtag_slave_readyfordata_from_sa,
                                                 jtag_uart_avalon_jtag_slave_reset_n,
                                                 jtag_uart_avalon_jtag_slave_waitrequest_from_sa,
                                                 jtag_uart_avalon_jtag_slave_write_n,
                                                 jtag_uart_avalon_jtag_slave_writedata,
                                                 pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave,
                                                 pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave,
                                                 pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave,
                                                 pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave
                                              )
;

  output           d1_jtag_uart_avalon_jtag_slave_end_xfer;
  output           jtag_uart_avalon_jtag_slave_address;
  output           jtag_uart_avalon_jtag_slave_chipselect;
  output           jtag_uart_avalon_jtag_slave_dataavailable_from_sa;
  output           jtag_uart_avalon_jtag_slave_irq_from_sa;
  output           jtag_uart_avalon_jtag_slave_read_n;
  output  [ 31: 0] jtag_uart_avalon_jtag_slave_readdata_from_sa;
  output           jtag_uart_avalon_jtag_slave_readyfordata_from_sa;
  output           jtag_uart_avalon_jtag_slave_reset_n;
  output           jtag_uart_avalon_jtag_slave_waitrequest_from_sa;
  output           jtag_uart_avalon_jtag_slave_write_n;
  output  [ 31: 0] jtag_uart_avalon_jtag_slave_writedata;
  output           pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave;
  output           pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave;
  output           pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave;
  output           pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;
  input            clk;
  input            jtag_uart_avalon_jtag_slave_dataavailable;
  input            jtag_uart_avalon_jtag_slave_irq;
  input   [ 31: 0] jtag_uart_avalon_jtag_slave_readdata;
  input            jtag_uart_avalon_jtag_slave_readyfordata;
  input            jtag_uart_avalon_jtag_slave_waitrequest;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;

  reg              d1_jtag_uart_avalon_jtag_slave_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             jtag_uart_avalon_jtag_slave_address;
  wire             jtag_uart_avalon_jtag_slave_allgrants;
  wire             jtag_uart_avalon_jtag_slave_allow_new_arb_cycle;
  wire             jtag_uart_avalon_jtag_slave_any_bursting_master_saved_grant;
  wire             jtag_uart_avalon_jtag_slave_any_continuerequest;
  wire             jtag_uart_avalon_jtag_slave_arb_counter_enable;
  reg              jtag_uart_avalon_jtag_slave_arb_share_counter;
  wire             jtag_uart_avalon_jtag_slave_arb_share_counter_next_value;
  wire             jtag_uart_avalon_jtag_slave_arb_share_set_values;
  wire             jtag_uart_avalon_jtag_slave_beginbursttransfer_internal;
  wire             jtag_uart_avalon_jtag_slave_begins_xfer;
  wire             jtag_uart_avalon_jtag_slave_chipselect;
  wire             jtag_uart_avalon_jtag_slave_dataavailable_from_sa;
  wire             jtag_uart_avalon_jtag_slave_end_xfer;
  wire             jtag_uart_avalon_jtag_slave_firsttransfer;
  wire             jtag_uart_avalon_jtag_slave_grant_vector;
  wire             jtag_uart_avalon_jtag_slave_in_a_read_cycle;
  wire             jtag_uart_avalon_jtag_slave_in_a_write_cycle;
  wire             jtag_uart_avalon_jtag_slave_irq_from_sa;
  wire             jtag_uart_avalon_jtag_slave_master_qreq_vector;
  wire             jtag_uart_avalon_jtag_slave_non_bursting_master_requests;
  wire             jtag_uart_avalon_jtag_slave_read_n;
  wire    [ 31: 0] jtag_uart_avalon_jtag_slave_readdata_from_sa;
  wire             jtag_uart_avalon_jtag_slave_readyfordata_from_sa;
  reg              jtag_uart_avalon_jtag_slave_reg_firsttransfer;
  wire             jtag_uart_avalon_jtag_slave_reset_n;
  reg              jtag_uart_avalon_jtag_slave_slavearbiterlockenable;
  wire             jtag_uart_avalon_jtag_slave_slavearbiterlockenable2;
  wire             jtag_uart_avalon_jtag_slave_unreg_firsttransfer;
  wire             jtag_uart_avalon_jtag_slave_waitrequest_from_sa;
  wire             jtag_uart_avalon_jtag_slave_waits_for_read;
  wire             jtag_uart_avalon_jtag_slave_waits_for_write;
  wire             jtag_uart_avalon_jtag_slave_write_n;
  wire    [ 31: 0] jtag_uart_avalon_jtag_slave_writedata;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_saved_grant_jtag_uart_avalon_jtag_slave;
  wire    [ 11: 0] shifted_address_to_jtag_uart_avalon_jtag_slave_from_pipeline_bridge_m1;
  wire             wait_for_jtag_uart_avalon_jtag_slave_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~jtag_uart_avalon_jtag_slave_end_xfer;
    end


  assign jtag_uart_avalon_jtag_slave_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave));
  //assign jtag_uart_avalon_jtag_slave_readdata_from_sa = jtag_uart_avalon_jtag_slave_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_readdata_from_sa = jtag_uart_avalon_jtag_slave_readdata;

  assign pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave = ({pipeline_bridge_m1_address_to_slave[11 : 3] , 3'b0} == 12'h868) & pipeline_bridge_m1_chipselect;
  //assign jtag_uart_avalon_jtag_slave_dataavailable_from_sa = jtag_uart_avalon_jtag_slave_dataavailable so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_dataavailable_from_sa = jtag_uart_avalon_jtag_slave_dataavailable;

  //assign jtag_uart_avalon_jtag_slave_readyfordata_from_sa = jtag_uart_avalon_jtag_slave_readyfordata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_readyfordata_from_sa = jtag_uart_avalon_jtag_slave_readyfordata;

  //assign jtag_uart_avalon_jtag_slave_waitrequest_from_sa = jtag_uart_avalon_jtag_slave_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_waitrequest_from_sa = jtag_uart_avalon_jtag_slave_waitrequest;

  //jtag_uart_avalon_jtag_slave_arb_share_counter set values, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_arb_share_set_values = 1;

  //jtag_uart_avalon_jtag_slave_non_bursting_master_requests mux, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_non_bursting_master_requests = pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;

  //jtag_uart_avalon_jtag_slave_any_bursting_master_saved_grant mux, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_any_bursting_master_saved_grant = 0;

  //jtag_uart_avalon_jtag_slave_arb_share_counter_next_value assignment, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_arb_share_counter_next_value = jtag_uart_avalon_jtag_slave_firsttransfer ? (jtag_uart_avalon_jtag_slave_arb_share_set_values - 1) : |jtag_uart_avalon_jtag_slave_arb_share_counter ? (jtag_uart_avalon_jtag_slave_arb_share_counter - 1) : 0;

  //jtag_uart_avalon_jtag_slave_allgrants all slave grants, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_allgrants = |jtag_uart_avalon_jtag_slave_grant_vector;

  //jtag_uart_avalon_jtag_slave_end_xfer assignment, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_end_xfer = ~(jtag_uart_avalon_jtag_slave_waits_for_read | jtag_uart_avalon_jtag_slave_waits_for_write);

  //end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave = jtag_uart_avalon_jtag_slave_end_xfer & (~jtag_uart_avalon_jtag_slave_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //jtag_uart_avalon_jtag_slave_arb_share_counter arbitration counter enable, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_arb_counter_enable = (end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave & jtag_uart_avalon_jtag_slave_allgrants) | (end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave & ~jtag_uart_avalon_jtag_slave_non_bursting_master_requests);

  //jtag_uart_avalon_jtag_slave_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          jtag_uart_avalon_jtag_slave_arb_share_counter <= 0;
      else if (jtag_uart_avalon_jtag_slave_arb_counter_enable)
          jtag_uart_avalon_jtag_slave_arb_share_counter <= jtag_uart_avalon_jtag_slave_arb_share_counter_next_value;
    end


  //jtag_uart_avalon_jtag_slave_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          jtag_uart_avalon_jtag_slave_slavearbiterlockenable <= 0;
      else if ((|jtag_uart_avalon_jtag_slave_master_qreq_vector & end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave) | (end_xfer_arb_share_counter_term_jtag_uart_avalon_jtag_slave & ~jtag_uart_avalon_jtag_slave_non_bursting_master_requests))
          jtag_uart_avalon_jtag_slave_slavearbiterlockenable <= |jtag_uart_avalon_jtag_slave_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 jtag_uart/avalon_jtag_slave arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = jtag_uart_avalon_jtag_slave_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //jtag_uart_avalon_jtag_slave_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_slavearbiterlockenable2 = |jtag_uart_avalon_jtag_slave_arb_share_counter_next_value;

  //pipeline_bridge/m1 jtag_uart/avalon_jtag_slave arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = jtag_uart_avalon_jtag_slave_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //jtag_uart_avalon_jtag_slave_any_continuerequest at least one master continues requesting, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave = pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((pipeline_bridge_m1_latency_counter != 0))));
  //local readdatavalid pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave = pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~jtag_uart_avalon_jtag_slave_waits_for_read;

  //jtag_uart_avalon_jtag_slave_writedata mux, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_writedata = pipeline_bridge_m1_writedata;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave = pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave;

  //pipeline_bridge/m1 saved-grant jtag_uart/avalon_jtag_slave, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_jtag_uart_avalon_jtag_slave = pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;

  //allow new arb cycle for jtag_uart/avalon_jtag_slave, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign jtag_uart_avalon_jtag_slave_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign jtag_uart_avalon_jtag_slave_master_qreq_vector = 1;

  //jtag_uart_avalon_jtag_slave_reset_n assignment, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_reset_n = reset_n;

  assign jtag_uart_avalon_jtag_slave_chipselect = pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave;
  //jtag_uart_avalon_jtag_slave_firsttransfer first transaction, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_firsttransfer = jtag_uart_avalon_jtag_slave_begins_xfer ? jtag_uart_avalon_jtag_slave_unreg_firsttransfer : jtag_uart_avalon_jtag_slave_reg_firsttransfer;

  //jtag_uart_avalon_jtag_slave_unreg_firsttransfer first transaction, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_unreg_firsttransfer = ~(jtag_uart_avalon_jtag_slave_slavearbiterlockenable & jtag_uart_avalon_jtag_slave_any_continuerequest);

  //jtag_uart_avalon_jtag_slave_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          jtag_uart_avalon_jtag_slave_reg_firsttransfer <= 1'b1;
      else if (jtag_uart_avalon_jtag_slave_begins_xfer)
          jtag_uart_avalon_jtag_slave_reg_firsttransfer <= jtag_uart_avalon_jtag_slave_unreg_firsttransfer;
    end


  //jtag_uart_avalon_jtag_slave_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_beginbursttransfer_internal = jtag_uart_avalon_jtag_slave_begins_xfer;

  //~jtag_uart_avalon_jtag_slave_read_n assignment, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_read_n = ~(pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect));

  //~jtag_uart_avalon_jtag_slave_write_n assignment, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_write_n = ~(pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect));

  assign shifted_address_to_jtag_uart_avalon_jtag_slave_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //jtag_uart_avalon_jtag_slave_address mux, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_address = shifted_address_to_jtag_uart_avalon_jtag_slave_from_pipeline_bridge_m1 >> 2;

  //d1_jtag_uart_avalon_jtag_slave_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_jtag_uart_avalon_jtag_slave_end_xfer <= 1;
      else 
        d1_jtag_uart_avalon_jtag_slave_end_xfer <= jtag_uart_avalon_jtag_slave_end_xfer;
    end


  //jtag_uart_avalon_jtag_slave_waits_for_read in a cycle, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_waits_for_read = jtag_uart_avalon_jtag_slave_in_a_read_cycle & jtag_uart_avalon_jtag_slave_waitrequest_from_sa;

  //jtag_uart_avalon_jtag_slave_in_a_read_cycle assignment, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_in_a_read_cycle = pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = jtag_uart_avalon_jtag_slave_in_a_read_cycle;

  //jtag_uart_avalon_jtag_slave_waits_for_write in a cycle, which is an e_mux
  assign jtag_uart_avalon_jtag_slave_waits_for_write = jtag_uart_avalon_jtag_slave_in_a_write_cycle & jtag_uart_avalon_jtag_slave_waitrequest_from_sa;

  //jtag_uart_avalon_jtag_slave_in_a_write_cycle assignment, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_in_a_write_cycle = pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = jtag_uart_avalon_jtag_slave_in_a_write_cycle;

  assign wait_for_jtag_uart_avalon_jtag_slave_counter = 0;
  //assign jtag_uart_avalon_jtag_slave_irq_from_sa = jtag_uart_avalon_jtag_slave_irq so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign jtag_uart_avalon_jtag_slave_irq_from_sa = jtag_uart_avalon_jtag_slave_irq;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //jtag_uart/avalon_jtag_slave enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave jtag_uart/avalon_jtag_slave", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_custom_dma_burst_1_downstream_to_pipeline_bridge_s1_module (
                                                                                 // inputs:
                                                                                  clear_fifo,
                                                                                  clk,
                                                                                  data_in,
                                                                                  read,
                                                                                  reset_n,
                                                                                  sync_reset,
                                                                                  write,

                                                                                 // outputs:
                                                                                  data_out,
                                                                                  empty,
                                                                                  fifo_contains_ones_n,
                                                                                  full
                                                                               )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  wire             full_4;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  reg              stage_0;
  reg              stage_1;
  reg              stage_2;
  reg              stage_3;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_3;
  assign empty = !full_0;
  assign full_4 = 0;
  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    0;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module rdv_fifo_for_custom_dma_burst_2_downstream_to_pipeline_bridge_s1_module (
                                                                                 // inputs:
                                                                                  clear_fifo,
                                                                                  clk,
                                                                                  data_in,
                                                                                  read,
                                                                                  reset_n,
                                                                                  sync_reset,
                                                                                  write,

                                                                                 // outputs:
                                                                                  data_out,
                                                                                  empty,
                                                                                  fifo_contains_ones_n,
                                                                                  full
                                                                               )
;

  output           data_out;
  output           empty;
  output           fifo_contains_ones_n;
  output           full;
  input            clear_fifo;
  input            clk;
  input            data_in;
  input            read;
  input            reset_n;
  input            sync_reset;
  input            write;

  wire             data_out;
  wire             empty;
  reg              fifo_contains_ones_n;
  wire             full;
  reg              full_0;
  reg              full_1;
  reg              full_2;
  reg              full_3;
  wire             full_4;
  reg     [  3: 0] how_many_ones;
  wire    [  3: 0] one_count_minus_one;
  wire    [  3: 0] one_count_plus_one;
  wire             p0_full_0;
  wire             p0_stage_0;
  wire             p1_full_1;
  wire             p1_stage_1;
  wire             p2_full_2;
  wire             p2_stage_2;
  wire             p3_full_3;
  wire             p3_stage_3;
  reg              stage_0;
  reg              stage_1;
  reg              stage_2;
  reg              stage_3;
  wire    [  3: 0] updated_one_count;
  assign data_out = stage_0;
  assign full = full_3;
  assign empty = !full_0;
  assign full_4 = 0;
  //data_3, which is an e_mux
  assign p3_stage_3 = ((full_4 & ~clear_fifo) == 0)? data_in :
    data_in;

  //data_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_3 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_3))
          if (sync_reset & full_3 & !((full_4 == 0) & read & write))
              stage_3 <= 0;
          else 
            stage_3 <= p3_stage_3;
    end


  //control_3, which is an e_mux
  assign p3_full_3 = ((read & !write) == 0)? full_2 :
    0;

  //control_reg_3, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_3 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_3 <= 0;
          else 
            full_3 <= p3_full_3;
    end


  //data_2, which is an e_mux
  assign p2_stage_2 = ((full_3 & ~clear_fifo) == 0)? data_in :
    stage_3;

  //data_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_2 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_2))
          if (sync_reset & full_2 & !((full_3 == 0) & read & write))
              stage_2 <= 0;
          else 
            stage_2 <= p2_stage_2;
    end


  //control_2, which is an e_mux
  assign p2_full_2 = ((read & !write) == 0)? full_1 :
    full_3;

  //control_reg_2, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_2 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_2 <= 0;
          else 
            full_2 <= p2_full_2;
    end


  //data_1, which is an e_mux
  assign p1_stage_1 = ((full_2 & ~clear_fifo) == 0)? data_in :
    stage_2;

  //data_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_1 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_1))
          if (sync_reset & full_1 & !((full_2 == 0) & read & write))
              stage_1 <= 0;
          else 
            stage_1 <= p1_stage_1;
    end


  //control_1, which is an e_mux
  assign p1_full_1 = ((read & !write) == 0)? full_0 :
    full_2;

  //control_reg_1, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_1 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo)
              full_1 <= 0;
          else 
            full_1 <= p1_full_1;
    end


  //data_0, which is an e_mux
  assign p0_stage_0 = ((full_1 & ~clear_fifo) == 0)? data_in :
    stage_1;

  //data_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          stage_0 <= 0;
      else if (clear_fifo | sync_reset | read | (write & !full_0))
          if (sync_reset & full_0 & !((full_1 == 0) & read & write))
              stage_0 <= 0;
          else 
            stage_0 <= p0_stage_0;
    end


  //control_0, which is an e_mux
  assign p0_full_0 = ((read & !write) == 0)? 1 :
    full_1;

  //control_reg_0, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          full_0 <= 0;
      else if (clear_fifo | (read ^ write) | (write & !full_0))
          if (clear_fifo & ~write)
              full_0 <= 0;
          else 
            full_0 <= p0_full_0;
    end


  assign one_count_plus_one = how_many_ones + 1;
  assign one_count_minus_one = how_many_ones - 1;
  //updated_one_count, which is an e_mux
  assign updated_one_count = ((((clear_fifo | sync_reset) & !write)))? 0 :
    ((((clear_fifo | sync_reset) & write)))? |data_in :
    ((read & (|data_in) & write & (|stage_0)))? how_many_ones :
    ((write & (|data_in)))? one_count_plus_one :
    ((read & (|stage_0)))? one_count_minus_one :
    how_many_ones;

  //counts how many ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          how_many_ones <= 0;
      else if (clear_fifo | sync_reset | read | write)
          how_many_ones <= updated_one_count;
    end


  //this fifo contains ones in the data pipeline, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          fifo_contains_ones_n <= 1;
      else if (clear_fifo | sync_reset | read | write)
          fifo_contains_ones_n <= ~(|updated_one_count);
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge_s1_arbitrator (
                                       // inputs:
                                        clk,
                                        custom_dma_burst_1_downstream_address_to_slave,
                                        custom_dma_burst_1_downstream_arbitrationshare,
                                        custom_dma_burst_1_downstream_burstcount,
                                        custom_dma_burst_1_downstream_byteenable,
                                        custom_dma_burst_1_downstream_debugaccess,
                                        custom_dma_burst_1_downstream_latency_counter,
                                        custom_dma_burst_1_downstream_nativeaddress,
                                        custom_dma_burst_1_downstream_read,
                                        custom_dma_burst_1_downstream_write,
                                        custom_dma_burst_1_downstream_writedata,
                                        custom_dma_burst_2_downstream_address_to_slave,
                                        custom_dma_burst_2_downstream_arbitrationshare,
                                        custom_dma_burst_2_downstream_burstcount,
                                        custom_dma_burst_2_downstream_byteenable,
                                        custom_dma_burst_2_downstream_debugaccess,
                                        custom_dma_burst_2_downstream_latency_counter,
                                        custom_dma_burst_2_downstream_nativeaddress,
                                        custom_dma_burst_2_downstream_read,
                                        custom_dma_burst_2_downstream_write,
                                        custom_dma_burst_2_downstream_writedata,
                                        pipeline_bridge_s1_endofpacket,
                                        pipeline_bridge_s1_readdata,
                                        pipeline_bridge_s1_readdatavalid,
                                        pipeline_bridge_s1_waitrequest,
                                        reset_n,

                                       // outputs:
                                        custom_dma_burst_1_downstream_granted_pipeline_bridge_s1,
                                        custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1,
                                        custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1,
                                        custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register,
                                        custom_dma_burst_1_downstream_requests_pipeline_bridge_s1,
                                        custom_dma_burst_2_downstream_granted_pipeline_bridge_s1,
                                        custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1,
                                        custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1,
                                        custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register,
                                        custom_dma_burst_2_downstream_requests_pipeline_bridge_s1,
                                        d1_pipeline_bridge_s1_end_xfer,
                                        pipeline_bridge_s1_address,
                                        pipeline_bridge_s1_arbiterlock,
                                        pipeline_bridge_s1_arbiterlock2,
                                        pipeline_bridge_s1_burstcount,
                                        pipeline_bridge_s1_byteenable,
                                        pipeline_bridge_s1_chipselect,
                                        pipeline_bridge_s1_debugaccess,
                                        pipeline_bridge_s1_endofpacket_from_sa,
                                        pipeline_bridge_s1_nativeaddress,
                                        pipeline_bridge_s1_read,
                                        pipeline_bridge_s1_readdata_from_sa,
                                        pipeline_bridge_s1_reset_n,
                                        pipeline_bridge_s1_waitrequest_from_sa,
                                        pipeline_bridge_s1_write,
                                        pipeline_bridge_s1_writedata
                                     )
;

  output           custom_dma_burst_1_downstream_granted_pipeline_bridge_s1;
  output           custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1;
  output           custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1;
  output           custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  output           custom_dma_burst_1_downstream_requests_pipeline_bridge_s1;
  output           custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;
  output           custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1;
  output           custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1;
  output           custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  output           custom_dma_burst_2_downstream_requests_pipeline_bridge_s1;
  output           d1_pipeline_bridge_s1_end_xfer;
  output  [  9: 0] pipeline_bridge_s1_address;
  output           pipeline_bridge_s1_arbiterlock;
  output           pipeline_bridge_s1_arbiterlock2;
  output           pipeline_bridge_s1_burstcount;
  output  [  3: 0] pipeline_bridge_s1_byteenable;
  output           pipeline_bridge_s1_chipselect;
  output           pipeline_bridge_s1_debugaccess;
  output           pipeline_bridge_s1_endofpacket_from_sa;
  output  [  9: 0] pipeline_bridge_s1_nativeaddress;
  output           pipeline_bridge_s1_read;
  output  [ 31: 0] pipeline_bridge_s1_readdata_from_sa;
  output           pipeline_bridge_s1_reset_n;
  output           pipeline_bridge_s1_waitrequest_from_sa;
  output           pipeline_bridge_s1_write;
  output  [ 31: 0] pipeline_bridge_s1_writedata;
  input            clk;
  input   [ 11: 0] custom_dma_burst_1_downstream_address_to_slave;
  input   [  3: 0] custom_dma_burst_1_downstream_arbitrationshare;
  input            custom_dma_burst_1_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_1_downstream_byteenable;
  input            custom_dma_burst_1_downstream_debugaccess;
  input            custom_dma_burst_1_downstream_latency_counter;
  input   [ 11: 0] custom_dma_burst_1_downstream_nativeaddress;
  input            custom_dma_burst_1_downstream_read;
  input            custom_dma_burst_1_downstream_write;
  input   [ 31: 0] custom_dma_burst_1_downstream_writedata;
  input   [ 11: 0] custom_dma_burst_2_downstream_address_to_slave;
  input   [  3: 0] custom_dma_burst_2_downstream_arbitrationshare;
  input            custom_dma_burst_2_downstream_burstcount;
  input   [  3: 0] custom_dma_burst_2_downstream_byteenable;
  input            custom_dma_burst_2_downstream_debugaccess;
  input            custom_dma_burst_2_downstream_latency_counter;
  input   [ 11: 0] custom_dma_burst_2_downstream_nativeaddress;
  input            custom_dma_burst_2_downstream_read;
  input            custom_dma_burst_2_downstream_write;
  input   [ 31: 0] custom_dma_burst_2_downstream_writedata;
  input            pipeline_bridge_s1_endofpacket;
  input   [ 31: 0] pipeline_bridge_s1_readdata;
  input            pipeline_bridge_s1_readdatavalid;
  input            pipeline_bridge_s1_waitrequest;
  input            reset_n;

  wire             custom_dma_burst_1_downstream_arbiterlock;
  wire             custom_dma_burst_1_downstream_arbiterlock2;
  wire             custom_dma_burst_1_downstream_continuerequest;
  wire             custom_dma_burst_1_downstream_granted_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_rdv_fifo_empty_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_rdv_fifo_output_from_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  wire             custom_dma_burst_1_downstream_requests_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_arbiterlock;
  wire             custom_dma_burst_2_downstream_arbiterlock2;
  wire             custom_dma_burst_2_downstream_continuerequest;
  wire             custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_rdv_fifo_empty_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_rdv_fifo_output_from_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  wire             custom_dma_burst_2_downstream_requests_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1;
  reg              d1_pipeline_bridge_s1_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_pipeline_bridge_s1;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  reg              last_cycle_custom_dma_burst_1_downstream_granted_slave_pipeline_bridge_s1;
  reg              last_cycle_custom_dma_burst_2_downstream_granted_slave_pipeline_bridge_s1;
  wire    [  9: 0] pipeline_bridge_s1_address;
  wire             pipeline_bridge_s1_allgrants;
  wire             pipeline_bridge_s1_allow_new_arb_cycle;
  wire             pipeline_bridge_s1_any_bursting_master_saved_grant;
  wire             pipeline_bridge_s1_any_continuerequest;
  reg     [  1: 0] pipeline_bridge_s1_arb_addend;
  wire             pipeline_bridge_s1_arb_counter_enable;
  reg     [  3: 0] pipeline_bridge_s1_arb_share_counter;
  wire    [  3: 0] pipeline_bridge_s1_arb_share_counter_next_value;
  wire    [  3: 0] pipeline_bridge_s1_arb_share_set_values;
  wire    [  1: 0] pipeline_bridge_s1_arb_winner;
  wire             pipeline_bridge_s1_arbiterlock;
  wire             pipeline_bridge_s1_arbiterlock2;
  wire             pipeline_bridge_s1_arbitration_holdoff_internal;
  wire             pipeline_bridge_s1_beginbursttransfer_internal;
  wire             pipeline_bridge_s1_begins_xfer;
  wire             pipeline_bridge_s1_burstcount;
  wire    [  3: 0] pipeline_bridge_s1_byteenable;
  wire             pipeline_bridge_s1_chipselect;
  wire    [  3: 0] pipeline_bridge_s1_chosen_master_double_vector;
  wire    [  1: 0] pipeline_bridge_s1_chosen_master_rot_left;
  wire             pipeline_bridge_s1_debugaccess;
  wire             pipeline_bridge_s1_end_xfer;
  wire             pipeline_bridge_s1_endofpacket_from_sa;
  wire             pipeline_bridge_s1_firsttransfer;
  wire    [  1: 0] pipeline_bridge_s1_grant_vector;
  wire             pipeline_bridge_s1_in_a_read_cycle;
  wire             pipeline_bridge_s1_in_a_write_cycle;
  wire    [  1: 0] pipeline_bridge_s1_master_qreq_vector;
  wire             pipeline_bridge_s1_move_on_to_next_transaction;
  wire    [  9: 0] pipeline_bridge_s1_nativeaddress;
  wire             pipeline_bridge_s1_non_bursting_master_requests;
  wire             pipeline_bridge_s1_read;
  wire    [ 31: 0] pipeline_bridge_s1_readdata_from_sa;
  wire             pipeline_bridge_s1_readdatavalid_from_sa;
  reg              pipeline_bridge_s1_reg_firsttransfer;
  wire             pipeline_bridge_s1_reset_n;
  reg     [  1: 0] pipeline_bridge_s1_saved_chosen_master_vector;
  reg              pipeline_bridge_s1_slavearbiterlockenable;
  wire             pipeline_bridge_s1_slavearbiterlockenable2;
  wire             pipeline_bridge_s1_unreg_firsttransfer;
  wire             pipeline_bridge_s1_waitrequest_from_sa;
  wire             pipeline_bridge_s1_waits_for_read;
  wire             pipeline_bridge_s1_waits_for_write;
  wire             pipeline_bridge_s1_write;
  wire    [ 31: 0] pipeline_bridge_s1_writedata;
  wire    [ 11: 0] shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_1_downstream;
  wire    [ 11: 0] shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_2_downstream;
  wire             wait_for_pipeline_bridge_s1_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~pipeline_bridge_s1_end_xfer;
    end


  assign pipeline_bridge_s1_begins_xfer = ~d1_reasons_to_wait & ((custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1 | custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1));
  //assign pipeline_bridge_s1_readdata_from_sa = pipeline_bridge_s1_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pipeline_bridge_s1_readdata_from_sa = pipeline_bridge_s1_readdata;

  assign custom_dma_burst_1_downstream_requests_pipeline_bridge_s1 = (1) & (custom_dma_burst_1_downstream_read | custom_dma_burst_1_downstream_write);
  //assign pipeline_bridge_s1_waitrequest_from_sa = pipeline_bridge_s1_waitrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pipeline_bridge_s1_waitrequest_from_sa = pipeline_bridge_s1_waitrequest;

  //assign pipeline_bridge_s1_readdatavalid_from_sa = pipeline_bridge_s1_readdatavalid so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pipeline_bridge_s1_readdatavalid_from_sa = pipeline_bridge_s1_readdatavalid;

  //pipeline_bridge_s1_arb_share_counter set values, which is an e_mux
  assign pipeline_bridge_s1_arb_share_set_values = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_arbitrationshare :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_arbitrationshare :
    (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_arbitrationshare :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_arbitrationshare :
    (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_arbitrationshare :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_arbitrationshare :
    1;

  //pipeline_bridge_s1_non_bursting_master_requests mux, which is an e_mux
  assign pipeline_bridge_s1_non_bursting_master_requests = 0;

  //pipeline_bridge_s1_any_bursting_master_saved_grant mux, which is an e_mux
  assign pipeline_bridge_s1_any_bursting_master_saved_grant = custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 |
    custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1 |
    custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 |
    custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1 |
    custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 |
    custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1;

  //pipeline_bridge_s1_arb_share_counter_next_value assignment, which is an e_assign
  assign pipeline_bridge_s1_arb_share_counter_next_value = pipeline_bridge_s1_firsttransfer ? (pipeline_bridge_s1_arb_share_set_values - 1) : |pipeline_bridge_s1_arb_share_counter ? (pipeline_bridge_s1_arb_share_counter - 1) : 0;

  //pipeline_bridge_s1_allgrants all slave grants, which is an e_mux
  assign pipeline_bridge_s1_allgrants = (|pipeline_bridge_s1_grant_vector) |
    (|pipeline_bridge_s1_grant_vector) |
    (|pipeline_bridge_s1_grant_vector) |
    (|pipeline_bridge_s1_grant_vector) |
    (|pipeline_bridge_s1_grant_vector) |
    (|pipeline_bridge_s1_grant_vector);

  //pipeline_bridge_s1_end_xfer assignment, which is an e_assign
  assign pipeline_bridge_s1_end_xfer = ~(pipeline_bridge_s1_waits_for_read | pipeline_bridge_s1_waits_for_write);

  //end_xfer_arb_share_counter_term_pipeline_bridge_s1 arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_pipeline_bridge_s1 = pipeline_bridge_s1_end_xfer & (~pipeline_bridge_s1_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //pipeline_bridge_s1_arb_share_counter arbitration counter enable, which is an e_assign
  assign pipeline_bridge_s1_arb_counter_enable = (end_xfer_arb_share_counter_term_pipeline_bridge_s1 & pipeline_bridge_s1_allgrants) | (end_xfer_arb_share_counter_term_pipeline_bridge_s1 & ~pipeline_bridge_s1_non_bursting_master_requests);

  //pipeline_bridge_s1_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_s1_arb_share_counter <= 0;
      else if (pipeline_bridge_s1_arb_counter_enable)
          pipeline_bridge_s1_arb_share_counter <= pipeline_bridge_s1_arb_share_counter_next_value;
    end


  //pipeline_bridge_s1_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_s1_slavearbiterlockenable <= 0;
      else if ((|pipeline_bridge_s1_master_qreq_vector & end_xfer_arb_share_counter_term_pipeline_bridge_s1) | (end_xfer_arb_share_counter_term_pipeline_bridge_s1 & ~pipeline_bridge_s1_non_bursting_master_requests))
          pipeline_bridge_s1_slavearbiterlockenable <= |pipeline_bridge_s1_arb_share_counter_next_value;
    end


  //custom_dma_burst_1/downstream pipeline_bridge/s1 arbiterlock, which is an e_assign
  assign custom_dma_burst_1_downstream_arbiterlock = pipeline_bridge_s1_slavearbiterlockenable & custom_dma_burst_1_downstream_continuerequest;

  //pipeline_bridge_s1_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign pipeline_bridge_s1_slavearbiterlockenable2 = |pipeline_bridge_s1_arb_share_counter_next_value;

  //custom_dma_burst_1/downstream pipeline_bridge/s1 arbiterlock2, which is an e_assign
  assign custom_dma_burst_1_downstream_arbiterlock2 = pipeline_bridge_s1_slavearbiterlockenable2 & custom_dma_burst_1_downstream_continuerequest;

  //custom_dma_burst_2/downstream pipeline_bridge/s1 arbiterlock, which is an e_assign
  assign custom_dma_burst_2_downstream_arbiterlock = pipeline_bridge_s1_slavearbiterlockenable & custom_dma_burst_2_downstream_continuerequest;

  //custom_dma_burst_2/downstream pipeline_bridge/s1 arbiterlock2, which is an e_assign
  assign custom_dma_burst_2_downstream_arbiterlock2 = pipeline_bridge_s1_slavearbiterlockenable2 & custom_dma_burst_2_downstream_continuerequest;

  //custom_dma_burst_2/downstream granted pipeline_bridge/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_2_downstream_granted_slave_pipeline_bridge_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_2_downstream_granted_slave_pipeline_bridge_s1 <= custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1 ? 1 : (pipeline_bridge_s1_arbitration_holdoff_internal | 0) ? 0 : last_cycle_custom_dma_burst_2_downstream_granted_slave_pipeline_bridge_s1;
    end


  //custom_dma_burst_2_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_2_downstream_continuerequest = last_cycle_custom_dma_burst_2_downstream_granted_slave_pipeline_bridge_s1 & 1;

  //pipeline_bridge_s1_any_continuerequest at least one master continues requesting, which is an e_mux
  assign pipeline_bridge_s1_any_continuerequest = custom_dma_burst_2_downstream_continuerequest |
    custom_dma_burst_1_downstream_continuerequest;

  assign custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1 = custom_dma_burst_1_downstream_requests_pipeline_bridge_s1 & ~((custom_dma_burst_1_downstream_read & ((custom_dma_burst_1_downstream_latency_counter != 0) | (1 < custom_dma_burst_1_downstream_latency_counter))) | custom_dma_burst_2_downstream_arbiterlock);
  //unique name for pipeline_bridge_s1_move_on_to_next_transaction, which is an e_assign
  assign pipeline_bridge_s1_move_on_to_next_transaction = pipeline_bridge_s1_readdatavalid_from_sa;

  //rdv_fifo_for_custom_dma_burst_1_downstream_to_pipeline_bridge_s1, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_custom_dma_burst_1_downstream_to_pipeline_bridge_s1_module rdv_fifo_for_custom_dma_burst_1_downstream_to_pipeline_bridge_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1),
      .data_out             (custom_dma_burst_1_downstream_rdv_fifo_output_from_pipeline_bridge_s1),
      .empty                (),
      .fifo_contains_ones_n (custom_dma_burst_1_downstream_rdv_fifo_empty_pipeline_bridge_s1),
      .full                 (),
      .read                 (pipeline_bridge_s1_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~pipeline_bridge_s1_waits_for_read)
    );

  assign custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register = ~custom_dma_burst_1_downstream_rdv_fifo_empty_pipeline_bridge_s1;
  //local readdatavalid custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1, which is an e_mux
  assign custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1 = (pipeline_bridge_s1_readdatavalid_from_sa & custom_dma_burst_1_downstream_rdv_fifo_output_from_pipeline_bridge_s1) & ~ custom_dma_burst_1_downstream_rdv_fifo_empty_pipeline_bridge_s1;

  //pipeline_bridge_s1_writedata mux, which is an e_mux
  assign pipeline_bridge_s1_writedata = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_writedata :
    custom_dma_burst_2_downstream_writedata;

  //assign pipeline_bridge_s1_endofpacket_from_sa = pipeline_bridge_s1_endofpacket so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pipeline_bridge_s1_endofpacket_from_sa = pipeline_bridge_s1_endofpacket;

  assign custom_dma_burst_2_downstream_requests_pipeline_bridge_s1 = (1) & (custom_dma_burst_2_downstream_read | custom_dma_burst_2_downstream_write);
  //custom_dma_burst_1/downstream granted pipeline_bridge/s1 last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          last_cycle_custom_dma_burst_1_downstream_granted_slave_pipeline_bridge_s1 <= 0;
      else 
        last_cycle_custom_dma_burst_1_downstream_granted_slave_pipeline_bridge_s1 <= custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 ? 1 : (pipeline_bridge_s1_arbitration_holdoff_internal | 0) ? 0 : last_cycle_custom_dma_burst_1_downstream_granted_slave_pipeline_bridge_s1;
    end


  //custom_dma_burst_1_downstream_continuerequest continued request, which is an e_mux
  assign custom_dma_burst_1_downstream_continuerequest = last_cycle_custom_dma_burst_1_downstream_granted_slave_pipeline_bridge_s1 & 1;

  assign custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1 = custom_dma_burst_2_downstream_requests_pipeline_bridge_s1 & ~((custom_dma_burst_2_downstream_read & ((custom_dma_burst_2_downstream_latency_counter != 0) | (1 < custom_dma_burst_2_downstream_latency_counter))) | custom_dma_burst_1_downstream_arbiterlock);
  //rdv_fifo_for_custom_dma_burst_2_downstream_to_pipeline_bridge_s1, which is an e_fifo_with_registered_outputs
  rdv_fifo_for_custom_dma_burst_2_downstream_to_pipeline_bridge_s1_module rdv_fifo_for_custom_dma_burst_2_downstream_to_pipeline_bridge_s1
    (
      .clear_fifo           (1'b0),
      .clk                  (clk),
      .data_in              (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1),
      .data_out             (custom_dma_burst_2_downstream_rdv_fifo_output_from_pipeline_bridge_s1),
      .empty                (),
      .fifo_contains_ones_n (custom_dma_burst_2_downstream_rdv_fifo_empty_pipeline_bridge_s1),
      .full                 (),
      .read                 (pipeline_bridge_s1_move_on_to_next_transaction),
      .reset_n              (reset_n),
      .sync_reset           (1'b0),
      .write                (in_a_read_cycle & ~pipeline_bridge_s1_waits_for_read)
    );

  assign custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register = ~custom_dma_burst_2_downstream_rdv_fifo_empty_pipeline_bridge_s1;
  //local readdatavalid custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1, which is an e_mux
  assign custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1 = (pipeline_bridge_s1_readdatavalid_from_sa & custom_dma_burst_2_downstream_rdv_fifo_output_from_pipeline_bridge_s1) & ~ custom_dma_burst_2_downstream_rdv_fifo_empty_pipeline_bridge_s1;

  //allow new arb cycle for pipeline_bridge/s1, which is an e_assign
  assign pipeline_bridge_s1_allow_new_arb_cycle = ~custom_dma_burst_1_downstream_arbiterlock & ~custom_dma_burst_2_downstream_arbiterlock;

  //custom_dma_burst_2/downstream assignment into master qualified-requests vector for pipeline_bridge/s1, which is an e_assign
  assign pipeline_bridge_s1_master_qreq_vector[0] = custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1;

  //custom_dma_burst_2/downstream grant pipeline_bridge/s1, which is an e_assign
  assign custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 = pipeline_bridge_s1_grant_vector[0];

  //custom_dma_burst_2/downstream saved-grant pipeline_bridge/s1, which is an e_assign
  assign custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1 = pipeline_bridge_s1_arb_winner[0];

  //custom_dma_burst_1/downstream assignment into master qualified-requests vector for pipeline_bridge/s1, which is an e_assign
  assign pipeline_bridge_s1_master_qreq_vector[1] = custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1;

  //custom_dma_burst_1/downstream grant pipeline_bridge/s1, which is an e_assign
  assign custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 = pipeline_bridge_s1_grant_vector[1];

  //custom_dma_burst_1/downstream saved-grant pipeline_bridge/s1, which is an e_assign
  assign custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 = pipeline_bridge_s1_arb_winner[1];

  //pipeline_bridge/s1 chosen-master double-vector, which is an e_assign
  assign pipeline_bridge_s1_chosen_master_double_vector = {pipeline_bridge_s1_master_qreq_vector, pipeline_bridge_s1_master_qreq_vector} & ({~pipeline_bridge_s1_master_qreq_vector, ~pipeline_bridge_s1_master_qreq_vector} + pipeline_bridge_s1_arb_addend);

  //stable onehot encoding of arb winner
  assign pipeline_bridge_s1_arb_winner = (pipeline_bridge_s1_allow_new_arb_cycle & | pipeline_bridge_s1_grant_vector) ? pipeline_bridge_s1_grant_vector : pipeline_bridge_s1_saved_chosen_master_vector;

  //saved pipeline_bridge_s1_grant_vector, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_s1_saved_chosen_master_vector <= 0;
      else if (pipeline_bridge_s1_allow_new_arb_cycle)
          pipeline_bridge_s1_saved_chosen_master_vector <= |pipeline_bridge_s1_grant_vector ? pipeline_bridge_s1_grant_vector : pipeline_bridge_s1_saved_chosen_master_vector;
    end


  //onehot encoding of chosen master
  assign pipeline_bridge_s1_grant_vector = {(pipeline_bridge_s1_chosen_master_double_vector[1] | pipeline_bridge_s1_chosen_master_double_vector[3]),
    (pipeline_bridge_s1_chosen_master_double_vector[0] | pipeline_bridge_s1_chosen_master_double_vector[2])};

  //pipeline_bridge/s1 chosen master rotated left, which is an e_assign
  assign pipeline_bridge_s1_chosen_master_rot_left = (pipeline_bridge_s1_arb_winner << 1) ? (pipeline_bridge_s1_arb_winner << 1) : 1;

  //pipeline_bridge/s1's addend for next-master-grant
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_s1_arb_addend <= 1;
      else if (|pipeline_bridge_s1_grant_vector)
          pipeline_bridge_s1_arb_addend <= pipeline_bridge_s1_end_xfer? pipeline_bridge_s1_chosen_master_rot_left : pipeline_bridge_s1_grant_vector;
    end


  //pipeline_bridge_s1_reset_n assignment, which is an e_assign
  assign pipeline_bridge_s1_reset_n = reset_n;

  assign pipeline_bridge_s1_chipselect = custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 | custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;
  //pipeline_bridge_s1_firsttransfer first transaction, which is an e_assign
  assign pipeline_bridge_s1_firsttransfer = pipeline_bridge_s1_begins_xfer ? pipeline_bridge_s1_unreg_firsttransfer : pipeline_bridge_s1_reg_firsttransfer;

  //pipeline_bridge_s1_unreg_firsttransfer first transaction, which is an e_assign
  assign pipeline_bridge_s1_unreg_firsttransfer = ~(pipeline_bridge_s1_slavearbiterlockenable & pipeline_bridge_s1_any_continuerequest);

  //pipeline_bridge_s1_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_s1_reg_firsttransfer <= 1'b1;
      else if (pipeline_bridge_s1_begins_xfer)
          pipeline_bridge_s1_reg_firsttransfer <= pipeline_bridge_s1_unreg_firsttransfer;
    end


  //pipeline_bridge_s1_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign pipeline_bridge_s1_beginbursttransfer_internal = pipeline_bridge_s1_begins_xfer;

  //pipeline_bridge_s1_arbitration_holdoff_internal arbitration_holdoff, which is an e_assign
  assign pipeline_bridge_s1_arbitration_holdoff_internal = pipeline_bridge_s1_begins_xfer & pipeline_bridge_s1_firsttransfer;

  //pipeline_bridge_s1_read assignment, which is an e_mux
  assign pipeline_bridge_s1_read = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_1_downstream_read) | (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_2_downstream_read);

  //pipeline_bridge_s1_write assignment, which is an e_mux
  assign pipeline_bridge_s1_write = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_1_downstream_write) | (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_2_downstream_write);

  assign shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_1_downstream = custom_dma_burst_1_downstream_address_to_slave;
  //pipeline_bridge_s1_address mux, which is an e_mux
  assign pipeline_bridge_s1_address = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? (shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_1_downstream >> 2) :
    (shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_2_downstream >> 2);

  assign shifted_address_to_pipeline_bridge_s1_from_custom_dma_burst_2_downstream = custom_dma_burst_2_downstream_address_to_slave;
  //slaveid pipeline_bridge_s1_nativeaddress nativeaddress mux, which is an e_mux
  assign pipeline_bridge_s1_nativeaddress = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_nativeaddress :
    custom_dma_burst_2_downstream_nativeaddress;

  //d1_pipeline_bridge_s1_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_pipeline_bridge_s1_end_xfer <= 1;
      else 
        d1_pipeline_bridge_s1_end_xfer <= pipeline_bridge_s1_end_xfer;
    end


  //pipeline_bridge_s1_waits_for_read in a cycle, which is an e_mux
  assign pipeline_bridge_s1_waits_for_read = pipeline_bridge_s1_in_a_read_cycle & pipeline_bridge_s1_waitrequest_from_sa;

  //pipeline_bridge_s1_in_a_read_cycle assignment, which is an e_assign
  assign pipeline_bridge_s1_in_a_read_cycle = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_1_downstream_read) | (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_2_downstream_read);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = pipeline_bridge_s1_in_a_read_cycle;

  //pipeline_bridge_s1_waits_for_write in a cycle, which is an e_mux
  assign pipeline_bridge_s1_waits_for_write = pipeline_bridge_s1_in_a_write_cycle & pipeline_bridge_s1_waitrequest_from_sa;

  //pipeline_bridge_s1_in_a_write_cycle assignment, which is an e_assign
  assign pipeline_bridge_s1_in_a_write_cycle = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_1_downstream_write) | (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 & custom_dma_burst_2_downstream_write);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = pipeline_bridge_s1_in_a_write_cycle;

  assign wait_for_pipeline_bridge_s1_counter = 0;
  //pipeline_bridge_s1_byteenable byte enable port mux, which is an e_mux
  assign pipeline_bridge_s1_byteenable = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_byteenable :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_byteenable :
    -1;

  //burstcount mux, which is an e_mux
  assign pipeline_bridge_s1_burstcount = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_burstcount :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_burstcount :
    1;

  //pipeline_bridge/s1 arbiterlock assigned from _handle_arbiterlock, which is an e_mux
  assign pipeline_bridge_s1_arbiterlock = (custom_dma_burst_1_downstream_arbiterlock)? custom_dma_burst_1_downstream_arbiterlock :
    custom_dma_burst_2_downstream_arbiterlock;

  //pipeline_bridge/s1 arbiterlock2 assigned from _handle_arbiterlock2, which is an e_mux
  assign pipeline_bridge_s1_arbiterlock2 = (custom_dma_burst_1_downstream_arbiterlock2)? custom_dma_burst_1_downstream_arbiterlock2 :
    custom_dma_burst_2_downstream_arbiterlock2;

  //debugaccess mux, which is an e_mux
  assign pipeline_bridge_s1_debugaccess = (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_1_downstream_debugaccess :
    (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1)? custom_dma_burst_2_downstream_debugaccess :
    0;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //pipeline_bridge/s1 enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //custom_dma_burst_1/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_1_downstream_requests_pipeline_bridge_s1 && (custom_dma_burst_1_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_1/downstream drove 0 on its 'arbitrationshare' port while accessing slave pipeline_bridge/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_1/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_1_downstream_requests_pipeline_bridge_s1 && (custom_dma_burst_1_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_1/downstream drove 0 on its 'burstcount' port while accessing slave pipeline_bridge/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_2/downstream non-zero arbitrationshare assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_2_downstream_requests_pipeline_bridge_s1 && (custom_dma_burst_2_downstream_arbitrationshare == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_2/downstream drove 0 on its 'arbitrationshare' port while accessing slave pipeline_bridge/s1", $time);
          $stop;
        end
    end


  //custom_dma_burst_2/downstream non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_2_downstream_requests_pipeline_bridge_s1 && (custom_dma_burst_2_downstream_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: custom_dma_burst_2/downstream drove 0 on its 'burstcount' port while accessing slave pipeline_bridge/s1", $time);
          $stop;
        end
    end


  //grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1 + custom_dma_burst_2_downstream_granted_pipeline_bridge_s1 > 1)
        begin
          $write("%0d ns: > 1 of grant signals are active simultaneously", $time);
          $stop;
        end
    end


  //saved_grant signals are active simultaneously, which is an e_process
  always @(posedge clk)
    begin
      if (custom_dma_burst_1_downstream_saved_grant_pipeline_bridge_s1 + custom_dma_burst_2_downstream_saved_grant_pipeline_bridge_s1 > 1)
        begin
          $write("%0d ns: > 1 of saved_grant signals are active simultaneously", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge_m1_arbitrator (
                                       // inputs:
                                        clk,
                                        cpu_jtag_debug_module_readdata_from_sa,
                                        custom_dma_clock_0_in_endofpacket_from_sa,
                                        custom_dma_clock_0_in_readdata_from_sa,
                                        custom_dma_clock_0_in_waitrequest_from_sa,
                                        d1_cpu_jtag_debug_module_end_xfer,
                                        d1_custom_dma_clock_0_in_end_xfer,
                                        d1_fir_dma_control_end_xfer,
                                        d1_jtag_uart_avalon_jtag_slave_end_xfer,
                                        d1_sysid_control_slave_end_xfer,
                                        d1_timestamp_timer_s1_end_xfer,
                                        fir_dma_control_readdata_from_sa,
                                        jtag_uart_avalon_jtag_slave_readdata_from_sa,
                                        jtag_uart_avalon_jtag_slave_waitrequest_from_sa,
                                        pipeline_bridge_m1_address,
                                        pipeline_bridge_m1_burstcount,
                                        pipeline_bridge_m1_byteenable,
                                        pipeline_bridge_m1_chipselect,
                                        pipeline_bridge_m1_granted_cpu_jtag_debug_module,
                                        pipeline_bridge_m1_granted_custom_dma_clock_0_in,
                                        pipeline_bridge_m1_granted_fir_dma_control,
                                        pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave,
                                        pipeline_bridge_m1_granted_sysid_control_slave,
                                        pipeline_bridge_m1_granted_timestamp_timer_s1,
                                        pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module,
                                        pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in,
                                        pipeline_bridge_m1_qualified_request_fir_dma_control,
                                        pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave,
                                        pipeline_bridge_m1_qualified_request_sysid_control_slave,
                                        pipeline_bridge_m1_qualified_request_timestamp_timer_s1,
                                        pipeline_bridge_m1_read,
                                        pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module,
                                        pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in,
                                        pipeline_bridge_m1_read_data_valid_fir_dma_control,
                                        pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave,
                                        pipeline_bridge_m1_read_data_valid_sysid_control_slave,
                                        pipeline_bridge_m1_read_data_valid_timestamp_timer_s1,
                                        pipeline_bridge_m1_requests_cpu_jtag_debug_module,
                                        pipeline_bridge_m1_requests_custom_dma_clock_0_in,
                                        pipeline_bridge_m1_requests_fir_dma_control,
                                        pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave,
                                        pipeline_bridge_m1_requests_sysid_control_slave,
                                        pipeline_bridge_m1_requests_timestamp_timer_s1,
                                        pipeline_bridge_m1_write,
                                        pipeline_bridge_m1_writedata,
                                        reset_n,
                                        sysid_control_slave_readdata_from_sa,
                                        timestamp_timer_s1_readdata_from_sa,

                                       // outputs:
                                        pipeline_bridge_m1_address_to_slave,
                                        pipeline_bridge_m1_endofpacket,
                                        pipeline_bridge_m1_latency_counter,
                                        pipeline_bridge_m1_readdata,
                                        pipeline_bridge_m1_readdatavalid,
                                        pipeline_bridge_m1_waitrequest
                                     )
;

  output  [ 11: 0] pipeline_bridge_m1_address_to_slave;
  output           pipeline_bridge_m1_endofpacket;
  output           pipeline_bridge_m1_latency_counter;
  output  [ 31: 0] pipeline_bridge_m1_readdata;
  output           pipeline_bridge_m1_readdatavalid;
  output           pipeline_bridge_m1_waitrequest;
  input            clk;
  input   [ 31: 0] cpu_jtag_debug_module_readdata_from_sa;
  input            custom_dma_clock_0_in_endofpacket_from_sa;
  input   [ 15: 0] custom_dma_clock_0_in_readdata_from_sa;
  input            custom_dma_clock_0_in_waitrequest_from_sa;
  input            d1_cpu_jtag_debug_module_end_xfer;
  input            d1_custom_dma_clock_0_in_end_xfer;
  input            d1_fir_dma_control_end_xfer;
  input            d1_jtag_uart_avalon_jtag_slave_end_xfer;
  input            d1_sysid_control_slave_end_xfer;
  input            d1_timestamp_timer_s1_end_xfer;
  input   [ 31: 0] fir_dma_control_readdata_from_sa;
  input   [ 31: 0] jtag_uart_avalon_jtag_slave_readdata_from_sa;
  input            jtag_uart_avalon_jtag_slave_waitrequest_from_sa;
  input   [ 11: 0] pipeline_bridge_m1_address;
  input            pipeline_bridge_m1_burstcount;
  input   [  3: 0] pipeline_bridge_m1_byteenable;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_granted_cpu_jtag_debug_module;
  input            pipeline_bridge_m1_granted_custom_dma_clock_0_in;
  input            pipeline_bridge_m1_granted_fir_dma_control;
  input            pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave;
  input            pipeline_bridge_m1_granted_sysid_control_slave;
  input            pipeline_bridge_m1_granted_timestamp_timer_s1;
  input            pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module;
  input            pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in;
  input            pipeline_bridge_m1_qualified_request_fir_dma_control;
  input            pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave;
  input            pipeline_bridge_m1_qualified_request_sysid_control_slave;
  input            pipeline_bridge_m1_qualified_request_timestamp_timer_s1;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module;
  input            pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in;
  input            pipeline_bridge_m1_read_data_valid_fir_dma_control;
  input            pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave;
  input            pipeline_bridge_m1_read_data_valid_sysid_control_slave;
  input            pipeline_bridge_m1_read_data_valid_timestamp_timer_s1;
  input            pipeline_bridge_m1_requests_cpu_jtag_debug_module;
  input            pipeline_bridge_m1_requests_custom_dma_clock_0_in;
  input            pipeline_bridge_m1_requests_fir_dma_control;
  input            pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;
  input            pipeline_bridge_m1_requests_sysid_control_slave;
  input            pipeline_bridge_m1_requests_timestamp_timer_s1;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;
  input   [ 31: 0] sysid_control_slave_readdata_from_sa;
  input   [ 15: 0] timestamp_timer_s1_readdata_from_sa;

  reg              active_and_waiting_last_time;
  wire             latency_load_value;
  wire             p1_pipeline_bridge_m1_latency_counter;
  reg     [ 11: 0] pipeline_bridge_m1_address_last_time;
  wire    [ 11: 0] pipeline_bridge_m1_address_to_slave;
  reg              pipeline_bridge_m1_burstcount_last_time;
  reg     [  3: 0] pipeline_bridge_m1_byteenable_last_time;
  reg              pipeline_bridge_m1_chipselect_last_time;
  wire             pipeline_bridge_m1_endofpacket;
  wire             pipeline_bridge_m1_is_granted_some_slave;
  reg              pipeline_bridge_m1_latency_counter;
  reg              pipeline_bridge_m1_read_but_no_slave_selected;
  reg              pipeline_bridge_m1_read_last_time;
  wire    [ 31: 0] pipeline_bridge_m1_readdata;
  wire             pipeline_bridge_m1_readdatavalid;
  wire             pipeline_bridge_m1_run;
  wire             pipeline_bridge_m1_waitrequest;
  reg              pipeline_bridge_m1_write_last_time;
  reg     [ 31: 0] pipeline_bridge_m1_writedata_last_time;
  wire             pre_flush_pipeline_bridge_m1_readdatavalid;
  wire             r_0;
  wire             r_1;
  //r_0 master_run cascaded wait assignment, which is an e_assign
  assign r_0 = 1 & (pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module | ~pipeline_bridge_m1_requests_cpu_jtag_debug_module) & ((~pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module | ~(pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) | (1 & ~d1_cpu_jtag_debug_module_end_xfer & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))) & ((~pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module | ~(pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect) | (1 & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect)))) & 1 & (pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in | ~pipeline_bridge_m1_requests_custom_dma_clock_0_in) & ((~pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in | ~pipeline_bridge_m1_chipselect | (1 & ~custom_dma_clock_0_in_waitrequest_from_sa & pipeline_bridge_m1_chipselect))) & ((~pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in | ~pipeline_bridge_m1_chipselect | (1 & ~custom_dma_clock_0_in_waitrequest_from_sa & pipeline_bridge_m1_chipselect))) & 1 & (pipeline_bridge_m1_qualified_request_fir_dma_control | ~pipeline_bridge_m1_requests_fir_dma_control) & ((~pipeline_bridge_m1_qualified_request_fir_dma_control | ~pipeline_bridge_m1_chipselect | (1 & pipeline_bridge_m1_chipselect))) & ((~pipeline_bridge_m1_qualified_request_fir_dma_control | ~pipeline_bridge_m1_chipselect | (1 & pipeline_bridge_m1_chipselect))) & 1 & (pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave | ~pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave) & ((~pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave | ~pipeline_bridge_m1_chipselect | (1 & ~jtag_uart_avalon_jtag_slave_waitrequest_from_sa & pipeline_bridge_m1_chipselect))) & ((~pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave | ~pipeline_bridge_m1_chipselect | (1 & ~jtag_uart_avalon_jtag_slave_waitrequest_from_sa & pipeline_bridge_m1_chipselect))) & 1 & (pipeline_bridge_m1_qualified_request_sysid_control_slave | ~pipeline_bridge_m1_requests_sysid_control_slave) & ((~pipeline_bridge_m1_qualified_request_sysid_control_slave | ~(pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) | (1 & ~d1_sysid_control_slave_end_xfer & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))) & ((~pipeline_bridge_m1_qualified_request_sysid_control_slave | ~(pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect) | (1 & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect))));

  //cascaded wait assignment, which is an e_assign
  assign pipeline_bridge_m1_run = r_0 & r_1;

  //r_1 master_run cascaded wait assignment, which is an e_assign
  assign r_1 = 1 & (pipeline_bridge_m1_qualified_request_timestamp_timer_s1 | ~pipeline_bridge_m1_requests_timestamp_timer_s1) & ((~pipeline_bridge_m1_qualified_request_timestamp_timer_s1 | ~(pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) | (1 & ~d1_timestamp_timer_s1_end_xfer & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))) & ((~pipeline_bridge_m1_qualified_request_timestamp_timer_s1 | ~(pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect) | (1 & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect))));

  //optimize select-logic by passing only those address bits which matter.
  assign pipeline_bridge_m1_address_to_slave = pipeline_bridge_m1_address[11 : 0];

  //pipeline_bridge_m1_read_but_no_slave_selected assignment, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_read_but_no_slave_selected <= 0;
      else 
        pipeline_bridge_m1_read_but_no_slave_selected <= (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & pipeline_bridge_m1_run & ~pipeline_bridge_m1_is_granted_some_slave;
    end


  //some slave is getting selected, which is an e_mux
  assign pipeline_bridge_m1_is_granted_some_slave = pipeline_bridge_m1_granted_cpu_jtag_debug_module |
    pipeline_bridge_m1_granted_custom_dma_clock_0_in |
    pipeline_bridge_m1_granted_fir_dma_control |
    pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave |
    pipeline_bridge_m1_granted_sysid_control_slave |
    pipeline_bridge_m1_granted_timestamp_timer_s1;

  //latent slave read data valids which may be flushed, which is an e_mux
  assign pre_flush_pipeline_bridge_m1_readdatavalid = pipeline_bridge_m1_read_data_valid_fir_dma_control;

  //latent slave read data valid which is not flushed, which is an e_mux
  assign pipeline_bridge_m1_readdatavalid = pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module |
    pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in |
    pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave |
    pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_data_valid_sysid_control_slave |
    pipeline_bridge_m1_read_but_no_slave_selected |
    pre_flush_pipeline_bridge_m1_readdatavalid |
    pipeline_bridge_m1_read_data_valid_timestamp_timer_s1;

  //pipeline_bridge/m1 readdata mux, which is an e_mux
  assign pipeline_bridge_m1_readdata = ({32 {~((pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))}} | cpu_jtag_debug_module_readdata_from_sa) &
    ({32 {~((pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))}} | custom_dma_clock_0_in_readdata_from_sa) &
    ({32 {~pipeline_bridge_m1_read_data_valid_fir_dma_control}} | fir_dma_control_readdata_from_sa) &
    ({32 {~((pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))}} | jtag_uart_avalon_jtag_slave_readdata_from_sa) &
    ({32 {~((pipeline_bridge_m1_qualified_request_sysid_control_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))}} | sysid_control_slave_readdata_from_sa) &
    ({32 {~((pipeline_bridge_m1_qualified_request_timestamp_timer_s1 & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))}} | timestamp_timer_s1_readdata_from_sa);

  //actual waitrequest port, which is an e_assign
  assign pipeline_bridge_m1_waitrequest = ~pipeline_bridge_m1_run;

  //latent max counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_latency_counter <= 0;
      else 
        pipeline_bridge_m1_latency_counter <= p1_pipeline_bridge_m1_latency_counter;
    end


  //latency counter load mux, which is an e_mux
  assign p1_pipeline_bridge_m1_latency_counter = ((pipeline_bridge_m1_run & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect)))? latency_load_value :
    (pipeline_bridge_m1_latency_counter)? pipeline_bridge_m1_latency_counter - 1 :
    0;

  //read latency load values, which is an e_mux
  assign latency_load_value = {1 {pipeline_bridge_m1_requests_fir_dma_control}} & 1;

  //mux pipeline_bridge_m1_endofpacket, which is an e_mux
  assign pipeline_bridge_m1_endofpacket = custom_dma_clock_0_in_endofpacket_from_sa;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //pipeline_bridge_m1_address check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_address_last_time <= 0;
      else 
        pipeline_bridge_m1_address_last_time <= pipeline_bridge_m1_address;
    end


  //pipeline_bridge/m1 waited last time, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          active_and_waiting_last_time <= 0;
      else 
        active_and_waiting_last_time <= pipeline_bridge_m1_waitrequest & pipeline_bridge_m1_chipselect;
    end


  //pipeline_bridge_m1_address matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_address != pipeline_bridge_m1_address_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_address did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_chipselect check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_chipselect_last_time <= 0;
      else 
        pipeline_bridge_m1_chipselect_last_time <= pipeline_bridge_m1_chipselect;
    end


  //pipeline_bridge_m1_chipselect matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_chipselect != pipeline_bridge_m1_chipselect_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_chipselect did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_burstcount check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_burstcount_last_time <= 0;
      else 
        pipeline_bridge_m1_burstcount_last_time <= pipeline_bridge_m1_burstcount;
    end


  //pipeline_bridge_m1_burstcount matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_burstcount != pipeline_bridge_m1_burstcount_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_burstcount did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_byteenable check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_byteenable_last_time <= 0;
      else 
        pipeline_bridge_m1_byteenable_last_time <= pipeline_bridge_m1_byteenable;
    end


  //pipeline_bridge_m1_byteenable matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_byteenable != pipeline_bridge_m1_byteenable_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_byteenable did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_read check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_read_last_time <= 0;
      else 
        pipeline_bridge_m1_read_last_time <= pipeline_bridge_m1_read;
    end


  //pipeline_bridge_m1_read matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_read != pipeline_bridge_m1_read_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_read did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_write check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_write_last_time <= 0;
      else 
        pipeline_bridge_m1_write_last_time <= pipeline_bridge_m1_write;
    end


  //pipeline_bridge_m1_write matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_write != pipeline_bridge_m1_write_last_time))
        begin
          $write("%0d ns: pipeline_bridge_m1_write did not heed wait!!!", $time);
          $stop;
        end
    end


  //pipeline_bridge_m1_writedata check against wait, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pipeline_bridge_m1_writedata_last_time <= 0;
      else 
        pipeline_bridge_m1_writedata_last_time <= pipeline_bridge_m1_writedata;
    end


  //pipeline_bridge_m1_writedata matches last port_name, which is an e_process
  always @(posedge clk)
    begin
      if (active_and_waiting_last_time & (pipeline_bridge_m1_writedata != pipeline_bridge_m1_writedata_last_time) & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect))
        begin
          $write("%0d ns: pipeline_bridge_m1_writedata did not heed wait!!!", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge_bridge_arbitrator 
;



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pll_s1_arbitrator (
                           // inputs:
                            clk,
                            custom_dma_clock_0_out_address_to_slave,
                            custom_dma_clock_0_out_nativeaddress,
                            custom_dma_clock_0_out_read,
                            custom_dma_clock_0_out_write,
                            custom_dma_clock_0_out_writedata,
                            pll_s1_readdata,
                            pll_s1_resetrequest,
                            reset_n,

                           // outputs:
                            custom_dma_clock_0_out_granted_pll_s1,
                            custom_dma_clock_0_out_qualified_request_pll_s1,
                            custom_dma_clock_0_out_read_data_valid_pll_s1,
                            custom_dma_clock_0_out_requests_pll_s1,
                            d1_pll_s1_end_xfer,
                            pll_s1_address,
                            pll_s1_chipselect,
                            pll_s1_read,
                            pll_s1_readdata_from_sa,
                            pll_s1_reset_n,
                            pll_s1_resetrequest_from_sa,
                            pll_s1_write,
                            pll_s1_writedata
                         )
;

  output           custom_dma_clock_0_out_granted_pll_s1;
  output           custom_dma_clock_0_out_qualified_request_pll_s1;
  output           custom_dma_clock_0_out_read_data_valid_pll_s1;
  output           custom_dma_clock_0_out_requests_pll_s1;
  output           d1_pll_s1_end_xfer;
  output  [  2: 0] pll_s1_address;
  output           pll_s1_chipselect;
  output           pll_s1_read;
  output  [ 15: 0] pll_s1_readdata_from_sa;
  output           pll_s1_reset_n;
  output           pll_s1_resetrequest_from_sa;
  output           pll_s1_write;
  output  [ 15: 0] pll_s1_writedata;
  input            clk;
  input   [  3: 0] custom_dma_clock_0_out_address_to_slave;
  input   [  2: 0] custom_dma_clock_0_out_nativeaddress;
  input            custom_dma_clock_0_out_read;
  input            custom_dma_clock_0_out_write;
  input   [ 15: 0] custom_dma_clock_0_out_writedata;
  input   [ 15: 0] pll_s1_readdata;
  input            pll_s1_resetrequest;
  input            reset_n;

  wire             custom_dma_clock_0_out_arbiterlock;
  wire             custom_dma_clock_0_out_arbiterlock2;
  wire             custom_dma_clock_0_out_continuerequest;
  wire             custom_dma_clock_0_out_granted_pll_s1;
  wire             custom_dma_clock_0_out_qualified_request_pll_s1;
  wire             custom_dma_clock_0_out_read_data_valid_pll_s1;
  wire             custom_dma_clock_0_out_requests_pll_s1;
  wire             custom_dma_clock_0_out_saved_grant_pll_s1;
  reg              d1_pll_s1_end_xfer;
  reg              d1_reasons_to_wait;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_pll_s1;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire    [  2: 0] pll_s1_address;
  wire             pll_s1_allgrants;
  wire             pll_s1_allow_new_arb_cycle;
  wire             pll_s1_any_bursting_master_saved_grant;
  wire             pll_s1_any_continuerequest;
  wire             pll_s1_arb_counter_enable;
  reg              pll_s1_arb_share_counter;
  wire             pll_s1_arb_share_counter_next_value;
  wire             pll_s1_arb_share_set_values;
  wire             pll_s1_beginbursttransfer_internal;
  wire             pll_s1_begins_xfer;
  wire             pll_s1_chipselect;
  wire             pll_s1_end_xfer;
  wire             pll_s1_firsttransfer;
  wire             pll_s1_grant_vector;
  wire             pll_s1_in_a_read_cycle;
  wire             pll_s1_in_a_write_cycle;
  wire             pll_s1_master_qreq_vector;
  wire             pll_s1_non_bursting_master_requests;
  wire             pll_s1_read;
  wire    [ 15: 0] pll_s1_readdata_from_sa;
  reg              pll_s1_reg_firsttransfer;
  wire             pll_s1_reset_n;
  wire             pll_s1_resetrequest_from_sa;
  reg              pll_s1_slavearbiterlockenable;
  wire             pll_s1_slavearbiterlockenable2;
  wire             pll_s1_unreg_firsttransfer;
  wire             pll_s1_waits_for_read;
  wire             pll_s1_waits_for_write;
  wire             pll_s1_write;
  wire    [ 15: 0] pll_s1_writedata;
  wire             wait_for_pll_s1_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~pll_s1_end_xfer;
    end


  assign pll_s1_begins_xfer = ~d1_reasons_to_wait & ((custom_dma_clock_0_out_qualified_request_pll_s1));
  //assign pll_s1_readdata_from_sa = pll_s1_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pll_s1_readdata_from_sa = pll_s1_readdata;

  assign custom_dma_clock_0_out_requests_pll_s1 = (1) & (custom_dma_clock_0_out_read | custom_dma_clock_0_out_write);
  //pll_s1_arb_share_counter set values, which is an e_mux
  assign pll_s1_arb_share_set_values = 1;

  //pll_s1_non_bursting_master_requests mux, which is an e_mux
  assign pll_s1_non_bursting_master_requests = custom_dma_clock_0_out_requests_pll_s1;

  //pll_s1_any_bursting_master_saved_grant mux, which is an e_mux
  assign pll_s1_any_bursting_master_saved_grant = 0;

  //pll_s1_arb_share_counter_next_value assignment, which is an e_assign
  assign pll_s1_arb_share_counter_next_value = pll_s1_firsttransfer ? (pll_s1_arb_share_set_values - 1) : |pll_s1_arb_share_counter ? (pll_s1_arb_share_counter - 1) : 0;

  //pll_s1_allgrants all slave grants, which is an e_mux
  assign pll_s1_allgrants = |pll_s1_grant_vector;

  //pll_s1_end_xfer assignment, which is an e_assign
  assign pll_s1_end_xfer = ~(pll_s1_waits_for_read | pll_s1_waits_for_write);

  //end_xfer_arb_share_counter_term_pll_s1 arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_pll_s1 = pll_s1_end_xfer & (~pll_s1_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //pll_s1_arb_share_counter arbitration counter enable, which is an e_assign
  assign pll_s1_arb_counter_enable = (end_xfer_arb_share_counter_term_pll_s1 & pll_s1_allgrants) | (end_xfer_arb_share_counter_term_pll_s1 & ~pll_s1_non_bursting_master_requests);

  //pll_s1_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pll_s1_arb_share_counter <= 0;
      else if (pll_s1_arb_counter_enable)
          pll_s1_arb_share_counter <= pll_s1_arb_share_counter_next_value;
    end


  //pll_s1_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pll_s1_slavearbiterlockenable <= 0;
      else if ((|pll_s1_master_qreq_vector & end_xfer_arb_share_counter_term_pll_s1) | (end_xfer_arb_share_counter_term_pll_s1 & ~pll_s1_non_bursting_master_requests))
          pll_s1_slavearbiterlockenable <= |pll_s1_arb_share_counter_next_value;
    end


  //custom_dma_clock_0/out pll/s1 arbiterlock, which is an e_assign
  assign custom_dma_clock_0_out_arbiterlock = pll_s1_slavearbiterlockenable & custom_dma_clock_0_out_continuerequest;

  //pll_s1_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign pll_s1_slavearbiterlockenable2 = |pll_s1_arb_share_counter_next_value;

  //custom_dma_clock_0/out pll/s1 arbiterlock2, which is an e_assign
  assign custom_dma_clock_0_out_arbiterlock2 = pll_s1_slavearbiterlockenable2 & custom_dma_clock_0_out_continuerequest;

  //pll_s1_any_continuerequest at least one master continues requesting, which is an e_assign
  assign pll_s1_any_continuerequest = 1;

  //custom_dma_clock_0_out_continuerequest continued request, which is an e_assign
  assign custom_dma_clock_0_out_continuerequest = 1;

  assign custom_dma_clock_0_out_qualified_request_pll_s1 = custom_dma_clock_0_out_requests_pll_s1;
  //pll_s1_writedata mux, which is an e_mux
  assign pll_s1_writedata = custom_dma_clock_0_out_writedata;

  //master is always granted when requested
  assign custom_dma_clock_0_out_granted_pll_s1 = custom_dma_clock_0_out_qualified_request_pll_s1;

  //custom_dma_clock_0/out saved-grant pll/s1, which is an e_assign
  assign custom_dma_clock_0_out_saved_grant_pll_s1 = custom_dma_clock_0_out_requests_pll_s1;

  //allow new arb cycle for pll/s1, which is an e_assign
  assign pll_s1_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign pll_s1_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign pll_s1_master_qreq_vector = 1;

  //pll_s1_reset_n assignment, which is an e_assign
  assign pll_s1_reset_n = reset_n;

  //assign pll_s1_resetrequest_from_sa = pll_s1_resetrequest so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign pll_s1_resetrequest_from_sa = pll_s1_resetrequest;

  assign pll_s1_chipselect = custom_dma_clock_0_out_granted_pll_s1;
  //pll_s1_firsttransfer first transaction, which is an e_assign
  assign pll_s1_firsttransfer = pll_s1_begins_xfer ? pll_s1_unreg_firsttransfer : pll_s1_reg_firsttransfer;

  //pll_s1_unreg_firsttransfer first transaction, which is an e_assign
  assign pll_s1_unreg_firsttransfer = ~(pll_s1_slavearbiterlockenable & pll_s1_any_continuerequest);

  //pll_s1_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          pll_s1_reg_firsttransfer <= 1'b1;
      else if (pll_s1_begins_xfer)
          pll_s1_reg_firsttransfer <= pll_s1_unreg_firsttransfer;
    end


  //pll_s1_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign pll_s1_beginbursttransfer_internal = pll_s1_begins_xfer;

  //pll_s1_read assignment, which is an e_mux
  assign pll_s1_read = custom_dma_clock_0_out_granted_pll_s1 & custom_dma_clock_0_out_read;

  //pll_s1_write assignment, which is an e_mux
  assign pll_s1_write = custom_dma_clock_0_out_granted_pll_s1 & custom_dma_clock_0_out_write;

  //pll_s1_address mux, which is an e_mux
  assign pll_s1_address = custom_dma_clock_0_out_nativeaddress;

  //d1_pll_s1_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_pll_s1_end_xfer <= 1;
      else 
        d1_pll_s1_end_xfer <= pll_s1_end_xfer;
    end


  //pll_s1_waits_for_read in a cycle, which is an e_mux
  assign pll_s1_waits_for_read = pll_s1_in_a_read_cycle & pll_s1_begins_xfer;

  //pll_s1_in_a_read_cycle assignment, which is an e_assign
  assign pll_s1_in_a_read_cycle = custom_dma_clock_0_out_granted_pll_s1 & custom_dma_clock_0_out_read;

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = pll_s1_in_a_read_cycle;

  //pll_s1_waits_for_write in a cycle, which is an e_mux
  assign pll_s1_waits_for_write = pll_s1_in_a_write_cycle & 0;

  //pll_s1_in_a_write_cycle assignment, which is an e_assign
  assign pll_s1_in_a_write_cycle = custom_dma_clock_0_out_granted_pll_s1 & custom_dma_clock_0_out_write;

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = pll_s1_in_a_write_cycle;

  assign wait_for_pll_s1_counter = 0;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //pll/s1 enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module sysid_control_slave_arbitrator (
                                        // inputs:
                                         clk,
                                         pipeline_bridge_m1_address_to_slave,
                                         pipeline_bridge_m1_burstcount,
                                         pipeline_bridge_m1_chipselect,
                                         pipeline_bridge_m1_latency_counter,
                                         pipeline_bridge_m1_read,
                                         pipeline_bridge_m1_write,
                                         reset_n,
                                         sysid_control_slave_readdata,

                                        // outputs:
                                         d1_sysid_control_slave_end_xfer,
                                         pipeline_bridge_m1_granted_sysid_control_slave,
                                         pipeline_bridge_m1_qualified_request_sysid_control_slave,
                                         pipeline_bridge_m1_read_data_valid_sysid_control_slave,
                                         pipeline_bridge_m1_requests_sysid_control_slave,
                                         sysid_control_slave_address,
                                         sysid_control_slave_readdata_from_sa
                                      )
;

  output           d1_sysid_control_slave_end_xfer;
  output           pipeline_bridge_m1_granted_sysid_control_slave;
  output           pipeline_bridge_m1_qualified_request_sysid_control_slave;
  output           pipeline_bridge_m1_read_data_valid_sysid_control_slave;
  output           pipeline_bridge_m1_requests_sysid_control_slave;
  output           sysid_control_slave_address;
  output  [ 31: 0] sysid_control_slave_readdata_from_sa;
  input            clk;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input            reset_n;
  input   [ 31: 0] sysid_control_slave_readdata;

  reg              d1_reasons_to_wait;
  reg              d1_sysid_control_slave_end_xfer;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_sysid_control_slave;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_sysid_control_slave;
  wire             pipeline_bridge_m1_qualified_request_sysid_control_slave;
  wire             pipeline_bridge_m1_read_data_valid_sysid_control_slave;
  wire             pipeline_bridge_m1_requests_sysid_control_slave;
  wire             pipeline_bridge_m1_saved_grant_sysid_control_slave;
  wire    [ 11: 0] shifted_address_to_sysid_control_slave_from_pipeline_bridge_m1;
  wire             sysid_control_slave_address;
  wire             sysid_control_slave_allgrants;
  wire             sysid_control_slave_allow_new_arb_cycle;
  wire             sysid_control_slave_any_bursting_master_saved_grant;
  wire             sysid_control_slave_any_continuerequest;
  wire             sysid_control_slave_arb_counter_enable;
  reg              sysid_control_slave_arb_share_counter;
  wire             sysid_control_slave_arb_share_counter_next_value;
  wire             sysid_control_slave_arb_share_set_values;
  wire             sysid_control_slave_beginbursttransfer_internal;
  wire             sysid_control_slave_begins_xfer;
  wire             sysid_control_slave_end_xfer;
  wire             sysid_control_slave_firsttransfer;
  wire             sysid_control_slave_grant_vector;
  wire             sysid_control_slave_in_a_read_cycle;
  wire             sysid_control_slave_in_a_write_cycle;
  wire             sysid_control_slave_master_qreq_vector;
  wire             sysid_control_slave_non_bursting_master_requests;
  wire    [ 31: 0] sysid_control_slave_readdata_from_sa;
  reg              sysid_control_slave_reg_firsttransfer;
  reg              sysid_control_slave_slavearbiterlockenable;
  wire             sysid_control_slave_slavearbiterlockenable2;
  wire             sysid_control_slave_unreg_firsttransfer;
  wire             sysid_control_slave_waits_for_read;
  wire             sysid_control_slave_waits_for_write;
  wire             wait_for_sysid_control_slave_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~sysid_control_slave_end_xfer;
    end


  assign sysid_control_slave_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_sysid_control_slave));
  //assign sysid_control_slave_readdata_from_sa = sysid_control_slave_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign sysid_control_slave_readdata_from_sa = sysid_control_slave_readdata;

  assign pipeline_bridge_m1_requests_sysid_control_slave = (({pipeline_bridge_m1_address_to_slave[11 : 3] , 3'b0} == 12'h860) & pipeline_bridge_m1_chipselect) & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);
  //sysid_control_slave_arb_share_counter set values, which is an e_mux
  assign sysid_control_slave_arb_share_set_values = 1;

  //sysid_control_slave_non_bursting_master_requests mux, which is an e_mux
  assign sysid_control_slave_non_bursting_master_requests = pipeline_bridge_m1_requests_sysid_control_slave;

  //sysid_control_slave_any_bursting_master_saved_grant mux, which is an e_mux
  assign sysid_control_slave_any_bursting_master_saved_grant = 0;

  //sysid_control_slave_arb_share_counter_next_value assignment, which is an e_assign
  assign sysid_control_slave_arb_share_counter_next_value = sysid_control_slave_firsttransfer ? (sysid_control_slave_arb_share_set_values - 1) : |sysid_control_slave_arb_share_counter ? (sysid_control_slave_arb_share_counter - 1) : 0;

  //sysid_control_slave_allgrants all slave grants, which is an e_mux
  assign sysid_control_slave_allgrants = |sysid_control_slave_grant_vector;

  //sysid_control_slave_end_xfer assignment, which is an e_assign
  assign sysid_control_slave_end_xfer = ~(sysid_control_slave_waits_for_read | sysid_control_slave_waits_for_write);

  //end_xfer_arb_share_counter_term_sysid_control_slave arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_sysid_control_slave = sysid_control_slave_end_xfer & (~sysid_control_slave_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //sysid_control_slave_arb_share_counter arbitration counter enable, which is an e_assign
  assign sysid_control_slave_arb_counter_enable = (end_xfer_arb_share_counter_term_sysid_control_slave & sysid_control_slave_allgrants) | (end_xfer_arb_share_counter_term_sysid_control_slave & ~sysid_control_slave_non_bursting_master_requests);

  //sysid_control_slave_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          sysid_control_slave_arb_share_counter <= 0;
      else if (sysid_control_slave_arb_counter_enable)
          sysid_control_slave_arb_share_counter <= sysid_control_slave_arb_share_counter_next_value;
    end


  //sysid_control_slave_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          sysid_control_slave_slavearbiterlockenable <= 0;
      else if ((|sysid_control_slave_master_qreq_vector & end_xfer_arb_share_counter_term_sysid_control_slave) | (end_xfer_arb_share_counter_term_sysid_control_slave & ~sysid_control_slave_non_bursting_master_requests))
          sysid_control_slave_slavearbiterlockenable <= |sysid_control_slave_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 sysid/control_slave arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = sysid_control_slave_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //sysid_control_slave_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign sysid_control_slave_slavearbiterlockenable2 = |sysid_control_slave_arb_share_counter_next_value;

  //pipeline_bridge/m1 sysid/control_slave arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = sysid_control_slave_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //sysid_control_slave_any_continuerequest at least one master continues requesting, which is an e_assign
  assign sysid_control_slave_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_sysid_control_slave = pipeline_bridge_m1_requests_sysid_control_slave & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((pipeline_bridge_m1_latency_counter != 0))));
  //local readdatavalid pipeline_bridge_m1_read_data_valid_sysid_control_slave, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_sysid_control_slave = pipeline_bridge_m1_granted_sysid_control_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~sysid_control_slave_waits_for_read;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_sysid_control_slave = pipeline_bridge_m1_qualified_request_sysid_control_slave;

  //pipeline_bridge/m1 saved-grant sysid/control_slave, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_sysid_control_slave = pipeline_bridge_m1_requests_sysid_control_slave;

  //allow new arb cycle for sysid/control_slave, which is an e_assign
  assign sysid_control_slave_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign sysid_control_slave_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign sysid_control_slave_master_qreq_vector = 1;

  //sysid_control_slave_firsttransfer first transaction, which is an e_assign
  assign sysid_control_slave_firsttransfer = sysid_control_slave_begins_xfer ? sysid_control_slave_unreg_firsttransfer : sysid_control_slave_reg_firsttransfer;

  //sysid_control_slave_unreg_firsttransfer first transaction, which is an e_assign
  assign sysid_control_slave_unreg_firsttransfer = ~(sysid_control_slave_slavearbiterlockenable & sysid_control_slave_any_continuerequest);

  //sysid_control_slave_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          sysid_control_slave_reg_firsttransfer <= 1'b1;
      else if (sysid_control_slave_begins_xfer)
          sysid_control_slave_reg_firsttransfer <= sysid_control_slave_unreg_firsttransfer;
    end


  //sysid_control_slave_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign sysid_control_slave_beginbursttransfer_internal = sysid_control_slave_begins_xfer;

  assign shifted_address_to_sysid_control_slave_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //sysid_control_slave_address mux, which is an e_mux
  assign sysid_control_slave_address = shifted_address_to_sysid_control_slave_from_pipeline_bridge_m1 >> 2;

  //d1_sysid_control_slave_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_sysid_control_slave_end_xfer <= 1;
      else 
        d1_sysid_control_slave_end_xfer <= sysid_control_slave_end_xfer;
    end


  //sysid_control_slave_waits_for_read in a cycle, which is an e_mux
  assign sysid_control_slave_waits_for_read = sysid_control_slave_in_a_read_cycle & sysid_control_slave_begins_xfer;

  //sysid_control_slave_in_a_read_cycle assignment, which is an e_assign
  assign sysid_control_slave_in_a_read_cycle = pipeline_bridge_m1_granted_sysid_control_slave & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = sysid_control_slave_in_a_read_cycle;

  //sysid_control_slave_waits_for_write in a cycle, which is an e_mux
  assign sysid_control_slave_waits_for_write = sysid_control_slave_in_a_write_cycle & 0;

  //sysid_control_slave_in_a_write_cycle assignment, which is an e_assign
  assign sysid_control_slave_in_a_write_cycle = pipeline_bridge_m1_granted_sysid_control_slave & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = sysid_control_slave_in_a_write_cycle;

  assign wait_for_sysid_control_slave_counter = 0;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //sysid/control_slave enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_sysid_control_slave && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave sysid/control_slave", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module timestamp_timer_s1_arbitrator (
                                       // inputs:
                                        clk,
                                        pipeline_bridge_m1_address_to_slave,
                                        pipeline_bridge_m1_burstcount,
                                        pipeline_bridge_m1_chipselect,
                                        pipeline_bridge_m1_latency_counter,
                                        pipeline_bridge_m1_read,
                                        pipeline_bridge_m1_write,
                                        pipeline_bridge_m1_writedata,
                                        reset_n,
                                        timestamp_timer_s1_irq,
                                        timestamp_timer_s1_readdata,

                                       // outputs:
                                        d1_timestamp_timer_s1_end_xfer,
                                        pipeline_bridge_m1_granted_timestamp_timer_s1,
                                        pipeline_bridge_m1_qualified_request_timestamp_timer_s1,
                                        pipeline_bridge_m1_read_data_valid_timestamp_timer_s1,
                                        pipeline_bridge_m1_requests_timestamp_timer_s1,
                                        timestamp_timer_s1_address,
                                        timestamp_timer_s1_chipselect,
                                        timestamp_timer_s1_irq_from_sa,
                                        timestamp_timer_s1_readdata_from_sa,
                                        timestamp_timer_s1_reset_n,
                                        timestamp_timer_s1_write_n,
                                        timestamp_timer_s1_writedata
                                     )
;

  output           d1_timestamp_timer_s1_end_xfer;
  output           pipeline_bridge_m1_granted_timestamp_timer_s1;
  output           pipeline_bridge_m1_qualified_request_timestamp_timer_s1;
  output           pipeline_bridge_m1_read_data_valid_timestamp_timer_s1;
  output           pipeline_bridge_m1_requests_timestamp_timer_s1;
  output  [  2: 0] timestamp_timer_s1_address;
  output           timestamp_timer_s1_chipselect;
  output           timestamp_timer_s1_irq_from_sa;
  output  [ 15: 0] timestamp_timer_s1_readdata_from_sa;
  output           timestamp_timer_s1_reset_n;
  output           timestamp_timer_s1_write_n;
  output  [ 15: 0] timestamp_timer_s1_writedata;
  input            clk;
  input   [ 11: 0] pipeline_bridge_m1_address_to_slave;
  input            pipeline_bridge_m1_burstcount;
  input            pipeline_bridge_m1_chipselect;
  input            pipeline_bridge_m1_latency_counter;
  input            pipeline_bridge_m1_read;
  input            pipeline_bridge_m1_write;
  input   [ 31: 0] pipeline_bridge_m1_writedata;
  input            reset_n;
  input            timestamp_timer_s1_irq;
  input   [ 15: 0] timestamp_timer_s1_readdata;

  reg              d1_reasons_to_wait;
  reg              d1_timestamp_timer_s1_end_xfer;
  reg              enable_nonzero_assertions;
  wire             end_xfer_arb_share_counter_term_timestamp_timer_s1;
  wire             in_a_read_cycle;
  wire             in_a_write_cycle;
  wire             pipeline_bridge_m1_arbiterlock;
  wire             pipeline_bridge_m1_arbiterlock2;
  wire             pipeline_bridge_m1_continuerequest;
  wire             pipeline_bridge_m1_granted_timestamp_timer_s1;
  wire             pipeline_bridge_m1_qualified_request_timestamp_timer_s1;
  wire             pipeline_bridge_m1_read_data_valid_timestamp_timer_s1;
  wire             pipeline_bridge_m1_requests_timestamp_timer_s1;
  wire             pipeline_bridge_m1_saved_grant_timestamp_timer_s1;
  wire    [ 11: 0] shifted_address_to_timestamp_timer_s1_from_pipeline_bridge_m1;
  wire    [  2: 0] timestamp_timer_s1_address;
  wire             timestamp_timer_s1_allgrants;
  wire             timestamp_timer_s1_allow_new_arb_cycle;
  wire             timestamp_timer_s1_any_bursting_master_saved_grant;
  wire             timestamp_timer_s1_any_continuerequest;
  wire             timestamp_timer_s1_arb_counter_enable;
  reg              timestamp_timer_s1_arb_share_counter;
  wire             timestamp_timer_s1_arb_share_counter_next_value;
  wire             timestamp_timer_s1_arb_share_set_values;
  wire             timestamp_timer_s1_beginbursttransfer_internal;
  wire             timestamp_timer_s1_begins_xfer;
  wire             timestamp_timer_s1_chipselect;
  wire             timestamp_timer_s1_end_xfer;
  wire             timestamp_timer_s1_firsttransfer;
  wire             timestamp_timer_s1_grant_vector;
  wire             timestamp_timer_s1_in_a_read_cycle;
  wire             timestamp_timer_s1_in_a_write_cycle;
  wire             timestamp_timer_s1_irq_from_sa;
  wire             timestamp_timer_s1_master_qreq_vector;
  wire             timestamp_timer_s1_non_bursting_master_requests;
  wire    [ 15: 0] timestamp_timer_s1_readdata_from_sa;
  reg              timestamp_timer_s1_reg_firsttransfer;
  wire             timestamp_timer_s1_reset_n;
  reg              timestamp_timer_s1_slavearbiterlockenable;
  wire             timestamp_timer_s1_slavearbiterlockenable2;
  wire             timestamp_timer_s1_unreg_firsttransfer;
  wire             timestamp_timer_s1_waits_for_read;
  wire             timestamp_timer_s1_waits_for_write;
  wire             timestamp_timer_s1_write_n;
  wire    [ 15: 0] timestamp_timer_s1_writedata;
  wire             wait_for_timestamp_timer_s1_counter;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_reasons_to_wait <= 0;
      else 
        d1_reasons_to_wait <= ~timestamp_timer_s1_end_xfer;
    end


  assign timestamp_timer_s1_begins_xfer = ~d1_reasons_to_wait & ((pipeline_bridge_m1_qualified_request_timestamp_timer_s1));
  //assign timestamp_timer_s1_readdata_from_sa = timestamp_timer_s1_readdata so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign timestamp_timer_s1_readdata_from_sa = timestamp_timer_s1_readdata;

  assign pipeline_bridge_m1_requests_timestamp_timer_s1 = ({pipeline_bridge_m1_address_to_slave[11 : 5] , 5'b0} == 12'h800) & pipeline_bridge_m1_chipselect;
  //timestamp_timer_s1_arb_share_counter set values, which is an e_mux
  assign timestamp_timer_s1_arb_share_set_values = 1;

  //timestamp_timer_s1_non_bursting_master_requests mux, which is an e_mux
  assign timestamp_timer_s1_non_bursting_master_requests = pipeline_bridge_m1_requests_timestamp_timer_s1;

  //timestamp_timer_s1_any_bursting_master_saved_grant mux, which is an e_mux
  assign timestamp_timer_s1_any_bursting_master_saved_grant = 0;

  //timestamp_timer_s1_arb_share_counter_next_value assignment, which is an e_assign
  assign timestamp_timer_s1_arb_share_counter_next_value = timestamp_timer_s1_firsttransfer ? (timestamp_timer_s1_arb_share_set_values - 1) : |timestamp_timer_s1_arb_share_counter ? (timestamp_timer_s1_arb_share_counter - 1) : 0;

  //timestamp_timer_s1_allgrants all slave grants, which is an e_mux
  assign timestamp_timer_s1_allgrants = |timestamp_timer_s1_grant_vector;

  //timestamp_timer_s1_end_xfer assignment, which is an e_assign
  assign timestamp_timer_s1_end_xfer = ~(timestamp_timer_s1_waits_for_read | timestamp_timer_s1_waits_for_write);

  //end_xfer_arb_share_counter_term_timestamp_timer_s1 arb share counter enable term, which is an e_assign
  assign end_xfer_arb_share_counter_term_timestamp_timer_s1 = timestamp_timer_s1_end_xfer & (~timestamp_timer_s1_any_bursting_master_saved_grant | in_a_read_cycle | in_a_write_cycle);

  //timestamp_timer_s1_arb_share_counter arbitration counter enable, which is an e_assign
  assign timestamp_timer_s1_arb_counter_enable = (end_xfer_arb_share_counter_term_timestamp_timer_s1 & timestamp_timer_s1_allgrants) | (end_xfer_arb_share_counter_term_timestamp_timer_s1 & ~timestamp_timer_s1_non_bursting_master_requests);

  //timestamp_timer_s1_arb_share_counter counter, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          timestamp_timer_s1_arb_share_counter <= 0;
      else if (timestamp_timer_s1_arb_counter_enable)
          timestamp_timer_s1_arb_share_counter <= timestamp_timer_s1_arb_share_counter_next_value;
    end


  //timestamp_timer_s1_slavearbiterlockenable slave enables arbiterlock, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          timestamp_timer_s1_slavearbiterlockenable <= 0;
      else if ((|timestamp_timer_s1_master_qreq_vector & end_xfer_arb_share_counter_term_timestamp_timer_s1) | (end_xfer_arb_share_counter_term_timestamp_timer_s1 & ~timestamp_timer_s1_non_bursting_master_requests))
          timestamp_timer_s1_slavearbiterlockenable <= |timestamp_timer_s1_arb_share_counter_next_value;
    end


  //pipeline_bridge/m1 timestamp_timer/s1 arbiterlock, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock = timestamp_timer_s1_slavearbiterlockenable & pipeline_bridge_m1_continuerequest;

  //timestamp_timer_s1_slavearbiterlockenable2 slave enables arbiterlock2, which is an e_assign
  assign timestamp_timer_s1_slavearbiterlockenable2 = |timestamp_timer_s1_arb_share_counter_next_value;

  //pipeline_bridge/m1 timestamp_timer/s1 arbiterlock2, which is an e_assign
  assign pipeline_bridge_m1_arbiterlock2 = timestamp_timer_s1_slavearbiterlockenable2 & pipeline_bridge_m1_continuerequest;

  //timestamp_timer_s1_any_continuerequest at least one master continues requesting, which is an e_assign
  assign timestamp_timer_s1_any_continuerequest = 1;

  //pipeline_bridge_m1_continuerequest continued request, which is an e_assign
  assign pipeline_bridge_m1_continuerequest = 1;

  assign pipeline_bridge_m1_qualified_request_timestamp_timer_s1 = pipeline_bridge_m1_requests_timestamp_timer_s1 & ~(((pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ((pipeline_bridge_m1_latency_counter != 0))));
  //local readdatavalid pipeline_bridge_m1_read_data_valid_timestamp_timer_s1, which is an e_mux
  assign pipeline_bridge_m1_read_data_valid_timestamp_timer_s1 = pipeline_bridge_m1_granted_timestamp_timer_s1 & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect) & ~timestamp_timer_s1_waits_for_read;

  //timestamp_timer_s1_writedata mux, which is an e_mux
  assign timestamp_timer_s1_writedata = pipeline_bridge_m1_writedata;

  //master is always granted when requested
  assign pipeline_bridge_m1_granted_timestamp_timer_s1 = pipeline_bridge_m1_qualified_request_timestamp_timer_s1;

  //pipeline_bridge/m1 saved-grant timestamp_timer/s1, which is an e_assign
  assign pipeline_bridge_m1_saved_grant_timestamp_timer_s1 = pipeline_bridge_m1_requests_timestamp_timer_s1;

  //allow new arb cycle for timestamp_timer/s1, which is an e_assign
  assign timestamp_timer_s1_allow_new_arb_cycle = 1;

  //placeholder chosen master
  assign timestamp_timer_s1_grant_vector = 1;

  //placeholder vector of master qualified-requests
  assign timestamp_timer_s1_master_qreq_vector = 1;

  //timestamp_timer_s1_reset_n assignment, which is an e_assign
  assign timestamp_timer_s1_reset_n = reset_n;

  assign timestamp_timer_s1_chipselect = pipeline_bridge_m1_granted_timestamp_timer_s1;
  //timestamp_timer_s1_firsttransfer first transaction, which is an e_assign
  assign timestamp_timer_s1_firsttransfer = timestamp_timer_s1_begins_xfer ? timestamp_timer_s1_unreg_firsttransfer : timestamp_timer_s1_reg_firsttransfer;

  //timestamp_timer_s1_unreg_firsttransfer first transaction, which is an e_assign
  assign timestamp_timer_s1_unreg_firsttransfer = ~(timestamp_timer_s1_slavearbiterlockenable & timestamp_timer_s1_any_continuerequest);

  //timestamp_timer_s1_reg_firsttransfer first transaction, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          timestamp_timer_s1_reg_firsttransfer <= 1'b1;
      else if (timestamp_timer_s1_begins_xfer)
          timestamp_timer_s1_reg_firsttransfer <= timestamp_timer_s1_unreg_firsttransfer;
    end


  //timestamp_timer_s1_beginbursttransfer_internal begin burst transfer, which is an e_assign
  assign timestamp_timer_s1_beginbursttransfer_internal = timestamp_timer_s1_begins_xfer;

  //~timestamp_timer_s1_write_n assignment, which is an e_mux
  assign timestamp_timer_s1_write_n = ~(pipeline_bridge_m1_granted_timestamp_timer_s1 & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect));

  assign shifted_address_to_timestamp_timer_s1_from_pipeline_bridge_m1 = pipeline_bridge_m1_address_to_slave;
  //timestamp_timer_s1_address mux, which is an e_mux
  assign timestamp_timer_s1_address = shifted_address_to_timestamp_timer_s1_from_pipeline_bridge_m1 >> 2;

  //d1_timestamp_timer_s1_end_xfer register, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          d1_timestamp_timer_s1_end_xfer <= 1;
      else 
        d1_timestamp_timer_s1_end_xfer <= timestamp_timer_s1_end_xfer;
    end


  //timestamp_timer_s1_waits_for_read in a cycle, which is an e_mux
  assign timestamp_timer_s1_waits_for_read = timestamp_timer_s1_in_a_read_cycle & timestamp_timer_s1_begins_xfer;

  //timestamp_timer_s1_in_a_read_cycle assignment, which is an e_assign
  assign timestamp_timer_s1_in_a_read_cycle = pipeline_bridge_m1_granted_timestamp_timer_s1 & (pipeline_bridge_m1_read & pipeline_bridge_m1_chipselect);

  //in_a_read_cycle assignment, which is an e_mux
  assign in_a_read_cycle = timestamp_timer_s1_in_a_read_cycle;

  //timestamp_timer_s1_waits_for_write in a cycle, which is an e_mux
  assign timestamp_timer_s1_waits_for_write = timestamp_timer_s1_in_a_write_cycle & 0;

  //timestamp_timer_s1_in_a_write_cycle assignment, which is an e_assign
  assign timestamp_timer_s1_in_a_write_cycle = pipeline_bridge_m1_granted_timestamp_timer_s1 & (pipeline_bridge_m1_write & pipeline_bridge_m1_chipselect);

  //in_a_write_cycle assignment, which is an e_mux
  assign in_a_write_cycle = timestamp_timer_s1_in_a_write_cycle;

  assign wait_for_timestamp_timer_s1_counter = 0;
  //assign timestamp_timer_s1_irq_from_sa = timestamp_timer_s1_irq so that symbol knows where to group signals which may go to master only, which is an e_assign
  assign timestamp_timer_s1_irq_from_sa = timestamp_timer_s1_irq;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  //timestamp_timer/s1 enable non-zero assertions, which is an e_register
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          enable_nonzero_assertions <= 0;
      else 
        enable_nonzero_assertions <= 1'b1;
    end


  //pipeline_bridge/m1 non-zero burstcount assertion, which is an e_process
  always @(posedge clk)
    begin
      if (pipeline_bridge_m1_requests_timestamp_timer_s1 && (pipeline_bridge_m1_burstcount == 0) && enable_nonzero_assertions)
        begin
          $write("%0d ns: pipeline_bridge/m1 drove 0 on its 'burstcount' port while accessing slave timestamp_timer/s1", $time);
          $stop;
        end
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_reset_system_clk_domain_synch_module (
                                                         // inputs:
                                                          clk,
                                                          data_in,
                                                          reset_n,

                                                         // outputs:
                                                          data_out
                                                       )
;

  output           data_out;
  input            clk;
  input            data_in;
  input            reset_n;

  reg              data_in_d1 /* synthesis ALTERA_ATTRIBUTE = "{-from \"*\"} CUT=ON ; PRESERVE_REGISTER=ON ; SUPPRESS_DA_RULE_INTERNAL=R101"  */;
  reg              data_out /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON ; SUPPRESS_DA_RULE_INTERNAL=R101"  */;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          data_in_d1 <= 0;
      else 
        data_in_d1 <= data_in;
    end


  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          data_out <= 0;
      else 
        data_out <= data_in_d1;
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_reset_external_clk_domain_synch_module (
                                                           // inputs:
                                                            clk,
                                                            data_in,
                                                            reset_n,

                                                           // outputs:
                                                            data_out
                                                         )
;

  output           data_out;
  input            clk;
  input            data_in;
  input            reset_n;

  reg              data_in_d1 /* synthesis ALTERA_ATTRIBUTE = "{-from \"*\"} CUT=ON ; PRESERVE_REGISTER=ON ; SUPPRESS_DA_RULE_INTERNAL=R101"  */;
  reg              data_out /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON ; SUPPRESS_DA_RULE_INTERNAL=R101"  */;
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          data_in_d1 <= 0;
      else 
        data_in_d1 <= data_in;
    end


  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          data_out <= 0;
      else 
        data_out <= data_in_d1;
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma (
                    // 1) global signals:
                     external_clk,
                     reset_n,
                     sdram_write_clk,
                     ssram_clk,
                     system_clk,

                    // the_ddr_sdram
                     clk_to_sdram_from_the_ddr_sdram,
                     clk_to_sdram_n_from_the_ddr_sdram,
                     ddr_a_from_the_ddr_sdram,
                     ddr_ba_from_the_ddr_sdram,
                     ddr_cas_n_from_the_ddr_sdram,
                     ddr_cke_from_the_ddr_sdram,
                     ddr_cs_n_from_the_ddr_sdram,
                     ddr_dm_from_the_ddr_sdram,
                     ddr_dq_to_and_from_the_ddr_sdram,
                     ddr_dqs_to_and_from_the_ddr_sdram,
                     ddr_ras_n_from_the_ddr_sdram,
                     ddr_we_n_from_the_ddr_sdram,
                     dqs_delay_ctrl_to_the_ddr_sdram,
                     dqsupdate_to_the_ddr_sdram,
                     stratix_dll_control_from_the_ddr_sdram,
                     write_clk_to_the_ddr_sdram,

                    // the_ext_ssram_bus_avalon_slave
                     adsc_n_to_the_ext_ssram,
                     bw_n_to_the_ext_ssram,
                     bwe_n_to_the_ext_ssram,
                     chipenable1_n_to_the_ext_ssram,
                     ext_ssram_bus_address,
                     ext_ssram_bus_data,
                     outputenable_n_to_the_ext_ssram
                  )
;

  output           adsc_n_to_the_ext_ssram;
  output  [  3: 0] bw_n_to_the_ext_ssram;
  output           bwe_n_to_the_ext_ssram;
  output           chipenable1_n_to_the_ext_ssram;
  output           clk_to_sdram_from_the_ddr_sdram;
  output           clk_to_sdram_n_from_the_ddr_sdram;
  output  [ 12: 0] ddr_a_from_the_ddr_sdram;
  output  [  1: 0] ddr_ba_from_the_ddr_sdram;
  output           ddr_cas_n_from_the_ddr_sdram;
  output           ddr_cke_from_the_ddr_sdram;
  output           ddr_cs_n_from_the_ddr_sdram;
  output  [  1: 0] ddr_dm_from_the_ddr_sdram;
  inout   [ 15: 0] ddr_dq_to_and_from_the_ddr_sdram;
  inout   [  1: 0] ddr_dqs_to_and_from_the_ddr_sdram;
  output           ddr_ras_n_from_the_ddr_sdram;
  output           ddr_we_n_from_the_ddr_sdram;
  output  [ 20: 0] ext_ssram_bus_address;
  inout   [ 31: 0] ext_ssram_bus_data;
  output           outputenable_n_to_the_ext_ssram;
  output           sdram_write_clk;
  output           ssram_clk;
  output           stratix_dll_control_from_the_ddr_sdram;
  output           system_clk;
  input   [  5: 0] dqs_delay_ctrl_to_the_ddr_sdram;
  input            dqsupdate_to_the_ddr_sdram;
  input            external_clk;
  input            reset_n;
  input            write_clk_to_the_ddr_sdram;

  wire             adsc_n_to_the_ext_ssram;
  wire    [  3: 0] bw_n_to_the_ext_ssram;
  wire             bwe_n_to_the_ext_ssram;
  wire             chipenable1_n_to_the_ext_ssram;
  wire             clk_to_sdram_from_the_ddr_sdram;
  wire             clk_to_sdram_n_from_the_ddr_sdram;
  wire    [ 26: 0] cpu_data_master_address;
  wire    [ 26: 0] cpu_data_master_address_to_slave;
  wire    [  3: 0] cpu_data_master_burstcount;
  wire    [  3: 0] cpu_data_master_byteenable;
  wire             cpu_data_master_debugaccess;
  wire             cpu_data_master_granted_custom_dma_burst_0_upstream;
  wire             cpu_data_master_granted_custom_dma_burst_2_upstream;
  wire             cpu_data_master_granted_custom_dma_burst_4_upstream;
  wire    [ 31: 0] cpu_data_master_irq;
  wire             cpu_data_master_latency_counter;
  wire             cpu_data_master_qualified_request_custom_dma_burst_0_upstream;
  wire             cpu_data_master_qualified_request_custom_dma_burst_2_upstream;
  wire             cpu_data_master_qualified_request_custom_dma_burst_4_upstream;
  wire             cpu_data_master_read;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_0_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_2_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_4_upstream;
  wire             cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register;
  wire    [ 31: 0] cpu_data_master_readdata;
  wire             cpu_data_master_readdatavalid;
  wire             cpu_data_master_requests_custom_dma_burst_0_upstream;
  wire             cpu_data_master_requests_custom_dma_burst_2_upstream;
  wire             cpu_data_master_requests_custom_dma_burst_4_upstream;
  wire             cpu_data_master_waitrequest;
  wire             cpu_data_master_write;
  wire    [ 31: 0] cpu_data_master_writedata;
  wire    [ 26: 0] cpu_instruction_master_address;
  wire    [ 26: 0] cpu_instruction_master_address_to_slave;
  wire    [  3: 0] cpu_instruction_master_burstcount;
  wire             cpu_instruction_master_granted_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_granted_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_latency_counter;
  wire             cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_read;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register;
  wire    [ 31: 0] cpu_instruction_master_readdata;
  wire             cpu_instruction_master_readdatavalid;
  wire             cpu_instruction_master_requests_custom_dma_burst_1_upstream;
  wire             cpu_instruction_master_requests_custom_dma_burst_3_upstream;
  wire             cpu_instruction_master_waitrequest;
  wire    [  8: 0] cpu_jtag_debug_module_address;
  wire             cpu_jtag_debug_module_begintransfer;
  wire    [  3: 0] cpu_jtag_debug_module_byteenable;
  wire             cpu_jtag_debug_module_chipselect;
  wire             cpu_jtag_debug_module_debugaccess;
  wire    [ 31: 0] cpu_jtag_debug_module_readdata;
  wire    [ 31: 0] cpu_jtag_debug_module_readdata_from_sa;
  wire             cpu_jtag_debug_module_reset_n;
  wire             cpu_jtag_debug_module_resetrequest;
  wire             cpu_jtag_debug_module_resetrequest_from_sa;
  wire             cpu_jtag_debug_module_write;
  wire    [ 31: 0] cpu_jtag_debug_module_writedata;
  wire    [ 20: 0] custom_dma_burst_0_downstream_address;
  wire    [ 20: 0] custom_dma_burst_0_downstream_address_to_slave;
  wire    [  3: 0] custom_dma_burst_0_downstream_arbitrationshare;
  wire             custom_dma_burst_0_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_0_downstream_byteenable;
  wire             custom_dma_burst_0_downstream_debugaccess;
  wire             custom_dma_burst_0_downstream_granted_ext_ssram_s1;
  wire    [  2: 0] custom_dma_burst_0_downstream_latency_counter;
  wire    [ 20: 0] custom_dma_burst_0_downstream_nativeaddress;
  wire             custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1;
  wire             custom_dma_burst_0_downstream_read;
  wire             custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1;
  wire    [ 31: 0] custom_dma_burst_0_downstream_readdata;
  wire             custom_dma_burst_0_downstream_readdatavalid;
  wire             custom_dma_burst_0_downstream_requests_ext_ssram_s1;
  wire             custom_dma_burst_0_downstream_reset_n;
  wire             custom_dma_burst_0_downstream_waitrequest;
  wire             custom_dma_burst_0_downstream_write;
  wire    [ 31: 0] custom_dma_burst_0_downstream_writedata;
  wire    [ 20: 0] custom_dma_burst_0_upstream_address;
  wire    [  3: 0] custom_dma_burst_0_upstream_burstcount;
  wire    [ 22: 0] custom_dma_burst_0_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_0_upstream_byteenable;
  wire             custom_dma_burst_0_upstream_debugaccess;
  wire             custom_dma_burst_0_upstream_read;
  wire    [ 31: 0] custom_dma_burst_0_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_0_upstream_readdata_from_sa;
  wire             custom_dma_burst_0_upstream_readdatavalid;
  wire             custom_dma_burst_0_upstream_waitrequest;
  wire             custom_dma_burst_0_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_0_upstream_write;
  wire    [ 31: 0] custom_dma_burst_0_upstream_writedata;
  wire    [ 11: 0] custom_dma_burst_1_downstream_address;
  wire    [ 11: 0] custom_dma_burst_1_downstream_address_to_slave;
  wire    [  3: 0] custom_dma_burst_1_downstream_arbitrationshare;
  wire             custom_dma_burst_1_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_1_downstream_byteenable;
  wire             custom_dma_burst_1_downstream_debugaccess;
  wire             custom_dma_burst_1_downstream_granted_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_latency_counter;
  wire    [ 11: 0] custom_dma_burst_1_downstream_nativeaddress;
  wire             custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_read;
  wire             custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  wire    [ 31: 0] custom_dma_burst_1_downstream_readdata;
  wire             custom_dma_burst_1_downstream_readdatavalid;
  wire             custom_dma_burst_1_downstream_requests_pipeline_bridge_s1;
  wire             custom_dma_burst_1_downstream_reset_n;
  wire             custom_dma_burst_1_downstream_waitrequest;
  wire             custom_dma_burst_1_downstream_write;
  wire    [ 31: 0] custom_dma_burst_1_downstream_writedata;
  wire    [ 11: 0] custom_dma_burst_1_upstream_address;
  wire    [ 13: 0] custom_dma_burst_1_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_1_upstream_byteenable;
  wire             custom_dma_burst_1_upstream_debugaccess;
  wire             custom_dma_burst_1_upstream_read;
  wire    [ 31: 0] custom_dma_burst_1_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_1_upstream_readdata_from_sa;
  wire             custom_dma_burst_1_upstream_readdatavalid;
  wire             custom_dma_burst_1_upstream_waitrequest;
  wire             custom_dma_burst_1_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_1_upstream_write;
  wire    [ 31: 0] custom_dma_burst_1_upstream_writedata;
  wire    [ 11: 0] custom_dma_burst_2_downstream_address;
  wire    [ 11: 0] custom_dma_burst_2_downstream_address_to_slave;
  wire    [  3: 0] custom_dma_burst_2_downstream_arbitrationshare;
  wire             custom_dma_burst_2_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_2_downstream_byteenable;
  wire             custom_dma_burst_2_downstream_debugaccess;
  wire             custom_dma_burst_2_downstream_granted_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_latency_counter;
  wire    [ 11: 0] custom_dma_burst_2_downstream_nativeaddress;
  wire             custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_read;
  wire             custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register;
  wire    [ 31: 0] custom_dma_burst_2_downstream_readdata;
  wire             custom_dma_burst_2_downstream_readdatavalid;
  wire             custom_dma_burst_2_downstream_requests_pipeline_bridge_s1;
  wire             custom_dma_burst_2_downstream_reset_n;
  wire             custom_dma_burst_2_downstream_waitrequest;
  wire             custom_dma_burst_2_downstream_write;
  wire    [ 31: 0] custom_dma_burst_2_downstream_writedata;
  wire    [ 11: 0] custom_dma_burst_2_upstream_address;
  wire    [  3: 0] custom_dma_burst_2_upstream_burstcount;
  wire    [ 13: 0] custom_dma_burst_2_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_2_upstream_byteenable;
  wire             custom_dma_burst_2_upstream_debugaccess;
  wire             custom_dma_burst_2_upstream_read;
  wire    [ 31: 0] custom_dma_burst_2_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_2_upstream_readdata_from_sa;
  wire             custom_dma_burst_2_upstream_readdatavalid;
  wire             custom_dma_burst_2_upstream_waitrequest;
  wire             custom_dma_burst_2_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_2_upstream_write;
  wire    [ 31: 0] custom_dma_burst_2_upstream_writedata;
  wire    [ 24: 0] custom_dma_burst_3_downstream_address;
  wire    [ 24: 0] custom_dma_burst_3_downstream_address_to_slave;
  wire    [  3: 0] custom_dma_burst_3_downstream_arbitrationshare;
  wire    [  2: 0] custom_dma_burst_3_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_3_downstream_byteenable;
  wire             custom_dma_burst_3_downstream_debugaccess;
  wire             custom_dma_burst_3_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_latency_counter;
  wire    [ 24: 0] custom_dma_burst_3_downstream_nativeaddress;
  wire             custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_read;
  wire             custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire    [ 31: 0] custom_dma_burst_3_downstream_readdata;
  wire             custom_dma_burst_3_downstream_readdatavalid;
  wire             custom_dma_burst_3_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_3_downstream_reset_n;
  wire             custom_dma_burst_3_downstream_waitrequest;
  wire             custom_dma_burst_3_downstream_write;
  wire    [ 31: 0] custom_dma_burst_3_downstream_writedata;
  wire    [ 24: 0] custom_dma_burst_3_upstream_address;
  wire    [ 26: 0] custom_dma_burst_3_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_3_upstream_byteenable;
  wire             custom_dma_burst_3_upstream_debugaccess;
  wire             custom_dma_burst_3_upstream_read;
  wire    [ 31: 0] custom_dma_burst_3_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_3_upstream_readdata_from_sa;
  wire             custom_dma_burst_3_upstream_readdatavalid;
  wire             custom_dma_burst_3_upstream_waitrequest;
  wire             custom_dma_burst_3_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_3_upstream_write;
  wire    [ 31: 0] custom_dma_burst_3_upstream_writedata;
  wire    [ 24: 0] custom_dma_burst_4_downstream_address;
  wire    [ 24: 0] custom_dma_burst_4_downstream_address_to_slave;
  wire    [  3: 0] custom_dma_burst_4_downstream_arbitrationshare;
  wire    [  2: 0] custom_dma_burst_4_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_4_downstream_byteenable;
  wire             custom_dma_burst_4_downstream_debugaccess;
  wire             custom_dma_burst_4_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_latency_counter;
  wire    [ 24: 0] custom_dma_burst_4_downstream_nativeaddress;
  wire             custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_read;
  wire             custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire    [ 31: 0] custom_dma_burst_4_downstream_readdata;
  wire             custom_dma_burst_4_downstream_readdatavalid;
  wire             custom_dma_burst_4_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_4_downstream_reset_n;
  wire             custom_dma_burst_4_downstream_waitrequest;
  wire             custom_dma_burst_4_downstream_write;
  wire    [ 31: 0] custom_dma_burst_4_downstream_writedata;
  wire    [ 24: 0] custom_dma_burst_4_upstream_address;
  wire    [  3: 0] custom_dma_burst_4_upstream_burstcount;
  wire    [ 26: 0] custom_dma_burst_4_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_4_upstream_byteenable;
  wire             custom_dma_burst_4_upstream_debugaccess;
  wire             custom_dma_burst_4_upstream_read;
  wire    [ 31: 0] custom_dma_burst_4_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_4_upstream_readdata_from_sa;
  wire             custom_dma_burst_4_upstream_readdatavalid;
  wire             custom_dma_burst_4_upstream_waitrequest;
  wire             custom_dma_burst_4_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_4_upstream_write;
  wire    [ 31: 0] custom_dma_burst_4_upstream_writedata;
  wire    [ 24: 0] custom_dma_burst_5_downstream_address;
  wire    [ 24: 0] custom_dma_burst_5_downstream_address_to_slave;
  wire    [  2: 0] custom_dma_burst_5_downstream_arbitrationshare;
  wire    [  2: 0] custom_dma_burst_5_downstream_burstcount;
  wire    [  3: 0] custom_dma_burst_5_downstream_byteenable;
  wire             custom_dma_burst_5_downstream_debugaccess;
  wire             custom_dma_burst_5_downstream_granted_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_latency_counter;
  wire    [ 24: 0] custom_dma_burst_5_downstream_nativeaddress;
  wire             custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_read;
  wire             custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register;
  wire    [ 31: 0] custom_dma_burst_5_downstream_readdata;
  wire             custom_dma_burst_5_downstream_readdatavalid;
  wire             custom_dma_burst_5_downstream_requests_ddr_sdram_s1;
  wire             custom_dma_burst_5_downstream_reset_n;
  wire             custom_dma_burst_5_downstream_waitrequest;
  wire             custom_dma_burst_5_downstream_write;
  wire    [ 31: 0] custom_dma_burst_5_downstream_writedata;
  wire    [ 24: 0] custom_dma_burst_5_upstream_address;
  wire    [  2: 0] custom_dma_burst_5_upstream_burstcount;
  wire    [ 26: 0] custom_dma_burst_5_upstream_byteaddress;
  wire    [  3: 0] custom_dma_burst_5_upstream_byteenable;
  wire             custom_dma_burst_5_upstream_debugaccess;
  wire             custom_dma_burst_5_upstream_read;
  wire    [ 31: 0] custom_dma_burst_5_upstream_readdata;
  wire    [ 31: 0] custom_dma_burst_5_upstream_readdata_from_sa;
  wire             custom_dma_burst_5_upstream_readdatavalid;
  wire             custom_dma_burst_5_upstream_readdatavalid_from_sa;
  wire             custom_dma_burst_5_upstream_waitrequest;
  wire             custom_dma_burst_5_upstream_waitrequest_from_sa;
  wire             custom_dma_burst_5_upstream_write;
  wire    [ 31: 0] custom_dma_burst_5_upstream_writedata;
  wire    [  3: 0] custom_dma_clock_0_in_address;
  wire    [  1: 0] custom_dma_clock_0_in_byteenable;
  wire             custom_dma_clock_0_in_endofpacket;
  wire             custom_dma_clock_0_in_endofpacket_from_sa;
  wire    [  2: 0] custom_dma_clock_0_in_nativeaddress;
  wire             custom_dma_clock_0_in_read;
  wire    [ 15: 0] custom_dma_clock_0_in_readdata;
  wire    [ 15: 0] custom_dma_clock_0_in_readdata_from_sa;
  wire             custom_dma_clock_0_in_reset_n;
  wire             custom_dma_clock_0_in_waitrequest;
  wire             custom_dma_clock_0_in_waitrequest_from_sa;
  wire             custom_dma_clock_0_in_write;
  wire    [ 15: 0] custom_dma_clock_0_in_writedata;
  wire    [  3: 0] custom_dma_clock_0_out_address;
  wire    [  3: 0] custom_dma_clock_0_out_address_to_slave;
  wire    [  1: 0] custom_dma_clock_0_out_byteenable;
  wire             custom_dma_clock_0_out_endofpacket;
  wire             custom_dma_clock_0_out_granted_pll_s1;
  wire    [  2: 0] custom_dma_clock_0_out_nativeaddress;
  wire             custom_dma_clock_0_out_qualified_request_pll_s1;
  wire             custom_dma_clock_0_out_read;
  wire             custom_dma_clock_0_out_read_data_valid_pll_s1;
  wire    [ 15: 0] custom_dma_clock_0_out_readdata;
  wire             custom_dma_clock_0_out_requests_pll_s1;
  wire             custom_dma_clock_0_out_reset_n;
  wire             custom_dma_clock_0_out_waitrequest;
  wire             custom_dma_clock_0_out_write;
  wire    [ 15: 0] custom_dma_clock_0_out_writedata;
  wire             d1_cpu_jtag_debug_module_end_xfer;
  wire             d1_custom_dma_burst_0_upstream_end_xfer;
  wire             d1_custom_dma_burst_1_upstream_end_xfer;
  wire             d1_custom_dma_burst_2_upstream_end_xfer;
  wire             d1_custom_dma_burst_3_upstream_end_xfer;
  wire             d1_custom_dma_burst_4_upstream_end_xfer;
  wire             d1_custom_dma_burst_5_upstream_end_xfer;
  wire             d1_custom_dma_clock_0_in_end_xfer;
  wire             d1_ddr_sdram_s1_end_xfer;
  wire             d1_ext_ssram_bus_avalon_slave_end_xfer;
  wire             d1_fir_dma_control_end_xfer;
  wire             d1_jtag_uart_avalon_jtag_slave_end_xfer;
  wire             d1_pipeline_bridge_s1_end_xfer;
  wire             d1_pll_s1_end_xfer;
  wire             d1_sysid_control_slave_end_xfer;
  wire             d1_timestamp_timer_s1_end_xfer;
  wire    [ 12: 0] ddr_a_from_the_ddr_sdram;
  wire    [  1: 0] ddr_ba_from_the_ddr_sdram;
  wire             ddr_cas_n_from_the_ddr_sdram;
  wire             ddr_cke_from_the_ddr_sdram;
  wire             ddr_cs_n_from_the_ddr_sdram;
  wire    [  1: 0] ddr_dm_from_the_ddr_sdram;
  wire    [ 15: 0] ddr_dq_to_and_from_the_ddr_sdram;
  wire    [  1: 0] ddr_dqs_to_and_from_the_ddr_sdram;
  wire             ddr_ras_n_from_the_ddr_sdram;
  wire    [ 22: 0] ddr_sdram_s1_address;
  wire             ddr_sdram_s1_beginbursttransfer;
  wire    [  2: 0] ddr_sdram_s1_burstcount;
  wire    [  3: 0] ddr_sdram_s1_byteenable;
  wire             ddr_sdram_s1_read;
  wire    [ 31: 0] ddr_sdram_s1_readdata;
  wire    [ 31: 0] ddr_sdram_s1_readdata_from_sa;
  wire             ddr_sdram_s1_readdatavalid;
  wire             ddr_sdram_s1_reset_n;
  wire             ddr_sdram_s1_waitrequest_n;
  wire             ddr_sdram_s1_waitrequest_n_from_sa;
  wire             ddr_sdram_s1_write;
  wire    [ 31: 0] ddr_sdram_s1_writedata;
  wire             ddr_we_n_from_the_ddr_sdram;
  wire    [ 20: 0] ext_ssram_bus_address;
  wire    [ 31: 0] ext_ssram_bus_data;
  wire             external_clk_reset_n;
  wire    [  2: 0] fir_dma_control_address;
  wire    [  3: 0] fir_dma_control_byteenable;
  wire             fir_dma_control_irq;
  wire             fir_dma_control_irq_from_sa;
  wire             fir_dma_control_read;
  wire    [ 31: 0] fir_dma_control_readdata;
  wire    [ 31: 0] fir_dma_control_readdata_from_sa;
  wire             fir_dma_control_reset;
  wire             fir_dma_control_write;
  wire    [ 31: 0] fir_dma_control_writedata;
  wire    [ 31: 0] fir_dma_read_master_address;
  wire    [ 31: 0] fir_dma_read_master_address_to_slave;
  wire    [  3: 0] fir_dma_read_master_byteenable;
  wire             fir_dma_read_master_granted_ext_ssram_s1;
  wire    [  2: 0] fir_dma_read_master_latency_counter;
  wire             fir_dma_read_master_qualified_request_ext_ssram_s1;
  wire             fir_dma_read_master_read;
  wire             fir_dma_read_master_read_data_valid_ext_ssram_s1;
  wire    [ 31: 0] fir_dma_read_master_readdata;
  wire             fir_dma_read_master_readdatavalid;
  wire             fir_dma_read_master_requests_ext_ssram_s1;
  wire             fir_dma_read_master_waitrequest;
  wire    [ 31: 0] fir_dma_write_master_address;
  wire    [ 31: 0] fir_dma_write_master_address_to_slave;
  wire    [  2: 0] fir_dma_write_master_burstcount;
  wire    [  3: 0] fir_dma_write_master_byteenable;
  wire             fir_dma_write_master_granted_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_requests_custom_dma_burst_5_upstream;
  wire             fir_dma_write_master_waitrequest;
  wire             fir_dma_write_master_write;
  wire    [ 31: 0] fir_dma_write_master_writedata;
  wire    [ 31: 0] incoming_ext_ssram_bus_data;
  wire             jtag_uart_avalon_jtag_slave_address;
  wire             jtag_uart_avalon_jtag_slave_chipselect;
  wire             jtag_uart_avalon_jtag_slave_dataavailable;
  wire             jtag_uart_avalon_jtag_slave_dataavailable_from_sa;
  wire             jtag_uart_avalon_jtag_slave_irq;
  wire             jtag_uart_avalon_jtag_slave_irq_from_sa;
  wire             jtag_uart_avalon_jtag_slave_read_n;
  wire    [ 31: 0] jtag_uart_avalon_jtag_slave_readdata;
  wire    [ 31: 0] jtag_uart_avalon_jtag_slave_readdata_from_sa;
  wire             jtag_uart_avalon_jtag_slave_readyfordata;
  wire             jtag_uart_avalon_jtag_slave_readyfordata_from_sa;
  wire             jtag_uart_avalon_jtag_slave_reset_n;
  wire             jtag_uart_avalon_jtag_slave_waitrequest;
  wire             jtag_uart_avalon_jtag_slave_waitrequest_from_sa;
  wire             jtag_uart_avalon_jtag_slave_write_n;
  wire    [ 31: 0] jtag_uart_avalon_jtag_slave_writedata;
  wire             out_clk_pll_c0;
  wire             out_clk_pll_c1;
  wire             out_clk_pll_c2;
  wire             outputenable_n_to_the_ext_ssram;
  wire    [ 11: 0] pipeline_bridge_m1_address;
  wire    [ 11: 0] pipeline_bridge_m1_address_to_slave;
  wire             pipeline_bridge_m1_burstcount;
  wire    [  3: 0] pipeline_bridge_m1_byteenable;
  wire             pipeline_bridge_m1_chipselect;
  wire             pipeline_bridge_m1_debugaccess;
  wire             pipeline_bridge_m1_endofpacket;
  wire             pipeline_bridge_m1_granted_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_granted_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_granted_fir_dma_control;
  wire             pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_granted_sysid_control_slave;
  wire             pipeline_bridge_m1_granted_timestamp_timer_s1;
  wire             pipeline_bridge_m1_latency_counter;
  wire             pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_qualified_request_fir_dma_control;
  wire             pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_qualified_request_sysid_control_slave;
  wire             pipeline_bridge_m1_qualified_request_timestamp_timer_s1;
  wire             pipeline_bridge_m1_read;
  wire             pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_read_data_valid_fir_dma_control;
  wire             pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_read_data_valid_sysid_control_slave;
  wire             pipeline_bridge_m1_read_data_valid_timestamp_timer_s1;
  wire    [ 31: 0] pipeline_bridge_m1_readdata;
  wire             pipeline_bridge_m1_readdatavalid;
  wire             pipeline_bridge_m1_requests_cpu_jtag_debug_module;
  wire             pipeline_bridge_m1_requests_custom_dma_clock_0_in;
  wire             pipeline_bridge_m1_requests_fir_dma_control;
  wire             pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave;
  wire             pipeline_bridge_m1_requests_sysid_control_slave;
  wire             pipeline_bridge_m1_requests_timestamp_timer_s1;
  wire             pipeline_bridge_m1_waitrequest;
  wire             pipeline_bridge_m1_write;
  wire    [ 31: 0] pipeline_bridge_m1_writedata;
  wire    [  9: 0] pipeline_bridge_s1_address;
  wire             pipeline_bridge_s1_arbiterlock;
  wire             pipeline_bridge_s1_arbiterlock2;
  wire             pipeline_bridge_s1_burstcount;
  wire    [  3: 0] pipeline_bridge_s1_byteenable;
  wire             pipeline_bridge_s1_chipselect;
  wire             pipeline_bridge_s1_debugaccess;
  wire             pipeline_bridge_s1_endofpacket;
  wire             pipeline_bridge_s1_endofpacket_from_sa;
  wire    [  9: 0] pipeline_bridge_s1_nativeaddress;
  wire             pipeline_bridge_s1_read;
  wire    [ 31: 0] pipeline_bridge_s1_readdata;
  wire    [ 31: 0] pipeline_bridge_s1_readdata_from_sa;
  wire             pipeline_bridge_s1_readdatavalid;
  wire             pipeline_bridge_s1_reset_n;
  wire             pipeline_bridge_s1_waitrequest;
  wire             pipeline_bridge_s1_waitrequest_from_sa;
  wire             pipeline_bridge_s1_write;
  wire    [ 31: 0] pipeline_bridge_s1_writedata;
  wire    [  2: 0] pll_s1_address;
  wire             pll_s1_chipselect;
  wire             pll_s1_read;
  wire    [ 15: 0] pll_s1_readdata;
  wire    [ 15: 0] pll_s1_readdata_from_sa;
  wire             pll_s1_reset_n;
  wire             pll_s1_resetrequest;
  wire             pll_s1_resetrequest_from_sa;
  wire             pll_s1_write;
  wire    [ 15: 0] pll_s1_writedata;
  wire             reset_n_sources;
  wire             sdram_write_clk;
  wire             ssram_clk;
  wire             stratix_dll_control_from_the_ddr_sdram;
  wire             sysid_control_slave_address;
  wire    [ 31: 0] sysid_control_slave_readdata;
  wire    [ 31: 0] sysid_control_slave_readdata_from_sa;
  wire             system_clk;
  wire             system_clk_reset_n;
  wire    [  2: 0] timestamp_timer_s1_address;
  wire             timestamp_timer_s1_chipselect;
  wire             timestamp_timer_s1_irq;
  wire             timestamp_timer_s1_irq_from_sa;
  wire    [ 15: 0] timestamp_timer_s1_readdata;
  wire    [ 15: 0] timestamp_timer_s1_readdata_from_sa;
  wire             timestamp_timer_s1_reset_n;
  wire             timestamp_timer_s1_write_n;
  wire    [ 15: 0] timestamp_timer_s1_writedata;
  cpu_jtag_debug_module_arbitrator the_cpu_jtag_debug_module
    (
      .clk                                                        (system_clk),
      .cpu_jtag_debug_module_address                              (cpu_jtag_debug_module_address),
      .cpu_jtag_debug_module_begintransfer                        (cpu_jtag_debug_module_begintransfer),
      .cpu_jtag_debug_module_byteenable                           (cpu_jtag_debug_module_byteenable),
      .cpu_jtag_debug_module_chipselect                           (cpu_jtag_debug_module_chipselect),
      .cpu_jtag_debug_module_debugaccess                          (cpu_jtag_debug_module_debugaccess),
      .cpu_jtag_debug_module_readdata                             (cpu_jtag_debug_module_readdata),
      .cpu_jtag_debug_module_readdata_from_sa                     (cpu_jtag_debug_module_readdata_from_sa),
      .cpu_jtag_debug_module_reset_n                              (cpu_jtag_debug_module_reset_n),
      .cpu_jtag_debug_module_resetrequest                         (cpu_jtag_debug_module_resetrequest),
      .cpu_jtag_debug_module_resetrequest_from_sa                 (cpu_jtag_debug_module_resetrequest_from_sa),
      .cpu_jtag_debug_module_write                                (cpu_jtag_debug_module_write),
      .cpu_jtag_debug_module_writedata                            (cpu_jtag_debug_module_writedata),
      .d1_cpu_jtag_debug_module_end_xfer                          (d1_cpu_jtag_debug_module_end_xfer),
      .pipeline_bridge_m1_address_to_slave                        (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                              (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_byteenable                              (pipeline_bridge_m1_byteenable),
      .pipeline_bridge_m1_chipselect                              (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_debugaccess                             (pipeline_bridge_m1_debugaccess),
      .pipeline_bridge_m1_granted_cpu_jtag_debug_module           (pipeline_bridge_m1_granted_cpu_jtag_debug_module),
      .pipeline_bridge_m1_latency_counter                         (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module (pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module),
      .pipeline_bridge_m1_read                                    (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module   (pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module),
      .pipeline_bridge_m1_requests_cpu_jtag_debug_module          (pipeline_bridge_m1_requests_cpu_jtag_debug_module),
      .pipeline_bridge_m1_write                                   (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                               (pipeline_bridge_m1_writedata),
      .reset_n                                                    (system_clk_reset_n)
    );

  cpu_data_master_arbitrator the_cpu_data_master
    (
      .clk                                                                        (system_clk),
      .cpu_data_master_address                                                    (cpu_data_master_address),
      .cpu_data_master_address_to_slave                                           (cpu_data_master_address_to_slave),
      .cpu_data_master_burstcount                                                 (cpu_data_master_burstcount),
      .cpu_data_master_byteenable                                                 (cpu_data_master_byteenable),
      .cpu_data_master_granted_custom_dma_burst_0_upstream                        (cpu_data_master_granted_custom_dma_burst_0_upstream),
      .cpu_data_master_granted_custom_dma_burst_2_upstream                        (cpu_data_master_granted_custom_dma_burst_2_upstream),
      .cpu_data_master_granted_custom_dma_burst_4_upstream                        (cpu_data_master_granted_custom_dma_burst_4_upstream),
      .cpu_data_master_irq                                                        (cpu_data_master_irq),
      .cpu_data_master_latency_counter                                            (cpu_data_master_latency_counter),
      .cpu_data_master_qualified_request_custom_dma_burst_0_upstream              (cpu_data_master_qualified_request_custom_dma_burst_0_upstream),
      .cpu_data_master_qualified_request_custom_dma_burst_2_upstream              (cpu_data_master_qualified_request_custom_dma_burst_2_upstream),
      .cpu_data_master_qualified_request_custom_dma_burst_4_upstream              (cpu_data_master_qualified_request_custom_dma_burst_4_upstream),
      .cpu_data_master_read                                                       (cpu_data_master_read),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register),
      .cpu_data_master_readdata                                                   (cpu_data_master_readdata),
      .cpu_data_master_readdatavalid                                              (cpu_data_master_readdatavalid),
      .cpu_data_master_requests_custom_dma_burst_0_upstream                       (cpu_data_master_requests_custom_dma_burst_0_upstream),
      .cpu_data_master_requests_custom_dma_burst_2_upstream                       (cpu_data_master_requests_custom_dma_burst_2_upstream),
      .cpu_data_master_requests_custom_dma_burst_4_upstream                       (cpu_data_master_requests_custom_dma_burst_4_upstream),
      .cpu_data_master_waitrequest                                                (cpu_data_master_waitrequest),
      .cpu_data_master_write                                                      (cpu_data_master_write),
      .cpu_data_master_writedata                                                  (cpu_data_master_writedata),
      .custom_dma_burst_0_upstream_readdata_from_sa                               (custom_dma_burst_0_upstream_readdata_from_sa),
      .custom_dma_burst_0_upstream_waitrequest_from_sa                            (custom_dma_burst_0_upstream_waitrequest_from_sa),
      .custom_dma_burst_2_upstream_readdata_from_sa                               (custom_dma_burst_2_upstream_readdata_from_sa),
      .custom_dma_burst_2_upstream_waitrequest_from_sa                            (custom_dma_burst_2_upstream_waitrequest_from_sa),
      .custom_dma_burst_4_upstream_readdata_from_sa                               (custom_dma_burst_4_upstream_readdata_from_sa),
      .custom_dma_burst_4_upstream_waitrequest_from_sa                            (custom_dma_burst_4_upstream_waitrequest_from_sa),
      .d1_custom_dma_burst_0_upstream_end_xfer                                    (d1_custom_dma_burst_0_upstream_end_xfer),
      .d1_custom_dma_burst_2_upstream_end_xfer                                    (d1_custom_dma_burst_2_upstream_end_xfer),
      .d1_custom_dma_burst_4_upstream_end_xfer                                    (d1_custom_dma_burst_4_upstream_end_xfer),
      .fir_dma_control_irq_from_sa                                                (fir_dma_control_irq_from_sa),
      .jtag_uart_avalon_jtag_slave_irq_from_sa                                    (jtag_uart_avalon_jtag_slave_irq_from_sa),
      .reset_n                                                                    (system_clk_reset_n),
      .timestamp_timer_s1_irq_from_sa                                             (timestamp_timer_s1_irq_from_sa)
    );

  cpu_instruction_master_arbitrator the_cpu_instruction_master
    (
      .clk                                                                               (system_clk),
      .cpu_instruction_master_address                                                    (cpu_instruction_master_address),
      .cpu_instruction_master_address_to_slave                                           (cpu_instruction_master_address_to_slave),
      .cpu_instruction_master_burstcount                                                 (cpu_instruction_master_burstcount),
      .cpu_instruction_master_granted_custom_dma_burst_1_upstream                        (cpu_instruction_master_granted_custom_dma_burst_1_upstream),
      .cpu_instruction_master_granted_custom_dma_burst_3_upstream                        (cpu_instruction_master_granted_custom_dma_burst_3_upstream),
      .cpu_instruction_master_latency_counter                                            (cpu_instruction_master_latency_counter),
      .cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream              (cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream),
      .cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream              (cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream),
      .cpu_instruction_master_read                                                       (cpu_instruction_master_read),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream                (cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream                (cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register),
      .cpu_instruction_master_readdata                                                   (cpu_instruction_master_readdata),
      .cpu_instruction_master_readdatavalid                                              (cpu_instruction_master_readdatavalid),
      .cpu_instruction_master_requests_custom_dma_burst_1_upstream                       (cpu_instruction_master_requests_custom_dma_burst_1_upstream),
      .cpu_instruction_master_requests_custom_dma_burst_3_upstream                       (cpu_instruction_master_requests_custom_dma_burst_3_upstream),
      .cpu_instruction_master_waitrequest                                                (cpu_instruction_master_waitrequest),
      .custom_dma_burst_1_upstream_readdata_from_sa                                      (custom_dma_burst_1_upstream_readdata_from_sa),
      .custom_dma_burst_1_upstream_waitrequest_from_sa                                   (custom_dma_burst_1_upstream_waitrequest_from_sa),
      .custom_dma_burst_3_upstream_readdata_from_sa                                      (custom_dma_burst_3_upstream_readdata_from_sa),
      .custom_dma_burst_3_upstream_waitrequest_from_sa                                   (custom_dma_burst_3_upstream_waitrequest_from_sa),
      .d1_custom_dma_burst_1_upstream_end_xfer                                           (d1_custom_dma_burst_1_upstream_end_xfer),
      .d1_custom_dma_burst_3_upstream_end_xfer                                           (d1_custom_dma_burst_3_upstream_end_xfer),
      .reset_n                                                                           (system_clk_reset_n)
    );

  cpu the_cpu
    (
      .clk                                   (system_clk),
      .d_address                             (cpu_data_master_address),
      .d_burstcount                          (cpu_data_master_burstcount),
      .d_byteenable                          (cpu_data_master_byteenable),
      .d_irq                                 (cpu_data_master_irq),
      .d_read                                (cpu_data_master_read),
      .d_readdata                            (cpu_data_master_readdata),
      .d_readdatavalid                       (cpu_data_master_readdatavalid),
      .d_waitrequest                         (cpu_data_master_waitrequest),
      .d_write                               (cpu_data_master_write),
      .d_writedata                           (cpu_data_master_writedata),
      .i_address                             (cpu_instruction_master_address),
      .i_burstcount                          (cpu_instruction_master_burstcount),
      .i_read                                (cpu_instruction_master_read),
      .i_readdata                            (cpu_instruction_master_readdata),
      .i_readdatavalid                       (cpu_instruction_master_readdatavalid),
      .i_waitrequest                         (cpu_instruction_master_waitrequest),
      .jtag_debug_module_address             (cpu_jtag_debug_module_address),
      .jtag_debug_module_begintransfer       (cpu_jtag_debug_module_begintransfer),
      .jtag_debug_module_byteenable          (cpu_jtag_debug_module_byteenable),
      .jtag_debug_module_debugaccess         (cpu_jtag_debug_module_debugaccess),
      .jtag_debug_module_debugaccess_to_roms (cpu_data_master_debugaccess),
      .jtag_debug_module_readdata            (cpu_jtag_debug_module_readdata),
      .jtag_debug_module_resetrequest        (cpu_jtag_debug_module_resetrequest),
      .jtag_debug_module_select              (cpu_jtag_debug_module_chipselect),
      .jtag_debug_module_write               (cpu_jtag_debug_module_write),
      .jtag_debug_module_writedata           (cpu_jtag_debug_module_writedata),
      .reset_n                               (cpu_jtag_debug_module_reset_n)
    );

  custom_dma_burst_0_upstream_arbitrator the_custom_dma_burst_0_upstream
    (
      .clk                                                                        (system_clk),
      .cpu_data_master_address_to_slave                                           (cpu_data_master_address_to_slave),
      .cpu_data_master_burstcount                                                 (cpu_data_master_burstcount),
      .cpu_data_master_byteenable                                                 (cpu_data_master_byteenable),
      .cpu_data_master_debugaccess                                                (cpu_data_master_debugaccess),
      .cpu_data_master_granted_custom_dma_burst_0_upstream                        (cpu_data_master_granted_custom_dma_burst_0_upstream),
      .cpu_data_master_latency_counter                                            (cpu_data_master_latency_counter),
      .cpu_data_master_qualified_request_custom_dma_burst_0_upstream              (cpu_data_master_qualified_request_custom_dma_burst_0_upstream),
      .cpu_data_master_read                                                       (cpu_data_master_read),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register),
      .cpu_data_master_requests_custom_dma_burst_0_upstream                       (cpu_data_master_requests_custom_dma_burst_0_upstream),
      .cpu_data_master_write                                                      (cpu_data_master_write),
      .cpu_data_master_writedata                                                  (cpu_data_master_writedata),
      .custom_dma_burst_0_upstream_address                                        (custom_dma_burst_0_upstream_address),
      .custom_dma_burst_0_upstream_burstcount                                     (custom_dma_burst_0_upstream_burstcount),
      .custom_dma_burst_0_upstream_byteaddress                                    (custom_dma_burst_0_upstream_byteaddress),
      .custom_dma_burst_0_upstream_byteenable                                     (custom_dma_burst_0_upstream_byteenable),
      .custom_dma_burst_0_upstream_debugaccess                                    (custom_dma_burst_0_upstream_debugaccess),
      .custom_dma_burst_0_upstream_read                                           (custom_dma_burst_0_upstream_read),
      .custom_dma_burst_0_upstream_readdata                                       (custom_dma_burst_0_upstream_readdata),
      .custom_dma_burst_0_upstream_readdata_from_sa                               (custom_dma_burst_0_upstream_readdata_from_sa),
      .custom_dma_burst_0_upstream_readdatavalid                                  (custom_dma_burst_0_upstream_readdatavalid),
      .custom_dma_burst_0_upstream_waitrequest                                    (custom_dma_burst_0_upstream_waitrequest),
      .custom_dma_burst_0_upstream_waitrequest_from_sa                            (custom_dma_burst_0_upstream_waitrequest_from_sa),
      .custom_dma_burst_0_upstream_write                                          (custom_dma_burst_0_upstream_write),
      .custom_dma_burst_0_upstream_writedata                                      (custom_dma_burst_0_upstream_writedata),
      .d1_custom_dma_burst_0_upstream_end_xfer                                    (d1_custom_dma_burst_0_upstream_end_xfer),
      .reset_n                                                                    (system_clk_reset_n)
    );

  custom_dma_burst_0_downstream_arbitrator the_custom_dma_burst_0_downstream
    (
      .clk                                                          (system_clk),
      .custom_dma_burst_0_downstream_address                        (custom_dma_burst_0_downstream_address),
      .custom_dma_burst_0_downstream_address_to_slave               (custom_dma_burst_0_downstream_address_to_slave),
      .custom_dma_burst_0_downstream_burstcount                     (custom_dma_burst_0_downstream_burstcount),
      .custom_dma_burst_0_downstream_byteenable                     (custom_dma_burst_0_downstream_byteenable),
      .custom_dma_burst_0_downstream_granted_ext_ssram_s1           (custom_dma_burst_0_downstream_granted_ext_ssram_s1),
      .custom_dma_burst_0_downstream_latency_counter                (custom_dma_burst_0_downstream_latency_counter),
      .custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 (custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1),
      .custom_dma_burst_0_downstream_read                           (custom_dma_burst_0_downstream_read),
      .custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1   (custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1),
      .custom_dma_burst_0_downstream_readdata                       (custom_dma_burst_0_downstream_readdata),
      .custom_dma_burst_0_downstream_readdatavalid                  (custom_dma_burst_0_downstream_readdatavalid),
      .custom_dma_burst_0_downstream_requests_ext_ssram_s1          (custom_dma_burst_0_downstream_requests_ext_ssram_s1),
      .custom_dma_burst_0_downstream_reset_n                        (custom_dma_burst_0_downstream_reset_n),
      .custom_dma_burst_0_downstream_waitrequest                    (custom_dma_burst_0_downstream_waitrequest),
      .custom_dma_burst_0_downstream_write                          (custom_dma_burst_0_downstream_write),
      .custom_dma_burst_0_downstream_writedata                      (custom_dma_burst_0_downstream_writedata),
      .d1_ext_ssram_bus_avalon_slave_end_xfer                       (d1_ext_ssram_bus_avalon_slave_end_xfer),
      .incoming_ext_ssram_bus_data                                  (incoming_ext_ssram_bus_data),
      .reset_n                                                      (system_clk_reset_n)
    );

  custom_dma_burst_0 the_custom_dma_burst_0
    (
      .clk                             (system_clk),
      .downstream_readdata             (custom_dma_burst_0_downstream_readdata),
      .downstream_readdatavalid        (custom_dma_burst_0_downstream_readdatavalid),
      .downstream_waitrequest          (custom_dma_burst_0_downstream_waitrequest),
      .reg_downstream_address          (custom_dma_burst_0_downstream_address),
      .reg_downstream_arbitrationshare (custom_dma_burst_0_downstream_arbitrationshare),
      .reg_downstream_burstcount       (custom_dma_burst_0_downstream_burstcount),
      .reg_downstream_byteenable       (custom_dma_burst_0_downstream_byteenable),
      .reg_downstream_debugaccess      (custom_dma_burst_0_downstream_debugaccess),
      .reg_downstream_nativeaddress    (custom_dma_burst_0_downstream_nativeaddress),
      .reg_downstream_read             (custom_dma_burst_0_downstream_read),
      .reg_downstream_write            (custom_dma_burst_0_downstream_write),
      .reg_downstream_writedata        (custom_dma_burst_0_downstream_writedata),
      .reset_n                         (custom_dma_burst_0_downstream_reset_n),
      .upstream_address                (custom_dma_burst_0_upstream_byteaddress),
      .upstream_burstcount             (custom_dma_burst_0_upstream_burstcount),
      .upstream_byteenable             (custom_dma_burst_0_upstream_byteenable),
      .upstream_debugaccess            (custom_dma_burst_0_upstream_debugaccess),
      .upstream_nativeaddress          (custom_dma_burst_0_upstream_address),
      .upstream_read                   (custom_dma_burst_0_upstream_read),
      .upstream_readdata               (custom_dma_burst_0_upstream_readdata),
      .upstream_readdatavalid          (custom_dma_burst_0_upstream_readdatavalid),
      .upstream_waitrequest            (custom_dma_burst_0_upstream_waitrequest),
      .upstream_write                  (custom_dma_burst_0_upstream_write),
      .upstream_writedata              (custom_dma_burst_0_upstream_writedata)
    );

  custom_dma_burst_1_upstream_arbitrator the_custom_dma_burst_1_upstream
    (
      .clk                                                                               (system_clk),
      .cpu_instruction_master_address_to_slave                                           (cpu_instruction_master_address_to_slave),
      .cpu_instruction_master_burstcount                                                 (cpu_instruction_master_burstcount),
      .cpu_instruction_master_granted_custom_dma_burst_1_upstream                        (cpu_instruction_master_granted_custom_dma_burst_1_upstream),
      .cpu_instruction_master_latency_counter                                            (cpu_instruction_master_latency_counter),
      .cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream              (cpu_instruction_master_qualified_request_custom_dma_burst_1_upstream),
      .cpu_instruction_master_read                                                       (cpu_instruction_master_read),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream                (cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register),
      .cpu_instruction_master_requests_custom_dma_burst_1_upstream                       (cpu_instruction_master_requests_custom_dma_burst_1_upstream),
      .custom_dma_burst_1_upstream_address                                               (custom_dma_burst_1_upstream_address),
      .custom_dma_burst_1_upstream_byteaddress                                           (custom_dma_burst_1_upstream_byteaddress),
      .custom_dma_burst_1_upstream_byteenable                                            (custom_dma_burst_1_upstream_byteenable),
      .custom_dma_burst_1_upstream_debugaccess                                           (custom_dma_burst_1_upstream_debugaccess),
      .custom_dma_burst_1_upstream_read                                                  (custom_dma_burst_1_upstream_read),
      .custom_dma_burst_1_upstream_readdata                                              (custom_dma_burst_1_upstream_readdata),
      .custom_dma_burst_1_upstream_readdata_from_sa                                      (custom_dma_burst_1_upstream_readdata_from_sa),
      .custom_dma_burst_1_upstream_readdatavalid                                         (custom_dma_burst_1_upstream_readdatavalid),
      .custom_dma_burst_1_upstream_waitrequest                                           (custom_dma_burst_1_upstream_waitrequest),
      .custom_dma_burst_1_upstream_waitrequest_from_sa                                   (custom_dma_burst_1_upstream_waitrequest_from_sa),
      .custom_dma_burst_1_upstream_write                                                 (custom_dma_burst_1_upstream_write),
      .d1_custom_dma_burst_1_upstream_end_xfer                                           (d1_custom_dma_burst_1_upstream_end_xfer),
      .reset_n                                                                           (system_clk_reset_n)
    );

  custom_dma_burst_1_downstream_arbitrator the_custom_dma_burst_1_downstream
    (
      .clk                                                                             (system_clk),
      .custom_dma_burst_1_downstream_address                                           (custom_dma_burst_1_downstream_address),
      .custom_dma_burst_1_downstream_address_to_slave                                  (custom_dma_burst_1_downstream_address_to_slave),
      .custom_dma_burst_1_downstream_burstcount                                        (custom_dma_burst_1_downstream_burstcount),
      .custom_dma_burst_1_downstream_byteenable                                        (custom_dma_burst_1_downstream_byteenable),
      .custom_dma_burst_1_downstream_granted_pipeline_bridge_s1                        (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_latency_counter                                   (custom_dma_burst_1_downstream_latency_counter),
      .custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1              (custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_read                                              (custom_dma_burst_1_downstream_read),
      .custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1                (custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register (custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register),
      .custom_dma_burst_1_downstream_readdata                                          (custom_dma_burst_1_downstream_readdata),
      .custom_dma_burst_1_downstream_readdatavalid                                     (custom_dma_burst_1_downstream_readdatavalid),
      .custom_dma_burst_1_downstream_requests_pipeline_bridge_s1                       (custom_dma_burst_1_downstream_requests_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_reset_n                                           (custom_dma_burst_1_downstream_reset_n),
      .custom_dma_burst_1_downstream_waitrequest                                       (custom_dma_burst_1_downstream_waitrequest),
      .custom_dma_burst_1_downstream_write                                             (custom_dma_burst_1_downstream_write),
      .custom_dma_burst_1_downstream_writedata                                         (custom_dma_burst_1_downstream_writedata),
      .d1_pipeline_bridge_s1_end_xfer                                                  (d1_pipeline_bridge_s1_end_xfer),
      .pipeline_bridge_s1_readdata_from_sa                                             (pipeline_bridge_s1_readdata_from_sa),
      .pipeline_bridge_s1_waitrequest_from_sa                                          (pipeline_bridge_s1_waitrequest_from_sa),
      .reset_n                                                                         (system_clk_reset_n)
    );

  custom_dma_burst_1 the_custom_dma_burst_1
    (
      .clk                             (system_clk),
      .downstream_readdata             (custom_dma_burst_1_downstream_readdata),
      .downstream_readdatavalid        (custom_dma_burst_1_downstream_readdatavalid),
      .downstream_waitrequest          (custom_dma_burst_1_downstream_waitrequest),
      .reg_downstream_address          (custom_dma_burst_1_downstream_address),
      .reg_downstream_arbitrationshare (custom_dma_burst_1_downstream_arbitrationshare),
      .reg_downstream_burstcount       (custom_dma_burst_1_downstream_burstcount),
      .reg_downstream_byteenable       (custom_dma_burst_1_downstream_byteenable),
      .reg_downstream_debugaccess      (custom_dma_burst_1_downstream_debugaccess),
      .reg_downstream_nativeaddress    (custom_dma_burst_1_downstream_nativeaddress),
      .reg_downstream_read             (custom_dma_burst_1_downstream_read),
      .reg_downstream_write            (custom_dma_burst_1_downstream_write),
      .reg_downstream_writedata        (custom_dma_burst_1_downstream_writedata),
      .reset_n                         (custom_dma_burst_1_downstream_reset_n),
      .upstream_address                (custom_dma_burst_1_upstream_byteaddress),
      .upstream_byteenable             (custom_dma_burst_1_upstream_byteenable),
      .upstream_debugaccess            (custom_dma_burst_1_upstream_debugaccess),
      .upstream_nativeaddress          (custom_dma_burst_1_upstream_address),
      .upstream_read                   (custom_dma_burst_1_upstream_read),
      .upstream_readdata               (custom_dma_burst_1_upstream_readdata),
      .upstream_readdatavalid          (custom_dma_burst_1_upstream_readdatavalid),
      .upstream_waitrequest            (custom_dma_burst_1_upstream_waitrequest),
      .upstream_write                  (custom_dma_burst_1_upstream_write),
      .upstream_writedata              (custom_dma_burst_1_upstream_writedata)
    );

  custom_dma_burst_2_upstream_arbitrator the_custom_dma_burst_2_upstream
    (
      .clk                                                                        (system_clk),
      .cpu_data_master_address_to_slave                                           (cpu_data_master_address_to_slave),
      .cpu_data_master_burstcount                                                 (cpu_data_master_burstcount),
      .cpu_data_master_byteenable                                                 (cpu_data_master_byteenable),
      .cpu_data_master_debugaccess                                                (cpu_data_master_debugaccess),
      .cpu_data_master_granted_custom_dma_burst_2_upstream                        (cpu_data_master_granted_custom_dma_burst_2_upstream),
      .cpu_data_master_latency_counter                                            (cpu_data_master_latency_counter),
      .cpu_data_master_qualified_request_custom_dma_burst_2_upstream              (cpu_data_master_qualified_request_custom_dma_burst_2_upstream),
      .cpu_data_master_read                                                       (cpu_data_master_read),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register),
      .cpu_data_master_requests_custom_dma_burst_2_upstream                       (cpu_data_master_requests_custom_dma_burst_2_upstream),
      .cpu_data_master_write                                                      (cpu_data_master_write),
      .cpu_data_master_writedata                                                  (cpu_data_master_writedata),
      .custom_dma_burst_2_upstream_address                                        (custom_dma_burst_2_upstream_address),
      .custom_dma_burst_2_upstream_burstcount                                     (custom_dma_burst_2_upstream_burstcount),
      .custom_dma_burst_2_upstream_byteaddress                                    (custom_dma_burst_2_upstream_byteaddress),
      .custom_dma_burst_2_upstream_byteenable                                     (custom_dma_burst_2_upstream_byteenable),
      .custom_dma_burst_2_upstream_debugaccess                                    (custom_dma_burst_2_upstream_debugaccess),
      .custom_dma_burst_2_upstream_read                                           (custom_dma_burst_2_upstream_read),
      .custom_dma_burst_2_upstream_readdata                                       (custom_dma_burst_2_upstream_readdata),
      .custom_dma_burst_2_upstream_readdata_from_sa                               (custom_dma_burst_2_upstream_readdata_from_sa),
      .custom_dma_burst_2_upstream_readdatavalid                                  (custom_dma_burst_2_upstream_readdatavalid),
      .custom_dma_burst_2_upstream_waitrequest                                    (custom_dma_burst_2_upstream_waitrequest),
      .custom_dma_burst_2_upstream_waitrequest_from_sa                            (custom_dma_burst_2_upstream_waitrequest_from_sa),
      .custom_dma_burst_2_upstream_write                                          (custom_dma_burst_2_upstream_write),
      .custom_dma_burst_2_upstream_writedata                                      (custom_dma_burst_2_upstream_writedata),
      .d1_custom_dma_burst_2_upstream_end_xfer                                    (d1_custom_dma_burst_2_upstream_end_xfer),
      .reset_n                                                                    (system_clk_reset_n)
    );

  custom_dma_burst_2_downstream_arbitrator the_custom_dma_burst_2_downstream
    (
      .clk                                                                             (system_clk),
      .custom_dma_burst_2_downstream_address                                           (custom_dma_burst_2_downstream_address),
      .custom_dma_burst_2_downstream_address_to_slave                                  (custom_dma_burst_2_downstream_address_to_slave),
      .custom_dma_burst_2_downstream_burstcount                                        (custom_dma_burst_2_downstream_burstcount),
      .custom_dma_burst_2_downstream_byteenable                                        (custom_dma_burst_2_downstream_byteenable),
      .custom_dma_burst_2_downstream_granted_pipeline_bridge_s1                        (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_latency_counter                                   (custom_dma_burst_2_downstream_latency_counter),
      .custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1              (custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_read                                              (custom_dma_burst_2_downstream_read),
      .custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1                (custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register (custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register),
      .custom_dma_burst_2_downstream_readdata                                          (custom_dma_burst_2_downstream_readdata),
      .custom_dma_burst_2_downstream_readdatavalid                                     (custom_dma_burst_2_downstream_readdatavalid),
      .custom_dma_burst_2_downstream_requests_pipeline_bridge_s1                       (custom_dma_burst_2_downstream_requests_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_reset_n                                           (custom_dma_burst_2_downstream_reset_n),
      .custom_dma_burst_2_downstream_waitrequest                                       (custom_dma_burst_2_downstream_waitrequest),
      .custom_dma_burst_2_downstream_write                                             (custom_dma_burst_2_downstream_write),
      .custom_dma_burst_2_downstream_writedata                                         (custom_dma_burst_2_downstream_writedata),
      .d1_pipeline_bridge_s1_end_xfer                                                  (d1_pipeline_bridge_s1_end_xfer),
      .pipeline_bridge_s1_readdata_from_sa                                             (pipeline_bridge_s1_readdata_from_sa),
      .pipeline_bridge_s1_waitrequest_from_sa                                          (pipeline_bridge_s1_waitrequest_from_sa),
      .reset_n                                                                         (system_clk_reset_n)
    );

  custom_dma_burst_2 the_custom_dma_burst_2
    (
      .clk                             (system_clk),
      .downstream_readdata             (custom_dma_burst_2_downstream_readdata),
      .downstream_readdatavalid        (custom_dma_burst_2_downstream_readdatavalid),
      .downstream_waitrequest          (custom_dma_burst_2_downstream_waitrequest),
      .reg_downstream_address          (custom_dma_burst_2_downstream_address),
      .reg_downstream_arbitrationshare (custom_dma_burst_2_downstream_arbitrationshare),
      .reg_downstream_burstcount       (custom_dma_burst_2_downstream_burstcount),
      .reg_downstream_byteenable       (custom_dma_burst_2_downstream_byteenable),
      .reg_downstream_debugaccess      (custom_dma_burst_2_downstream_debugaccess),
      .reg_downstream_nativeaddress    (custom_dma_burst_2_downstream_nativeaddress),
      .reg_downstream_read             (custom_dma_burst_2_downstream_read),
      .reg_downstream_write            (custom_dma_burst_2_downstream_write),
      .reg_downstream_writedata        (custom_dma_burst_2_downstream_writedata),
      .reset_n                         (custom_dma_burst_2_downstream_reset_n),
      .upstream_address                (custom_dma_burst_2_upstream_byteaddress),
      .upstream_burstcount             (custom_dma_burst_2_upstream_burstcount),
      .upstream_byteenable             (custom_dma_burst_2_upstream_byteenable),
      .upstream_debugaccess            (custom_dma_burst_2_upstream_debugaccess),
      .upstream_nativeaddress          (custom_dma_burst_2_upstream_address),
      .upstream_read                   (custom_dma_burst_2_upstream_read),
      .upstream_readdata               (custom_dma_burst_2_upstream_readdata),
      .upstream_readdatavalid          (custom_dma_burst_2_upstream_readdatavalid),
      .upstream_waitrequest            (custom_dma_burst_2_upstream_waitrequest),
      .upstream_write                  (custom_dma_burst_2_upstream_write),
      .upstream_writedata              (custom_dma_burst_2_upstream_writedata)
    );

  custom_dma_burst_3_upstream_arbitrator the_custom_dma_burst_3_upstream
    (
      .clk                                                                               (system_clk),
      .cpu_instruction_master_address_to_slave                                           (cpu_instruction_master_address_to_slave),
      .cpu_instruction_master_burstcount                                                 (cpu_instruction_master_burstcount),
      .cpu_instruction_master_granted_custom_dma_burst_3_upstream                        (cpu_instruction_master_granted_custom_dma_burst_3_upstream),
      .cpu_instruction_master_latency_counter                                            (cpu_instruction_master_latency_counter),
      .cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream              (cpu_instruction_master_qualified_request_custom_dma_burst_3_upstream),
      .cpu_instruction_master_read                                                       (cpu_instruction_master_read),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_1_upstream_shift_register),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream                (cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream),
      .cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register (cpu_instruction_master_read_data_valid_custom_dma_burst_3_upstream_shift_register),
      .cpu_instruction_master_requests_custom_dma_burst_3_upstream                       (cpu_instruction_master_requests_custom_dma_burst_3_upstream),
      .custom_dma_burst_3_upstream_address                                               (custom_dma_burst_3_upstream_address),
      .custom_dma_burst_3_upstream_byteaddress                                           (custom_dma_burst_3_upstream_byteaddress),
      .custom_dma_burst_3_upstream_byteenable                                            (custom_dma_burst_3_upstream_byteenable),
      .custom_dma_burst_3_upstream_debugaccess                                           (custom_dma_burst_3_upstream_debugaccess),
      .custom_dma_burst_3_upstream_read                                                  (custom_dma_burst_3_upstream_read),
      .custom_dma_burst_3_upstream_readdata                                              (custom_dma_burst_3_upstream_readdata),
      .custom_dma_burst_3_upstream_readdata_from_sa                                      (custom_dma_burst_3_upstream_readdata_from_sa),
      .custom_dma_burst_3_upstream_readdatavalid                                         (custom_dma_burst_3_upstream_readdatavalid),
      .custom_dma_burst_3_upstream_waitrequest                                           (custom_dma_burst_3_upstream_waitrequest),
      .custom_dma_burst_3_upstream_waitrequest_from_sa                                   (custom_dma_burst_3_upstream_waitrequest_from_sa),
      .custom_dma_burst_3_upstream_write                                                 (custom_dma_burst_3_upstream_write),
      .d1_custom_dma_burst_3_upstream_end_xfer                                           (d1_custom_dma_burst_3_upstream_end_xfer),
      .reset_n                                                                           (system_clk_reset_n)
    );

  custom_dma_burst_3_downstream_arbitrator the_custom_dma_burst_3_downstream
    (
      .clk                                                                       (system_clk),
      .custom_dma_burst_3_downstream_address                                     (custom_dma_burst_3_downstream_address),
      .custom_dma_burst_3_downstream_address_to_slave                            (custom_dma_burst_3_downstream_address_to_slave),
      .custom_dma_burst_3_downstream_burstcount                                  (custom_dma_burst_3_downstream_burstcount),
      .custom_dma_burst_3_downstream_byteenable                                  (custom_dma_burst_3_downstream_byteenable),
      .custom_dma_burst_3_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_3_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_latency_counter                             (custom_dma_burst_3_downstream_latency_counter),
      .custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_read                                        (custom_dma_burst_3_downstream_read),
      .custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_3_downstream_readdata                                    (custom_dma_burst_3_downstream_readdata),
      .custom_dma_burst_3_downstream_readdatavalid                               (custom_dma_burst_3_downstream_readdatavalid),
      .custom_dma_burst_3_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_3_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_reset_n                                     (custom_dma_burst_3_downstream_reset_n),
      .custom_dma_burst_3_downstream_waitrequest                                 (custom_dma_burst_3_downstream_waitrequest),
      .custom_dma_burst_3_downstream_write                                       (custom_dma_burst_3_downstream_write),
      .custom_dma_burst_3_downstream_writedata                                   (custom_dma_burst_3_downstream_writedata),
      .d1_ddr_sdram_s1_end_xfer                                                  (d1_ddr_sdram_s1_end_xfer),
      .ddr_sdram_s1_readdata_from_sa                                             (ddr_sdram_s1_readdata_from_sa),
      .ddr_sdram_s1_waitrequest_n_from_sa                                        (ddr_sdram_s1_waitrequest_n_from_sa),
      .reset_n                                                                   (system_clk_reset_n)
    );

  custom_dma_burst_3 the_custom_dma_burst_3
    (
      .clk                             (system_clk),
      .downstream_readdata             (custom_dma_burst_3_downstream_readdata),
      .downstream_readdatavalid        (custom_dma_burst_3_downstream_readdatavalid),
      .downstream_waitrequest          (custom_dma_burst_3_downstream_waitrequest),
      .reg_downstream_address          (custom_dma_burst_3_downstream_address),
      .reg_downstream_arbitrationshare (custom_dma_burst_3_downstream_arbitrationshare),
      .reg_downstream_burstcount       (custom_dma_burst_3_downstream_burstcount),
      .reg_downstream_byteenable       (custom_dma_burst_3_downstream_byteenable),
      .reg_downstream_debugaccess      (custom_dma_burst_3_downstream_debugaccess),
      .reg_downstream_nativeaddress    (custom_dma_burst_3_downstream_nativeaddress),
      .reg_downstream_read             (custom_dma_burst_3_downstream_read),
      .reg_downstream_write            (custom_dma_burst_3_downstream_write),
      .reg_downstream_writedata        (custom_dma_burst_3_downstream_writedata),
      .reset_n                         (custom_dma_burst_3_downstream_reset_n),
      .upstream_address                (custom_dma_burst_3_upstream_byteaddress),
      .upstream_byteenable             (custom_dma_burst_3_upstream_byteenable),
      .upstream_debugaccess            (custom_dma_burst_3_upstream_debugaccess),
      .upstream_nativeaddress          (custom_dma_burst_3_upstream_address),
      .upstream_read                   (custom_dma_burst_3_upstream_read),
      .upstream_readdata               (custom_dma_burst_3_upstream_readdata),
      .upstream_readdatavalid          (custom_dma_burst_3_upstream_readdatavalid),
      .upstream_waitrequest            (custom_dma_burst_3_upstream_waitrequest),
      .upstream_write                  (custom_dma_burst_3_upstream_write),
      .upstream_writedata              (custom_dma_burst_3_upstream_writedata)
    );

  custom_dma_burst_4_upstream_arbitrator the_custom_dma_burst_4_upstream
    (
      .clk                                                                        (system_clk),
      .cpu_data_master_address_to_slave                                           (cpu_data_master_address_to_slave),
      .cpu_data_master_burstcount                                                 (cpu_data_master_burstcount),
      .cpu_data_master_byteenable                                                 (cpu_data_master_byteenable),
      .cpu_data_master_debugaccess                                                (cpu_data_master_debugaccess),
      .cpu_data_master_granted_custom_dma_burst_4_upstream                        (cpu_data_master_granted_custom_dma_burst_4_upstream),
      .cpu_data_master_latency_counter                                            (cpu_data_master_latency_counter),
      .cpu_data_master_qualified_request_custom_dma_burst_4_upstream              (cpu_data_master_qualified_request_custom_dma_burst_4_upstream),
      .cpu_data_master_read                                                       (cpu_data_master_read),
      .cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_0_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_2_upstream_shift_register),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream                (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream),
      .cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register (cpu_data_master_read_data_valid_custom_dma_burst_4_upstream_shift_register),
      .cpu_data_master_requests_custom_dma_burst_4_upstream                       (cpu_data_master_requests_custom_dma_burst_4_upstream),
      .cpu_data_master_write                                                      (cpu_data_master_write),
      .cpu_data_master_writedata                                                  (cpu_data_master_writedata),
      .custom_dma_burst_4_upstream_address                                        (custom_dma_burst_4_upstream_address),
      .custom_dma_burst_4_upstream_burstcount                                     (custom_dma_burst_4_upstream_burstcount),
      .custom_dma_burst_4_upstream_byteaddress                                    (custom_dma_burst_4_upstream_byteaddress),
      .custom_dma_burst_4_upstream_byteenable                                     (custom_dma_burst_4_upstream_byteenable),
      .custom_dma_burst_4_upstream_debugaccess                                    (custom_dma_burst_4_upstream_debugaccess),
      .custom_dma_burst_4_upstream_read                                           (custom_dma_burst_4_upstream_read),
      .custom_dma_burst_4_upstream_readdata                                       (custom_dma_burst_4_upstream_readdata),
      .custom_dma_burst_4_upstream_readdata_from_sa                               (custom_dma_burst_4_upstream_readdata_from_sa),
      .custom_dma_burst_4_upstream_readdatavalid                                  (custom_dma_burst_4_upstream_readdatavalid),
      .custom_dma_burst_4_upstream_waitrequest                                    (custom_dma_burst_4_upstream_waitrequest),
      .custom_dma_burst_4_upstream_waitrequest_from_sa                            (custom_dma_burst_4_upstream_waitrequest_from_sa),
      .custom_dma_burst_4_upstream_write                                          (custom_dma_burst_4_upstream_write),
      .custom_dma_burst_4_upstream_writedata                                      (custom_dma_burst_4_upstream_writedata),
      .d1_custom_dma_burst_4_upstream_end_xfer                                    (d1_custom_dma_burst_4_upstream_end_xfer),
      .reset_n                                                                    (system_clk_reset_n)
    );

  custom_dma_burst_4_downstream_arbitrator the_custom_dma_burst_4_downstream
    (
      .clk                                                                       (system_clk),
      .custom_dma_burst_4_downstream_address                                     (custom_dma_burst_4_downstream_address),
      .custom_dma_burst_4_downstream_address_to_slave                            (custom_dma_burst_4_downstream_address_to_slave),
      .custom_dma_burst_4_downstream_burstcount                                  (custom_dma_burst_4_downstream_burstcount),
      .custom_dma_burst_4_downstream_byteenable                                  (custom_dma_burst_4_downstream_byteenable),
      .custom_dma_burst_4_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_4_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_latency_counter                             (custom_dma_burst_4_downstream_latency_counter),
      .custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_read                                        (custom_dma_burst_4_downstream_read),
      .custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_4_downstream_readdata                                    (custom_dma_burst_4_downstream_readdata),
      .custom_dma_burst_4_downstream_readdatavalid                               (custom_dma_burst_4_downstream_readdatavalid),
      .custom_dma_burst_4_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_4_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_reset_n                                     (custom_dma_burst_4_downstream_reset_n),
      .custom_dma_burst_4_downstream_waitrequest                                 (custom_dma_burst_4_downstream_waitrequest),
      .custom_dma_burst_4_downstream_write                                       (custom_dma_burst_4_downstream_write),
      .custom_dma_burst_4_downstream_writedata                                   (custom_dma_burst_4_downstream_writedata),
      .d1_ddr_sdram_s1_end_xfer                                                  (d1_ddr_sdram_s1_end_xfer),
      .ddr_sdram_s1_readdata_from_sa                                             (ddr_sdram_s1_readdata_from_sa),
      .ddr_sdram_s1_waitrequest_n_from_sa                                        (ddr_sdram_s1_waitrequest_n_from_sa),
      .reset_n                                                                   (system_clk_reset_n)
    );

  custom_dma_burst_4 the_custom_dma_burst_4
    (
      .clk                             (system_clk),
      .downstream_readdata             (custom_dma_burst_4_downstream_readdata),
      .downstream_readdatavalid        (custom_dma_burst_4_downstream_readdatavalid),
      .downstream_waitrequest          (custom_dma_burst_4_downstream_waitrequest),
      .reg_downstream_address          (custom_dma_burst_4_downstream_address),
      .reg_downstream_arbitrationshare (custom_dma_burst_4_downstream_arbitrationshare),
      .reg_downstream_burstcount       (custom_dma_burst_4_downstream_burstcount),
      .reg_downstream_byteenable       (custom_dma_burst_4_downstream_byteenable),
      .reg_downstream_debugaccess      (custom_dma_burst_4_downstream_debugaccess),
      .reg_downstream_nativeaddress    (custom_dma_burst_4_downstream_nativeaddress),
      .reg_downstream_read             (custom_dma_burst_4_downstream_read),
      .reg_downstream_write            (custom_dma_burst_4_downstream_write),
      .reg_downstream_writedata        (custom_dma_burst_4_downstream_writedata),
      .reset_n                         (custom_dma_burst_4_downstream_reset_n),
      .upstream_address                (custom_dma_burst_4_upstream_byteaddress),
      .upstream_burstcount             (custom_dma_burst_4_upstream_burstcount),
      .upstream_byteenable             (custom_dma_burst_4_upstream_byteenable),
      .upstream_debugaccess            (custom_dma_burst_4_upstream_debugaccess),
      .upstream_nativeaddress          (custom_dma_burst_4_upstream_address),
      .upstream_read                   (custom_dma_burst_4_upstream_read),
      .upstream_readdata               (custom_dma_burst_4_upstream_readdata),
      .upstream_readdatavalid          (custom_dma_burst_4_upstream_readdatavalid),
      .upstream_waitrequest            (custom_dma_burst_4_upstream_waitrequest),
      .upstream_write                  (custom_dma_burst_4_upstream_write),
      .upstream_writedata              (custom_dma_burst_4_upstream_writedata)
    );

  custom_dma_burst_5_upstream_arbitrator the_custom_dma_burst_5_upstream
    (
      .clk                                                                (system_clk),
      .custom_dma_burst_5_upstream_address                                (custom_dma_burst_5_upstream_address),
      .custom_dma_burst_5_upstream_burstcount                             (custom_dma_burst_5_upstream_burstcount),
      .custom_dma_burst_5_upstream_byteaddress                            (custom_dma_burst_5_upstream_byteaddress),
      .custom_dma_burst_5_upstream_byteenable                             (custom_dma_burst_5_upstream_byteenable),
      .custom_dma_burst_5_upstream_debugaccess                            (custom_dma_burst_5_upstream_debugaccess),
      .custom_dma_burst_5_upstream_read                                   (custom_dma_burst_5_upstream_read),
      .custom_dma_burst_5_upstream_readdata                               (custom_dma_burst_5_upstream_readdata),
      .custom_dma_burst_5_upstream_readdata_from_sa                       (custom_dma_burst_5_upstream_readdata_from_sa),
      .custom_dma_burst_5_upstream_readdatavalid                          (custom_dma_burst_5_upstream_readdatavalid),
      .custom_dma_burst_5_upstream_readdatavalid_from_sa                  (custom_dma_burst_5_upstream_readdatavalid_from_sa),
      .custom_dma_burst_5_upstream_waitrequest                            (custom_dma_burst_5_upstream_waitrequest),
      .custom_dma_burst_5_upstream_waitrequest_from_sa                    (custom_dma_burst_5_upstream_waitrequest_from_sa),
      .custom_dma_burst_5_upstream_write                                  (custom_dma_burst_5_upstream_write),
      .custom_dma_burst_5_upstream_writedata                              (custom_dma_burst_5_upstream_writedata),
      .d1_custom_dma_burst_5_upstream_end_xfer                            (d1_custom_dma_burst_5_upstream_end_xfer),
      .fir_dma_write_master_address_to_slave                              (fir_dma_write_master_address_to_slave),
      .fir_dma_write_master_burstcount                                    (fir_dma_write_master_burstcount),
      .fir_dma_write_master_byteenable                                    (fir_dma_write_master_byteenable),
      .fir_dma_write_master_granted_custom_dma_burst_5_upstream           (fir_dma_write_master_granted_custom_dma_burst_5_upstream),
      .fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream (fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream),
      .fir_dma_write_master_requests_custom_dma_burst_5_upstream          (fir_dma_write_master_requests_custom_dma_burst_5_upstream),
      .fir_dma_write_master_write                                         (fir_dma_write_master_write),
      .fir_dma_write_master_writedata                                     (fir_dma_write_master_writedata),
      .reset_n                                                            (system_clk_reset_n)
    );

  custom_dma_burst_5_downstream_arbitrator the_custom_dma_burst_5_downstream
    (
      .clk                                                                       (system_clk),
      .custom_dma_burst_5_downstream_address                                     (custom_dma_burst_5_downstream_address),
      .custom_dma_burst_5_downstream_address_to_slave                            (custom_dma_burst_5_downstream_address_to_slave),
      .custom_dma_burst_5_downstream_burstcount                                  (custom_dma_burst_5_downstream_burstcount),
      .custom_dma_burst_5_downstream_byteenable                                  (custom_dma_burst_5_downstream_byteenable),
      .custom_dma_burst_5_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_5_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_latency_counter                             (custom_dma_burst_5_downstream_latency_counter),
      .custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_read                                        (custom_dma_burst_5_downstream_read),
      .custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_5_downstream_readdata                                    (custom_dma_burst_5_downstream_readdata),
      .custom_dma_burst_5_downstream_readdatavalid                               (custom_dma_burst_5_downstream_readdatavalid),
      .custom_dma_burst_5_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_5_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_reset_n                                     (custom_dma_burst_5_downstream_reset_n),
      .custom_dma_burst_5_downstream_waitrequest                                 (custom_dma_burst_5_downstream_waitrequest),
      .custom_dma_burst_5_downstream_write                                       (custom_dma_burst_5_downstream_write),
      .custom_dma_burst_5_downstream_writedata                                   (custom_dma_burst_5_downstream_writedata),
      .d1_ddr_sdram_s1_end_xfer                                                  (d1_ddr_sdram_s1_end_xfer),
      .ddr_sdram_s1_readdata_from_sa                                             (ddr_sdram_s1_readdata_from_sa),
      .ddr_sdram_s1_waitrequest_n_from_sa                                        (ddr_sdram_s1_waitrequest_n_from_sa),
      .reset_n                                                                   (system_clk_reset_n)
    );

  custom_dma_burst_5 the_custom_dma_burst_5
    (
      .clk                         (system_clk),
      .downstream_address          (custom_dma_burst_5_downstream_address),
      .downstream_arbitrationshare (custom_dma_burst_5_downstream_arbitrationshare),
      .downstream_burstcount       (custom_dma_burst_5_downstream_burstcount),
      .downstream_byteenable       (custom_dma_burst_5_downstream_byteenable),
      .downstream_debugaccess      (custom_dma_burst_5_downstream_debugaccess),
      .downstream_nativeaddress    (custom_dma_burst_5_downstream_nativeaddress),
      .downstream_read             (custom_dma_burst_5_downstream_read),
      .downstream_readdata         (custom_dma_burst_5_downstream_readdata),
      .downstream_readdatavalid    (custom_dma_burst_5_downstream_readdatavalid),
      .downstream_waitrequest      (custom_dma_burst_5_downstream_waitrequest),
      .downstream_write            (custom_dma_burst_5_downstream_write),
      .downstream_writedata        (custom_dma_burst_5_downstream_writedata),
      .reset_n                     (custom_dma_burst_5_downstream_reset_n),
      .upstream_address            (custom_dma_burst_5_upstream_byteaddress),
      .upstream_burstcount         (custom_dma_burst_5_upstream_burstcount),
      .upstream_byteenable         (custom_dma_burst_5_upstream_byteenable),
      .upstream_debugaccess        (custom_dma_burst_5_upstream_debugaccess),
      .upstream_nativeaddress      (custom_dma_burst_5_upstream_address),
      .upstream_read               (custom_dma_burst_5_upstream_read),
      .upstream_readdata           (custom_dma_burst_5_upstream_readdata),
      .upstream_readdatavalid      (custom_dma_burst_5_upstream_readdatavalid),
      .upstream_waitrequest        (custom_dma_burst_5_upstream_waitrequest),
      .upstream_write              (custom_dma_burst_5_upstream_write),
      .upstream_writedata          (custom_dma_burst_5_upstream_writedata)
    );

  custom_dma_clock_0_in_arbitrator the_custom_dma_clock_0_in
    (
      .clk                                                        (system_clk),
      .custom_dma_clock_0_in_address                              (custom_dma_clock_0_in_address),
      .custom_dma_clock_0_in_byteenable                           (custom_dma_clock_0_in_byteenable),
      .custom_dma_clock_0_in_endofpacket                          (custom_dma_clock_0_in_endofpacket),
      .custom_dma_clock_0_in_endofpacket_from_sa                  (custom_dma_clock_0_in_endofpacket_from_sa),
      .custom_dma_clock_0_in_nativeaddress                        (custom_dma_clock_0_in_nativeaddress),
      .custom_dma_clock_0_in_read                                 (custom_dma_clock_0_in_read),
      .custom_dma_clock_0_in_readdata                             (custom_dma_clock_0_in_readdata),
      .custom_dma_clock_0_in_readdata_from_sa                     (custom_dma_clock_0_in_readdata_from_sa),
      .custom_dma_clock_0_in_reset_n                              (custom_dma_clock_0_in_reset_n),
      .custom_dma_clock_0_in_waitrequest                          (custom_dma_clock_0_in_waitrequest),
      .custom_dma_clock_0_in_waitrequest_from_sa                  (custom_dma_clock_0_in_waitrequest_from_sa),
      .custom_dma_clock_0_in_write                                (custom_dma_clock_0_in_write),
      .custom_dma_clock_0_in_writedata                            (custom_dma_clock_0_in_writedata),
      .d1_custom_dma_clock_0_in_end_xfer                          (d1_custom_dma_clock_0_in_end_xfer),
      .pipeline_bridge_m1_address_to_slave                        (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                              (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_byteenable                              (pipeline_bridge_m1_byteenable),
      .pipeline_bridge_m1_chipselect                              (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_granted_custom_dma_clock_0_in           (pipeline_bridge_m1_granted_custom_dma_clock_0_in),
      .pipeline_bridge_m1_latency_counter                         (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in (pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in),
      .pipeline_bridge_m1_read                                    (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in   (pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in),
      .pipeline_bridge_m1_requests_custom_dma_clock_0_in          (pipeline_bridge_m1_requests_custom_dma_clock_0_in),
      .pipeline_bridge_m1_write                                   (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                               (pipeline_bridge_m1_writedata),
      .reset_n                                                    (system_clk_reset_n)
    );

  custom_dma_clock_0_out_arbitrator the_custom_dma_clock_0_out
    (
      .clk                                             (external_clk),
      .custom_dma_clock_0_out_address                  (custom_dma_clock_0_out_address),
      .custom_dma_clock_0_out_address_to_slave         (custom_dma_clock_0_out_address_to_slave),
      .custom_dma_clock_0_out_byteenable               (custom_dma_clock_0_out_byteenable),
      .custom_dma_clock_0_out_granted_pll_s1           (custom_dma_clock_0_out_granted_pll_s1),
      .custom_dma_clock_0_out_qualified_request_pll_s1 (custom_dma_clock_0_out_qualified_request_pll_s1),
      .custom_dma_clock_0_out_read                     (custom_dma_clock_0_out_read),
      .custom_dma_clock_0_out_read_data_valid_pll_s1   (custom_dma_clock_0_out_read_data_valid_pll_s1),
      .custom_dma_clock_0_out_readdata                 (custom_dma_clock_0_out_readdata),
      .custom_dma_clock_0_out_requests_pll_s1          (custom_dma_clock_0_out_requests_pll_s1),
      .custom_dma_clock_0_out_reset_n                  (custom_dma_clock_0_out_reset_n),
      .custom_dma_clock_0_out_waitrequest              (custom_dma_clock_0_out_waitrequest),
      .custom_dma_clock_0_out_write                    (custom_dma_clock_0_out_write),
      .custom_dma_clock_0_out_writedata                (custom_dma_clock_0_out_writedata),
      .d1_pll_s1_end_xfer                              (d1_pll_s1_end_xfer),
      .pll_s1_readdata_from_sa                         (pll_s1_readdata_from_sa),
      .reset_n                                         (external_clk_reset_n)
    );

  custom_dma_clock_0 the_custom_dma_clock_0
    (
      .master_address       (custom_dma_clock_0_out_address),
      .master_byteenable    (custom_dma_clock_0_out_byteenable),
      .master_clk           (external_clk),
      .master_endofpacket   (custom_dma_clock_0_out_endofpacket),
      .master_nativeaddress (custom_dma_clock_0_out_nativeaddress),
      .master_read          (custom_dma_clock_0_out_read),
      .master_readdata      (custom_dma_clock_0_out_readdata),
      .master_reset_n       (custom_dma_clock_0_out_reset_n),
      .master_waitrequest   (custom_dma_clock_0_out_waitrequest),
      .master_write         (custom_dma_clock_0_out_write),
      .master_writedata     (custom_dma_clock_0_out_writedata),
      .slave_address        (custom_dma_clock_0_in_address),
      .slave_byteenable     (custom_dma_clock_0_in_byteenable),
      .slave_clk            (system_clk),
      .slave_endofpacket    (custom_dma_clock_0_in_endofpacket),
      .slave_nativeaddress  (custom_dma_clock_0_in_nativeaddress),
      .slave_read           (custom_dma_clock_0_in_read),
      .slave_readdata       (custom_dma_clock_0_in_readdata),
      .slave_reset_n        (custom_dma_clock_0_in_reset_n),
      .slave_waitrequest    (custom_dma_clock_0_in_waitrequest),
      .slave_write          (custom_dma_clock_0_in_write),
      .slave_writedata      (custom_dma_clock_0_in_writedata)
    );

  ddr_sdram_s1_arbitrator the_ddr_sdram_s1
    (
      .clk                                                                       (system_clk),
      .custom_dma_burst_3_downstream_address_to_slave                            (custom_dma_burst_3_downstream_address_to_slave),
      .custom_dma_burst_3_downstream_arbitrationshare                            (custom_dma_burst_3_downstream_arbitrationshare),
      .custom_dma_burst_3_downstream_burstcount                                  (custom_dma_burst_3_downstream_burstcount),
      .custom_dma_burst_3_downstream_byteenable                                  (custom_dma_burst_3_downstream_byteenable),
      .custom_dma_burst_3_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_3_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_latency_counter                             (custom_dma_burst_3_downstream_latency_counter),
      .custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_3_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_read                                        (custom_dma_burst_3_downstream_read),
      .custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_3_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_3_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_3_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_3_downstream_write                                       (custom_dma_burst_3_downstream_write),
      .custom_dma_burst_3_downstream_writedata                                   (custom_dma_burst_3_downstream_writedata),
      .custom_dma_burst_4_downstream_address_to_slave                            (custom_dma_burst_4_downstream_address_to_slave),
      .custom_dma_burst_4_downstream_arbitrationshare                            (custom_dma_burst_4_downstream_arbitrationshare),
      .custom_dma_burst_4_downstream_burstcount                                  (custom_dma_burst_4_downstream_burstcount),
      .custom_dma_burst_4_downstream_byteenable                                  (custom_dma_burst_4_downstream_byteenable),
      .custom_dma_burst_4_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_4_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_latency_counter                             (custom_dma_burst_4_downstream_latency_counter),
      .custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_4_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_read                                        (custom_dma_burst_4_downstream_read),
      .custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_4_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_4_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_4_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_4_downstream_write                                       (custom_dma_burst_4_downstream_write),
      .custom_dma_burst_4_downstream_writedata                                   (custom_dma_burst_4_downstream_writedata),
      .custom_dma_burst_5_downstream_address_to_slave                            (custom_dma_burst_5_downstream_address_to_slave),
      .custom_dma_burst_5_downstream_arbitrationshare                            (custom_dma_burst_5_downstream_arbitrationshare),
      .custom_dma_burst_5_downstream_burstcount                                  (custom_dma_burst_5_downstream_burstcount),
      .custom_dma_burst_5_downstream_byteenable                                  (custom_dma_burst_5_downstream_byteenable),
      .custom_dma_burst_5_downstream_granted_ddr_sdram_s1                        (custom_dma_burst_5_downstream_granted_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_latency_counter                             (custom_dma_burst_5_downstream_latency_counter),
      .custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1              (custom_dma_burst_5_downstream_qualified_request_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_read                                        (custom_dma_burst_5_downstream_read),
      .custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1                (custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register (custom_dma_burst_5_downstream_read_data_valid_ddr_sdram_s1_shift_register),
      .custom_dma_burst_5_downstream_requests_ddr_sdram_s1                       (custom_dma_burst_5_downstream_requests_ddr_sdram_s1),
      .custom_dma_burst_5_downstream_write                                       (custom_dma_burst_5_downstream_write),
      .custom_dma_burst_5_downstream_writedata                                   (custom_dma_burst_5_downstream_writedata),
      .d1_ddr_sdram_s1_end_xfer                                                  (d1_ddr_sdram_s1_end_xfer),
      .ddr_sdram_s1_address                                                      (ddr_sdram_s1_address),
      .ddr_sdram_s1_beginbursttransfer                                           (ddr_sdram_s1_beginbursttransfer),
      .ddr_sdram_s1_burstcount                                                   (ddr_sdram_s1_burstcount),
      .ddr_sdram_s1_byteenable                                                   (ddr_sdram_s1_byteenable),
      .ddr_sdram_s1_read                                                         (ddr_sdram_s1_read),
      .ddr_sdram_s1_readdata                                                     (ddr_sdram_s1_readdata),
      .ddr_sdram_s1_readdata_from_sa                                             (ddr_sdram_s1_readdata_from_sa),
      .ddr_sdram_s1_readdatavalid                                                (ddr_sdram_s1_readdatavalid),
      .ddr_sdram_s1_reset_n                                                      (ddr_sdram_s1_reset_n),
      .ddr_sdram_s1_waitrequest_n                                                (ddr_sdram_s1_waitrequest_n),
      .ddr_sdram_s1_waitrequest_n_from_sa                                        (ddr_sdram_s1_waitrequest_n_from_sa),
      .ddr_sdram_s1_write                                                        (ddr_sdram_s1_write),
      .ddr_sdram_s1_writedata                                                    (ddr_sdram_s1_writedata),
      .reset_n                                                                   (system_clk_reset_n)
    );

  ddr_sdram the_ddr_sdram
    (
      .clk                 (system_clk),
      .clk_to_sdram        (clk_to_sdram_from_the_ddr_sdram),
      .clk_to_sdram_n      (clk_to_sdram_n_from_the_ddr_sdram),
      .ddr_a               (ddr_a_from_the_ddr_sdram),
      .ddr_ba              (ddr_ba_from_the_ddr_sdram),
      .ddr_cas_n           (ddr_cas_n_from_the_ddr_sdram),
      .ddr_cke             (ddr_cke_from_the_ddr_sdram),
      .ddr_cs_n            (ddr_cs_n_from_the_ddr_sdram),
      .ddr_dm              (ddr_dm_from_the_ddr_sdram),
      .ddr_dq              (ddr_dq_to_and_from_the_ddr_sdram),
      .ddr_dqs             (ddr_dqs_to_and_from_the_ddr_sdram),
      .ddr_ras_n           (ddr_ras_n_from_the_ddr_sdram),
      .ddr_we_n            (ddr_we_n_from_the_ddr_sdram),
      .dqs_delay_ctrl      (dqs_delay_ctrl_to_the_ddr_sdram),
      .dqsupdate           (dqsupdate_to_the_ddr_sdram),
      .local_addr          (ddr_sdram_s1_address),
      .local_be            (ddr_sdram_s1_byteenable),
      .local_burstbegin    (ddr_sdram_s1_beginbursttransfer),
      .local_rdata         (ddr_sdram_s1_readdata),
      .local_rdata_valid   (ddr_sdram_s1_readdatavalid),
      .local_read_req      (ddr_sdram_s1_read),
      .local_ready         (ddr_sdram_s1_waitrequest_n),
      .local_size          (ddr_sdram_s1_burstcount),
      .local_wdata         (ddr_sdram_s1_writedata),
      .local_write_req     (ddr_sdram_s1_write),
      .reset_n             (ddr_sdram_s1_reset_n),
      .stratix_dll_control (stratix_dll_control_from_the_ddr_sdram),
      .write_clk           (write_clk_to_the_ddr_sdram)
    );

  ext_ssram_bus_avalon_slave_arbitrator the_ext_ssram_bus_avalon_slave
    (
      .adsc_n_to_the_ext_ssram                                      (adsc_n_to_the_ext_ssram),
      .bw_n_to_the_ext_ssram                                        (bw_n_to_the_ext_ssram),
      .bwe_n_to_the_ext_ssram                                       (bwe_n_to_the_ext_ssram),
      .chipenable1_n_to_the_ext_ssram                               (chipenable1_n_to_the_ext_ssram),
      .clk                                                          (system_clk),
      .custom_dma_burst_0_downstream_address_to_slave               (custom_dma_burst_0_downstream_address_to_slave),
      .custom_dma_burst_0_downstream_arbitrationshare               (custom_dma_burst_0_downstream_arbitrationshare),
      .custom_dma_burst_0_downstream_burstcount                     (custom_dma_burst_0_downstream_burstcount),
      .custom_dma_burst_0_downstream_byteenable                     (custom_dma_burst_0_downstream_byteenable),
      .custom_dma_burst_0_downstream_granted_ext_ssram_s1           (custom_dma_burst_0_downstream_granted_ext_ssram_s1),
      .custom_dma_burst_0_downstream_latency_counter                (custom_dma_burst_0_downstream_latency_counter),
      .custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1 (custom_dma_burst_0_downstream_qualified_request_ext_ssram_s1),
      .custom_dma_burst_0_downstream_read                           (custom_dma_burst_0_downstream_read),
      .custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1   (custom_dma_burst_0_downstream_read_data_valid_ext_ssram_s1),
      .custom_dma_burst_0_downstream_requests_ext_ssram_s1          (custom_dma_burst_0_downstream_requests_ext_ssram_s1),
      .custom_dma_burst_0_downstream_write                          (custom_dma_burst_0_downstream_write),
      .custom_dma_burst_0_downstream_writedata                      (custom_dma_burst_0_downstream_writedata),
      .d1_ext_ssram_bus_avalon_slave_end_xfer                       (d1_ext_ssram_bus_avalon_slave_end_xfer),
      .ext_ssram_bus_address                                        (ext_ssram_bus_address),
      .ext_ssram_bus_data                                           (ext_ssram_bus_data),
      .fir_dma_read_master_address_to_slave                         (fir_dma_read_master_address_to_slave),
      .fir_dma_read_master_granted_ext_ssram_s1                     (fir_dma_read_master_granted_ext_ssram_s1),
      .fir_dma_read_master_latency_counter                          (fir_dma_read_master_latency_counter),
      .fir_dma_read_master_qualified_request_ext_ssram_s1           (fir_dma_read_master_qualified_request_ext_ssram_s1),
      .fir_dma_read_master_read                                     (fir_dma_read_master_read),
      .fir_dma_read_master_read_data_valid_ext_ssram_s1             (fir_dma_read_master_read_data_valid_ext_ssram_s1),
      .fir_dma_read_master_requests_ext_ssram_s1                    (fir_dma_read_master_requests_ext_ssram_s1),
      .incoming_ext_ssram_bus_data                                  (incoming_ext_ssram_bus_data),
      .outputenable_n_to_the_ext_ssram                              (outputenable_n_to_the_ext_ssram),
      .reset_n                                                      (system_clk_reset_n)
    );

  fir_dma_control_arbitrator the_fir_dma_control
    (
      .clk                                                  (system_clk),
      .d1_fir_dma_control_end_xfer                          (d1_fir_dma_control_end_xfer),
      .fir_dma_control_address                              (fir_dma_control_address),
      .fir_dma_control_byteenable                           (fir_dma_control_byteenable),
      .fir_dma_control_irq                                  (fir_dma_control_irq),
      .fir_dma_control_irq_from_sa                          (fir_dma_control_irq_from_sa),
      .fir_dma_control_read                                 (fir_dma_control_read),
      .fir_dma_control_readdata                             (fir_dma_control_readdata),
      .fir_dma_control_readdata_from_sa                     (fir_dma_control_readdata_from_sa),
      .fir_dma_control_reset                                (fir_dma_control_reset),
      .fir_dma_control_write                                (fir_dma_control_write),
      .fir_dma_control_writedata                            (fir_dma_control_writedata),
      .pipeline_bridge_m1_address_to_slave                  (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                        (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_byteenable                        (pipeline_bridge_m1_byteenable),
      .pipeline_bridge_m1_chipselect                        (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_granted_fir_dma_control           (pipeline_bridge_m1_granted_fir_dma_control),
      .pipeline_bridge_m1_latency_counter                   (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_fir_dma_control (pipeline_bridge_m1_qualified_request_fir_dma_control),
      .pipeline_bridge_m1_read                              (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_fir_dma_control   (pipeline_bridge_m1_read_data_valid_fir_dma_control),
      .pipeline_bridge_m1_requests_fir_dma_control          (pipeline_bridge_m1_requests_fir_dma_control),
      .pipeline_bridge_m1_write                             (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                         (pipeline_bridge_m1_writedata),
      .reset_n                                              (system_clk_reset_n)
    );

  fir_dma_read_master_arbitrator the_fir_dma_read_master
    (
      .clk                                                (system_clk),
      .d1_ext_ssram_bus_avalon_slave_end_xfer             (d1_ext_ssram_bus_avalon_slave_end_xfer),
      .fir_dma_read_master_address                        (fir_dma_read_master_address),
      .fir_dma_read_master_address_to_slave               (fir_dma_read_master_address_to_slave),
      .fir_dma_read_master_byteenable                     (fir_dma_read_master_byteenable),
      .fir_dma_read_master_granted_ext_ssram_s1           (fir_dma_read_master_granted_ext_ssram_s1),
      .fir_dma_read_master_latency_counter                (fir_dma_read_master_latency_counter),
      .fir_dma_read_master_qualified_request_ext_ssram_s1 (fir_dma_read_master_qualified_request_ext_ssram_s1),
      .fir_dma_read_master_read                           (fir_dma_read_master_read),
      .fir_dma_read_master_read_data_valid_ext_ssram_s1   (fir_dma_read_master_read_data_valid_ext_ssram_s1),
      .fir_dma_read_master_readdata                       (fir_dma_read_master_readdata),
      .fir_dma_read_master_readdatavalid                  (fir_dma_read_master_readdatavalid),
      .fir_dma_read_master_requests_ext_ssram_s1          (fir_dma_read_master_requests_ext_ssram_s1),
      .fir_dma_read_master_waitrequest                    (fir_dma_read_master_waitrequest),
      .incoming_ext_ssram_bus_data                        (incoming_ext_ssram_bus_data),
      .reset_n                                            (system_clk_reset_n)
    );

  fir_dma_write_master_arbitrator the_fir_dma_write_master
    (
      .clk                                                                (system_clk),
      .custom_dma_burst_5_upstream_waitrequest_from_sa                    (custom_dma_burst_5_upstream_waitrequest_from_sa),
      .d1_custom_dma_burst_5_upstream_end_xfer                            (d1_custom_dma_burst_5_upstream_end_xfer),
      .fir_dma_write_master_address                                       (fir_dma_write_master_address),
      .fir_dma_write_master_address_to_slave                              (fir_dma_write_master_address_to_slave),
      .fir_dma_write_master_burstcount                                    (fir_dma_write_master_burstcount),
      .fir_dma_write_master_byteenable                                    (fir_dma_write_master_byteenable),
      .fir_dma_write_master_granted_custom_dma_burst_5_upstream           (fir_dma_write_master_granted_custom_dma_burst_5_upstream),
      .fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream (fir_dma_write_master_qualified_request_custom_dma_burst_5_upstream),
      .fir_dma_write_master_requests_custom_dma_burst_5_upstream          (fir_dma_write_master_requests_custom_dma_burst_5_upstream),
      .fir_dma_write_master_waitrequest                                   (fir_dma_write_master_waitrequest),
      .fir_dma_write_master_write                                         (fir_dma_write_master_write),
      .fir_dma_write_master_writedata                                     (fir_dma_write_master_writedata),
      .reset_n                                                            (system_clk_reset_n)
    );

  fir_dma the_fir_dma
    (
      .clk                       (system_clk),
      .read_master_address       (fir_dma_read_master_address),
      .read_master_byteenable    (fir_dma_read_master_byteenable),
      .read_master_read          (fir_dma_read_master_read),
      .read_master_readdata      (fir_dma_read_master_readdata),
      .read_master_readdatavalid (fir_dma_read_master_readdatavalid),
      .read_master_waitrequest   (fir_dma_read_master_waitrequest),
      .reset                     (fir_dma_control_reset),
      .slave_address             (fir_dma_control_address),
      .slave_byteenable          (fir_dma_control_byteenable),
      .slave_irq                 (fir_dma_control_irq),
      .slave_read                (fir_dma_control_read),
      .slave_readdata            (fir_dma_control_readdata),
      .slave_write               (fir_dma_control_write),
      .slave_writedata           (fir_dma_control_writedata),
      .write_master_address      (fir_dma_write_master_address),
      .write_master_burstcount   (fir_dma_write_master_burstcount),
      .write_master_byteenable   (fir_dma_write_master_byteenable),
      .write_master_waitrequest  (fir_dma_write_master_waitrequest),
      .write_master_write        (fir_dma_write_master_write),
      .write_master_writedata    (fir_dma_write_master_writedata)
    );

  jtag_uart_avalon_jtag_slave_arbitrator the_jtag_uart_avalon_jtag_slave
    (
      .clk                                                              (system_clk),
      .d1_jtag_uart_avalon_jtag_slave_end_xfer                          (d1_jtag_uart_avalon_jtag_slave_end_xfer),
      .jtag_uart_avalon_jtag_slave_address                              (jtag_uart_avalon_jtag_slave_address),
      .jtag_uart_avalon_jtag_slave_chipselect                           (jtag_uart_avalon_jtag_slave_chipselect),
      .jtag_uart_avalon_jtag_slave_dataavailable                        (jtag_uart_avalon_jtag_slave_dataavailable),
      .jtag_uart_avalon_jtag_slave_dataavailable_from_sa                (jtag_uart_avalon_jtag_slave_dataavailable_from_sa),
      .jtag_uart_avalon_jtag_slave_irq                                  (jtag_uart_avalon_jtag_slave_irq),
      .jtag_uart_avalon_jtag_slave_irq_from_sa                          (jtag_uart_avalon_jtag_slave_irq_from_sa),
      .jtag_uart_avalon_jtag_slave_read_n                               (jtag_uart_avalon_jtag_slave_read_n),
      .jtag_uart_avalon_jtag_slave_readdata                             (jtag_uart_avalon_jtag_slave_readdata),
      .jtag_uart_avalon_jtag_slave_readdata_from_sa                     (jtag_uart_avalon_jtag_slave_readdata_from_sa),
      .jtag_uart_avalon_jtag_slave_readyfordata                         (jtag_uart_avalon_jtag_slave_readyfordata),
      .jtag_uart_avalon_jtag_slave_readyfordata_from_sa                 (jtag_uart_avalon_jtag_slave_readyfordata_from_sa),
      .jtag_uart_avalon_jtag_slave_reset_n                              (jtag_uart_avalon_jtag_slave_reset_n),
      .jtag_uart_avalon_jtag_slave_waitrequest                          (jtag_uart_avalon_jtag_slave_waitrequest),
      .jtag_uart_avalon_jtag_slave_waitrequest_from_sa                  (jtag_uart_avalon_jtag_slave_waitrequest_from_sa),
      .jtag_uart_avalon_jtag_slave_write_n                              (jtag_uart_avalon_jtag_slave_write_n),
      .jtag_uart_avalon_jtag_slave_writedata                            (jtag_uart_avalon_jtag_slave_writedata),
      .pipeline_bridge_m1_address_to_slave                              (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                                    (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_chipselect                                    (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave           (pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_latency_counter                               (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave (pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_read                                          (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave   (pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave          (pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_write                                         (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                                     (pipeline_bridge_m1_writedata),
      .reset_n                                                          (system_clk_reset_n)
    );

  jtag_uart the_jtag_uart
    (
      .av_address     (jtag_uart_avalon_jtag_slave_address),
      .av_chipselect  (jtag_uart_avalon_jtag_slave_chipselect),
      .av_irq         (jtag_uart_avalon_jtag_slave_irq),
      .av_read_n      (jtag_uart_avalon_jtag_slave_read_n),
      .av_readdata    (jtag_uart_avalon_jtag_slave_readdata),
      .av_waitrequest (jtag_uart_avalon_jtag_slave_waitrequest),
      .av_write_n     (jtag_uart_avalon_jtag_slave_write_n),
      .av_writedata   (jtag_uart_avalon_jtag_slave_writedata),
      .clk            (system_clk),
      .dataavailable  (jtag_uart_avalon_jtag_slave_dataavailable),
      .readyfordata   (jtag_uart_avalon_jtag_slave_readyfordata),
      .rst_n          (jtag_uart_avalon_jtag_slave_reset_n)
    );

  pipeline_bridge_s1_arbitrator the_pipeline_bridge_s1
    (
      .clk                                                                             (system_clk),
      .custom_dma_burst_1_downstream_address_to_slave                                  (custom_dma_burst_1_downstream_address_to_slave),
      .custom_dma_burst_1_downstream_arbitrationshare                                  (custom_dma_burst_1_downstream_arbitrationshare),
      .custom_dma_burst_1_downstream_burstcount                                        (custom_dma_burst_1_downstream_burstcount),
      .custom_dma_burst_1_downstream_byteenable                                        (custom_dma_burst_1_downstream_byteenable),
      .custom_dma_burst_1_downstream_debugaccess                                       (custom_dma_burst_1_downstream_debugaccess),
      .custom_dma_burst_1_downstream_granted_pipeline_bridge_s1                        (custom_dma_burst_1_downstream_granted_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_latency_counter                                   (custom_dma_burst_1_downstream_latency_counter),
      .custom_dma_burst_1_downstream_nativeaddress                                     (custom_dma_burst_1_downstream_nativeaddress),
      .custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1              (custom_dma_burst_1_downstream_qualified_request_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_read                                              (custom_dma_burst_1_downstream_read),
      .custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1                (custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register (custom_dma_burst_1_downstream_read_data_valid_pipeline_bridge_s1_shift_register),
      .custom_dma_burst_1_downstream_requests_pipeline_bridge_s1                       (custom_dma_burst_1_downstream_requests_pipeline_bridge_s1),
      .custom_dma_burst_1_downstream_write                                             (custom_dma_burst_1_downstream_write),
      .custom_dma_burst_1_downstream_writedata                                         (custom_dma_burst_1_downstream_writedata),
      .custom_dma_burst_2_downstream_address_to_slave                                  (custom_dma_burst_2_downstream_address_to_slave),
      .custom_dma_burst_2_downstream_arbitrationshare                                  (custom_dma_burst_2_downstream_arbitrationshare),
      .custom_dma_burst_2_downstream_burstcount                                        (custom_dma_burst_2_downstream_burstcount),
      .custom_dma_burst_2_downstream_byteenable                                        (custom_dma_burst_2_downstream_byteenable),
      .custom_dma_burst_2_downstream_debugaccess                                       (custom_dma_burst_2_downstream_debugaccess),
      .custom_dma_burst_2_downstream_granted_pipeline_bridge_s1                        (custom_dma_burst_2_downstream_granted_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_latency_counter                                   (custom_dma_burst_2_downstream_latency_counter),
      .custom_dma_burst_2_downstream_nativeaddress                                     (custom_dma_burst_2_downstream_nativeaddress),
      .custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1              (custom_dma_burst_2_downstream_qualified_request_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_read                                              (custom_dma_burst_2_downstream_read),
      .custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1                (custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register (custom_dma_burst_2_downstream_read_data_valid_pipeline_bridge_s1_shift_register),
      .custom_dma_burst_2_downstream_requests_pipeline_bridge_s1                       (custom_dma_burst_2_downstream_requests_pipeline_bridge_s1),
      .custom_dma_burst_2_downstream_write                                             (custom_dma_burst_2_downstream_write),
      .custom_dma_burst_2_downstream_writedata                                         (custom_dma_burst_2_downstream_writedata),
      .d1_pipeline_bridge_s1_end_xfer                                                  (d1_pipeline_bridge_s1_end_xfer),
      .pipeline_bridge_s1_address                                                      (pipeline_bridge_s1_address),
      .pipeline_bridge_s1_arbiterlock                                                  (pipeline_bridge_s1_arbiterlock),
      .pipeline_bridge_s1_arbiterlock2                                                 (pipeline_bridge_s1_arbiterlock2),
      .pipeline_bridge_s1_burstcount                                                   (pipeline_bridge_s1_burstcount),
      .pipeline_bridge_s1_byteenable                                                   (pipeline_bridge_s1_byteenable),
      .pipeline_bridge_s1_chipselect                                                   (pipeline_bridge_s1_chipselect),
      .pipeline_bridge_s1_debugaccess                                                  (pipeline_bridge_s1_debugaccess),
      .pipeline_bridge_s1_endofpacket                                                  (pipeline_bridge_s1_endofpacket),
      .pipeline_bridge_s1_endofpacket_from_sa                                          (pipeline_bridge_s1_endofpacket_from_sa),
      .pipeline_bridge_s1_nativeaddress                                                (pipeline_bridge_s1_nativeaddress),
      .pipeline_bridge_s1_read                                                         (pipeline_bridge_s1_read),
      .pipeline_bridge_s1_readdata                                                     (pipeline_bridge_s1_readdata),
      .pipeline_bridge_s1_readdata_from_sa                                             (pipeline_bridge_s1_readdata_from_sa),
      .pipeline_bridge_s1_readdatavalid                                                (pipeline_bridge_s1_readdatavalid),
      .pipeline_bridge_s1_reset_n                                                      (pipeline_bridge_s1_reset_n),
      .pipeline_bridge_s1_waitrequest                                                  (pipeline_bridge_s1_waitrequest),
      .pipeline_bridge_s1_waitrequest_from_sa                                          (pipeline_bridge_s1_waitrequest_from_sa),
      .pipeline_bridge_s1_write                                                        (pipeline_bridge_s1_write),
      .pipeline_bridge_s1_writedata                                                    (pipeline_bridge_s1_writedata),
      .reset_n                                                                         (system_clk_reset_n)
    );

  pipeline_bridge_m1_arbitrator the_pipeline_bridge_m1
    (
      .clk                                                              (system_clk),
      .cpu_jtag_debug_module_readdata_from_sa                           (cpu_jtag_debug_module_readdata_from_sa),
      .custom_dma_clock_0_in_endofpacket_from_sa                        (custom_dma_clock_0_in_endofpacket_from_sa),
      .custom_dma_clock_0_in_readdata_from_sa                           (custom_dma_clock_0_in_readdata_from_sa),
      .custom_dma_clock_0_in_waitrequest_from_sa                        (custom_dma_clock_0_in_waitrequest_from_sa),
      .d1_cpu_jtag_debug_module_end_xfer                                (d1_cpu_jtag_debug_module_end_xfer),
      .d1_custom_dma_clock_0_in_end_xfer                                (d1_custom_dma_clock_0_in_end_xfer),
      .d1_fir_dma_control_end_xfer                                      (d1_fir_dma_control_end_xfer),
      .d1_jtag_uart_avalon_jtag_slave_end_xfer                          (d1_jtag_uart_avalon_jtag_slave_end_xfer),
      .d1_sysid_control_slave_end_xfer                                  (d1_sysid_control_slave_end_xfer),
      .d1_timestamp_timer_s1_end_xfer                                   (d1_timestamp_timer_s1_end_xfer),
      .fir_dma_control_readdata_from_sa                                 (fir_dma_control_readdata_from_sa),
      .jtag_uart_avalon_jtag_slave_readdata_from_sa                     (jtag_uart_avalon_jtag_slave_readdata_from_sa),
      .jtag_uart_avalon_jtag_slave_waitrequest_from_sa                  (jtag_uart_avalon_jtag_slave_waitrequest_from_sa),
      .pipeline_bridge_m1_address                                       (pipeline_bridge_m1_address),
      .pipeline_bridge_m1_address_to_slave                              (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                                    (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_byteenable                                    (pipeline_bridge_m1_byteenable),
      .pipeline_bridge_m1_chipselect                                    (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_endofpacket                                   (pipeline_bridge_m1_endofpacket),
      .pipeline_bridge_m1_granted_cpu_jtag_debug_module                 (pipeline_bridge_m1_granted_cpu_jtag_debug_module),
      .pipeline_bridge_m1_granted_custom_dma_clock_0_in                 (pipeline_bridge_m1_granted_custom_dma_clock_0_in),
      .pipeline_bridge_m1_granted_fir_dma_control                       (pipeline_bridge_m1_granted_fir_dma_control),
      .pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave           (pipeline_bridge_m1_granted_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_granted_sysid_control_slave                   (pipeline_bridge_m1_granted_sysid_control_slave),
      .pipeline_bridge_m1_granted_timestamp_timer_s1                    (pipeline_bridge_m1_granted_timestamp_timer_s1),
      .pipeline_bridge_m1_latency_counter                               (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module       (pipeline_bridge_m1_qualified_request_cpu_jtag_debug_module),
      .pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in       (pipeline_bridge_m1_qualified_request_custom_dma_clock_0_in),
      .pipeline_bridge_m1_qualified_request_fir_dma_control             (pipeline_bridge_m1_qualified_request_fir_dma_control),
      .pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave (pipeline_bridge_m1_qualified_request_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_qualified_request_sysid_control_slave         (pipeline_bridge_m1_qualified_request_sysid_control_slave),
      .pipeline_bridge_m1_qualified_request_timestamp_timer_s1          (pipeline_bridge_m1_qualified_request_timestamp_timer_s1),
      .pipeline_bridge_m1_read                                          (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module         (pipeline_bridge_m1_read_data_valid_cpu_jtag_debug_module),
      .pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in         (pipeline_bridge_m1_read_data_valid_custom_dma_clock_0_in),
      .pipeline_bridge_m1_read_data_valid_fir_dma_control               (pipeline_bridge_m1_read_data_valid_fir_dma_control),
      .pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave   (pipeline_bridge_m1_read_data_valid_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_read_data_valid_sysid_control_slave           (pipeline_bridge_m1_read_data_valid_sysid_control_slave),
      .pipeline_bridge_m1_read_data_valid_timestamp_timer_s1            (pipeline_bridge_m1_read_data_valid_timestamp_timer_s1),
      .pipeline_bridge_m1_readdata                                      (pipeline_bridge_m1_readdata),
      .pipeline_bridge_m1_readdatavalid                                 (pipeline_bridge_m1_readdatavalid),
      .pipeline_bridge_m1_requests_cpu_jtag_debug_module                (pipeline_bridge_m1_requests_cpu_jtag_debug_module),
      .pipeline_bridge_m1_requests_custom_dma_clock_0_in                (pipeline_bridge_m1_requests_custom_dma_clock_0_in),
      .pipeline_bridge_m1_requests_fir_dma_control                      (pipeline_bridge_m1_requests_fir_dma_control),
      .pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave          (pipeline_bridge_m1_requests_jtag_uart_avalon_jtag_slave),
      .pipeline_bridge_m1_requests_sysid_control_slave                  (pipeline_bridge_m1_requests_sysid_control_slave),
      .pipeline_bridge_m1_requests_timestamp_timer_s1                   (pipeline_bridge_m1_requests_timestamp_timer_s1),
      .pipeline_bridge_m1_waitrequest                                   (pipeline_bridge_m1_waitrequest),
      .pipeline_bridge_m1_write                                         (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                                     (pipeline_bridge_m1_writedata),
      .reset_n                                                          (system_clk_reset_n),
      .sysid_control_slave_readdata_from_sa                             (sysid_control_slave_readdata_from_sa),
      .timestamp_timer_s1_readdata_from_sa                              (timestamp_timer_s1_readdata_from_sa)
    );

  pipeline_bridge the_pipeline_bridge
    (
      .clk              (system_clk),
      .m1_address       (pipeline_bridge_m1_address),
      .m1_burstcount    (pipeline_bridge_m1_burstcount),
      .m1_byteenable    (pipeline_bridge_m1_byteenable),
      .m1_chipselect    (pipeline_bridge_m1_chipselect),
      .m1_debugaccess   (pipeline_bridge_m1_debugaccess),
      .m1_endofpacket   (pipeline_bridge_m1_endofpacket),
      .m1_read          (pipeline_bridge_m1_read),
      .m1_readdata      (pipeline_bridge_m1_readdata),
      .m1_readdatavalid (pipeline_bridge_m1_readdatavalid),
      .m1_waitrequest   (pipeline_bridge_m1_waitrequest),
      .m1_write         (pipeline_bridge_m1_write),
      .m1_writedata     (pipeline_bridge_m1_writedata),
      .reset_n          (pipeline_bridge_s1_reset_n),
      .s1_address       (pipeline_bridge_s1_address),
      .s1_arbiterlock   (pipeline_bridge_s1_arbiterlock),
      .s1_arbiterlock2  (pipeline_bridge_s1_arbiterlock2),
      .s1_burstcount    (pipeline_bridge_s1_burstcount),
      .s1_byteenable    (pipeline_bridge_s1_byteenable),
      .s1_chipselect    (pipeline_bridge_s1_chipselect),
      .s1_debugaccess   (pipeline_bridge_s1_debugaccess),
      .s1_endofpacket   (pipeline_bridge_s1_endofpacket),
      .s1_nativeaddress (pipeline_bridge_s1_nativeaddress),
      .s1_read          (pipeline_bridge_s1_read),
      .s1_readdata      (pipeline_bridge_s1_readdata),
      .s1_readdatavalid (pipeline_bridge_s1_readdatavalid),
      .s1_waitrequest   (pipeline_bridge_s1_waitrequest),
      .s1_write         (pipeline_bridge_s1_write),
      .s1_writedata     (pipeline_bridge_s1_writedata)
    );

  pll_s1_arbitrator the_pll_s1
    (
      .clk                                             (external_clk),
      .custom_dma_clock_0_out_address_to_slave         (custom_dma_clock_0_out_address_to_slave),
      .custom_dma_clock_0_out_granted_pll_s1           (custom_dma_clock_0_out_granted_pll_s1),
      .custom_dma_clock_0_out_nativeaddress            (custom_dma_clock_0_out_nativeaddress),
      .custom_dma_clock_0_out_qualified_request_pll_s1 (custom_dma_clock_0_out_qualified_request_pll_s1),
      .custom_dma_clock_0_out_read                     (custom_dma_clock_0_out_read),
      .custom_dma_clock_0_out_read_data_valid_pll_s1   (custom_dma_clock_0_out_read_data_valid_pll_s1),
      .custom_dma_clock_0_out_requests_pll_s1          (custom_dma_clock_0_out_requests_pll_s1),
      .custom_dma_clock_0_out_write                    (custom_dma_clock_0_out_write),
      .custom_dma_clock_0_out_writedata                (custom_dma_clock_0_out_writedata),
      .d1_pll_s1_end_xfer                              (d1_pll_s1_end_xfer),
      .pll_s1_address                                  (pll_s1_address),
      .pll_s1_chipselect                               (pll_s1_chipselect),
      .pll_s1_read                                     (pll_s1_read),
      .pll_s1_readdata                                 (pll_s1_readdata),
      .pll_s1_readdata_from_sa                         (pll_s1_readdata_from_sa),
      .pll_s1_reset_n                                  (pll_s1_reset_n),
      .pll_s1_resetrequest                             (pll_s1_resetrequest),
      .pll_s1_resetrequest_from_sa                     (pll_s1_resetrequest_from_sa),
      .pll_s1_write                                    (pll_s1_write),
      .pll_s1_writedata                                (pll_s1_writedata),
      .reset_n                                         (external_clk_reset_n)
    );

  //system_clk out_clk assignment, which is an e_assign
  assign system_clk = out_clk_pll_c0;

  //ssram_clk out_clk assignment, which is an e_assign
  assign ssram_clk = out_clk_pll_c1;

  //sdram_write_clk out_clk assignment, which is an e_assign
  assign sdram_write_clk = out_clk_pll_c2;

  pll the_pll
    (
      .address      (pll_s1_address),
      .c0           (out_clk_pll_c0),
      .c1           (out_clk_pll_c1),
      .c2           (out_clk_pll_c2),
      .chipselect   (pll_s1_chipselect),
      .clk          (external_clk),
      .read         (pll_s1_read),
      .readdata     (pll_s1_readdata),
      .reset_n      (pll_s1_reset_n),
      .resetrequest (pll_s1_resetrequest),
      .write        (pll_s1_write),
      .writedata    (pll_s1_writedata)
    );

  sysid_control_slave_arbitrator the_sysid_control_slave
    (
      .clk                                                      (system_clk),
      .d1_sysid_control_slave_end_xfer                          (d1_sysid_control_slave_end_xfer),
      .pipeline_bridge_m1_address_to_slave                      (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                            (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_chipselect                            (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_granted_sysid_control_slave           (pipeline_bridge_m1_granted_sysid_control_slave),
      .pipeline_bridge_m1_latency_counter                       (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_sysid_control_slave (pipeline_bridge_m1_qualified_request_sysid_control_slave),
      .pipeline_bridge_m1_read                                  (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_sysid_control_slave   (pipeline_bridge_m1_read_data_valid_sysid_control_slave),
      .pipeline_bridge_m1_requests_sysid_control_slave          (pipeline_bridge_m1_requests_sysid_control_slave),
      .pipeline_bridge_m1_write                                 (pipeline_bridge_m1_write),
      .reset_n                                                  (system_clk_reset_n),
      .sysid_control_slave_address                              (sysid_control_slave_address),
      .sysid_control_slave_readdata                             (sysid_control_slave_readdata),
      .sysid_control_slave_readdata_from_sa                     (sysid_control_slave_readdata_from_sa)
    );

  sysid the_sysid
    (
      .address  (sysid_control_slave_address),
      .readdata (sysid_control_slave_readdata)
    );

  timestamp_timer_s1_arbitrator the_timestamp_timer_s1
    (
      .clk                                                     (system_clk),
      .d1_timestamp_timer_s1_end_xfer                          (d1_timestamp_timer_s1_end_xfer),
      .pipeline_bridge_m1_address_to_slave                     (pipeline_bridge_m1_address_to_slave),
      .pipeline_bridge_m1_burstcount                           (pipeline_bridge_m1_burstcount),
      .pipeline_bridge_m1_chipselect                           (pipeline_bridge_m1_chipselect),
      .pipeline_bridge_m1_granted_timestamp_timer_s1           (pipeline_bridge_m1_granted_timestamp_timer_s1),
      .pipeline_bridge_m1_latency_counter                      (pipeline_bridge_m1_latency_counter),
      .pipeline_bridge_m1_qualified_request_timestamp_timer_s1 (pipeline_bridge_m1_qualified_request_timestamp_timer_s1),
      .pipeline_bridge_m1_read                                 (pipeline_bridge_m1_read),
      .pipeline_bridge_m1_read_data_valid_timestamp_timer_s1   (pipeline_bridge_m1_read_data_valid_timestamp_timer_s1),
      .pipeline_bridge_m1_requests_timestamp_timer_s1          (pipeline_bridge_m1_requests_timestamp_timer_s1),
      .pipeline_bridge_m1_write                                (pipeline_bridge_m1_write),
      .pipeline_bridge_m1_writedata                            (pipeline_bridge_m1_writedata),
      .reset_n                                                 (system_clk_reset_n),
      .timestamp_timer_s1_address                              (timestamp_timer_s1_address),
      .timestamp_timer_s1_chipselect                           (timestamp_timer_s1_chipselect),
      .timestamp_timer_s1_irq                                  (timestamp_timer_s1_irq),
      .timestamp_timer_s1_irq_from_sa                          (timestamp_timer_s1_irq_from_sa),
      .timestamp_timer_s1_readdata                             (timestamp_timer_s1_readdata),
      .timestamp_timer_s1_readdata_from_sa                     (timestamp_timer_s1_readdata_from_sa),
      .timestamp_timer_s1_reset_n                              (timestamp_timer_s1_reset_n),
      .timestamp_timer_s1_write_n                              (timestamp_timer_s1_write_n),
      .timestamp_timer_s1_writedata                            (timestamp_timer_s1_writedata)
    );

  timestamp_timer the_timestamp_timer
    (
      .address    (timestamp_timer_s1_address),
      .chipselect (timestamp_timer_s1_chipselect),
      .clk        (system_clk),
      .irq        (timestamp_timer_s1_irq),
      .readdata   (timestamp_timer_s1_readdata),
      .reset_n    (timestamp_timer_s1_reset_n),
      .write_n    (timestamp_timer_s1_write_n),
      .writedata  (timestamp_timer_s1_writedata)
    );

  //reset is asserted asynchronously and deasserted synchronously
  custom_dma_reset_system_clk_domain_synch_module custom_dma_reset_system_clk_domain_synch
    (
      .clk      (system_clk),
      .data_in  (1'b1),
      .data_out (system_clk_reset_n),
      .reset_n  (reset_n_sources)
    );

  //reset sources mux, which is an e_mux
  assign reset_n_sources = ~(~reset_n |
    0 |
    cpu_jtag_debug_module_resetrequest_from_sa |
    cpu_jtag_debug_module_resetrequest_from_sa |
    0 |
    pll_s1_resetrequest_from_sa |
    pll_s1_resetrequest_from_sa);

  //reset is asserted asynchronously and deasserted synchronously
  custom_dma_reset_external_clk_domain_synch_module custom_dma_reset_external_clk_domain_synch
    (
      .clk      (external_clk),
      .data_in  (1'b1),
      .data_out (external_clk_reset_n),
      .reset_n  (reset_n_sources)
    );

  //custom_dma_burst_1_upstream_writedata of type writedata does not connect to anything so wire it to default (0)
  assign custom_dma_burst_1_upstream_writedata = 0;

  //custom_dma_burst_3_upstream_writedata of type writedata does not connect to anything so wire it to default (0)
  assign custom_dma_burst_3_upstream_writedata = 0;

  //custom_dma_clock_0_out_endofpacket of type endofpacket does not connect to anything so wire it to default (0)
  assign custom_dma_clock_0_out_endofpacket = 0;


endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_lane0_module (
                                // inputs:
                                 clk,
                                 data,
                                 rdaddress,
                                 rdclken,
                                 reset_n,
                                 wraddress,
                                 wrclock,
                                 wren,

                                // outputs:
                                 q
                              )
;

  output  [  7: 0] q;
  input            clk;
  input   [  7: 0] data;
  input   [ 18: 0] rdaddress;
  input            rdclken;
  input            reset_n;
  input   [ 18: 0] wraddress;
  input            wrclock;
  input            wren;

  reg     [ 18: 0] d1_rdaddress;
  reg     [  7: 0] mem_array [524287: 0];
  wire    [  7: 0] q;
  reg     [ 18: 0] read_address;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          d1_rdaddress <= 0;
          read_address <= 0;
        end
      else if (rdclken)
        begin
          d1_rdaddress <= rdaddress;
          read_address <= d1_rdaddress;
        end
    end


  // Data read is synchronized through latent_rdaddress.
  assign q = mem_array[read_address];

initial
    $readmemh("ext_ssram_lane0.dat", mem_array);
  always @(posedge wrclock)
    begin
      // Write data
      if (wren)
          mem_array[wraddress] <= data;
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  always @(rdaddress)
//    begin
//      read_address = rdaddress;
//    end
//
//
//  lpm_ram_dp lpm_ram_dp_component
//    (
//      .data (data),
//      .q (q),
//      .rdaddress (read_address),
//      .rdclken (rdclken),
//      .rdclock (clk),
//      .wraddress (wraddress),
//      .wrclock (wrclock),
//      .wren (wren)
//    );
//
//  defparam lpm_ram_dp_component.lpm_file = "ext_ssram_lane0.mif",
//           lpm_ram_dp_component.lpm_hint = "USE_EAB=ON",
//           lpm_ram_dp_component.lpm_indata = "REGISTERED",
//           lpm_ram_dp_component.lpm_outdata = "REGISTERED",
//           lpm_ram_dp_component.lpm_rdaddress_control = "REGISTERED",
//           lpm_ram_dp_component.lpm_width = 8,
//           lpm_ram_dp_component.lpm_widthad = 19,
//           lpm_ram_dp_component.lpm_wraddress_control = "REGISTERED",
//           lpm_ram_dp_component.suppress_memory_conversion_warnings = "ON";
//
//synthesis read_comments_as_HDL off

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_lane1_module (
                                // inputs:
                                 clk,
                                 data,
                                 rdaddress,
                                 rdclken,
                                 reset_n,
                                 wraddress,
                                 wrclock,
                                 wren,

                                // outputs:
                                 q
                              )
;

  output  [  7: 0] q;
  input            clk;
  input   [  7: 0] data;
  input   [ 18: 0] rdaddress;
  input            rdclken;
  input            reset_n;
  input   [ 18: 0] wraddress;
  input            wrclock;
  input            wren;

  reg     [ 18: 0] d1_rdaddress;
  reg     [  7: 0] mem_array [524287: 0];
  wire    [  7: 0] q;
  reg     [ 18: 0] read_address;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          d1_rdaddress <= 0;
          read_address <= 0;
        end
      else if (rdclken)
        begin
          d1_rdaddress <= rdaddress;
          read_address <= d1_rdaddress;
        end
    end


  // Data read is synchronized through latent_rdaddress.
  assign q = mem_array[read_address];

initial
    $readmemh("ext_ssram_lane1.dat", mem_array);
  always @(posedge wrclock)
    begin
      // Write data
      if (wren)
          mem_array[wraddress] <= data;
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  always @(rdaddress)
//    begin
//      read_address = rdaddress;
//    end
//
//
//  lpm_ram_dp lpm_ram_dp_component
//    (
//      .data (data),
//      .q (q),
//      .rdaddress (read_address),
//      .rdclken (rdclken),
//      .rdclock (clk),
//      .wraddress (wraddress),
//      .wrclock (wrclock),
//      .wren (wren)
//    );
//
//  defparam lpm_ram_dp_component.lpm_file = "ext_ssram_lane1.mif",
//           lpm_ram_dp_component.lpm_hint = "USE_EAB=ON",
//           lpm_ram_dp_component.lpm_indata = "REGISTERED",
//           lpm_ram_dp_component.lpm_outdata = "REGISTERED",
//           lpm_ram_dp_component.lpm_rdaddress_control = "REGISTERED",
//           lpm_ram_dp_component.lpm_width = 8,
//           lpm_ram_dp_component.lpm_widthad = 19,
//           lpm_ram_dp_component.lpm_wraddress_control = "REGISTERED",
//           lpm_ram_dp_component.suppress_memory_conversion_warnings = "ON";
//
//synthesis read_comments_as_HDL off

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_lane2_module (
                                // inputs:
                                 clk,
                                 data,
                                 rdaddress,
                                 rdclken,
                                 reset_n,
                                 wraddress,
                                 wrclock,
                                 wren,

                                // outputs:
                                 q
                              )
;

  output  [  7: 0] q;
  input            clk;
  input   [  7: 0] data;
  input   [ 18: 0] rdaddress;
  input            rdclken;
  input            reset_n;
  input   [ 18: 0] wraddress;
  input            wrclock;
  input            wren;

  reg     [ 18: 0] d1_rdaddress;
  reg     [  7: 0] mem_array [524287: 0];
  wire    [  7: 0] q;
  reg     [ 18: 0] read_address;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          d1_rdaddress <= 0;
          read_address <= 0;
        end
      else if (rdclken)
        begin
          d1_rdaddress <= rdaddress;
          read_address <= d1_rdaddress;
        end
    end


  // Data read is synchronized through latent_rdaddress.
  assign q = mem_array[read_address];

initial
    $readmemh("ext_ssram_lane2.dat", mem_array);
  always @(posedge wrclock)
    begin
      // Write data
      if (wren)
          mem_array[wraddress] <= data;
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  always @(rdaddress)
//    begin
//      read_address = rdaddress;
//    end
//
//
//  lpm_ram_dp lpm_ram_dp_component
//    (
//      .data (data),
//      .q (q),
//      .rdaddress (read_address),
//      .rdclken (rdclken),
//      .rdclock (clk),
//      .wraddress (wraddress),
//      .wrclock (wrclock),
//      .wren (wren)
//    );
//
//  defparam lpm_ram_dp_component.lpm_file = "ext_ssram_lane2.mif",
//           lpm_ram_dp_component.lpm_hint = "USE_EAB=ON",
//           lpm_ram_dp_component.lpm_indata = "REGISTERED",
//           lpm_ram_dp_component.lpm_outdata = "REGISTERED",
//           lpm_ram_dp_component.lpm_rdaddress_control = "REGISTERED",
//           lpm_ram_dp_component.lpm_width = 8,
//           lpm_ram_dp_component.lpm_widthad = 19,
//           lpm_ram_dp_component.lpm_wraddress_control = "REGISTERED",
//           lpm_ram_dp_component.suppress_memory_conversion_warnings = "ON";
//
//synthesis read_comments_as_HDL off

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram_lane3_module (
                                // inputs:
                                 clk,
                                 data,
                                 rdaddress,
                                 rdclken,
                                 reset_n,
                                 wraddress,
                                 wrclock,
                                 wren,

                                // outputs:
                                 q
                              )
;

  output  [  7: 0] q;
  input            clk;
  input   [  7: 0] data;
  input   [ 18: 0] rdaddress;
  input            rdclken;
  input            reset_n;
  input   [ 18: 0] wraddress;
  input            wrclock;
  input            wren;

  reg     [ 18: 0] d1_rdaddress;
  reg     [  7: 0] mem_array [524287: 0];
  wire    [  7: 0] q;
  reg     [ 18: 0] read_address;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          d1_rdaddress <= 0;
          read_address <= 0;
        end
      else if (rdclken)
        begin
          d1_rdaddress <= rdaddress;
          read_address <= d1_rdaddress;
        end
    end


  // Data read is synchronized through latent_rdaddress.
  assign q = mem_array[read_address];

initial
    $readmemh("ext_ssram_lane3.dat", mem_array);
  always @(posedge wrclock)
    begin
      // Write data
      if (wren)
          mem_array[wraddress] <= data;
    end



//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  always @(rdaddress)
//    begin
//      read_address = rdaddress;
//    end
//
//
//  lpm_ram_dp lpm_ram_dp_component
//    (
//      .data (data),
//      .q (q),
//      .rdaddress (read_address),
//      .rdclken (rdclken),
//      .rdclock (clk),
//      .wraddress (wraddress),
//      .wrclock (wrclock),
//      .wren (wren)
//    );
//
//  defparam lpm_ram_dp_component.lpm_file = "ext_ssram_lane3.mif",
//           lpm_ram_dp_component.lpm_hint = "USE_EAB=ON",
//           lpm_ram_dp_component.lpm_indata = "REGISTERED",
//           lpm_ram_dp_component.lpm_outdata = "REGISTERED",
//           lpm_ram_dp_component.lpm_rdaddress_control = "REGISTERED",
//           lpm_ram_dp_component.lpm_width = 8,
//           lpm_ram_dp_component.lpm_widthad = 19,
//           lpm_ram_dp_component.lpm_wraddress_control = "REGISTERED",
//           lpm_ram_dp_component.suppress_memory_conversion_warnings = "ON";
//
//synthesis read_comments_as_HDL off

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ext_ssram (
                   // inputs:
                    address,
                    adsc_n,
                    bw_n,
                    bwe_n,
                    chipenable1_n,
                    clk,
                    outputenable_n,
                    reset_n,

                   // outputs:
                    data
                 )
;

  inout   [ 31: 0] data;
  input   [ 18: 0] address;
  input            adsc_n;
  input   [  3: 0] bw_n;
  input            bwe_n;
  input            chipenable1_n;
  input            clk;
  input            outputenable_n;
  input            reset_n;

  wire    [ 31: 0] data;
  wire    [  7: 0] data_0;
  wire    [  7: 0] data_1;
  wire    [  7: 0] data_2;
  wire    [  7: 0] data_3;
  wire    [ 31: 0] logic_vector_gasket;
  wire    [  7: 0] q_0;
  wire    [  7: 0] q_1;
  wire    [  7: 0] q_2;
  wire    [  7: 0] q_3;
  //s1, which is an e_ptf_slave

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  assign logic_vector_gasket = data;
  assign data_0 = logic_vector_gasket[7 : 0];
  //ext_ssram_lane0, which is an e_ram
  ext_ssram_lane0_module ext_ssram_lane0
    (
      .clk       (clk),
      .data      (data_0),
      .q         (q_0),
      .rdaddress (address),
      .rdclken   (1'b1),
      .reset_n   (reset_n),
      .wraddress (address),
      .wrclock   (clk),
      .wren      (~chipenable1_n & ~bwe_n & ~bw_n[0])
    );

  assign data_1 = logic_vector_gasket[15 : 8];
  //ext_ssram_lane1, which is an e_ram
  ext_ssram_lane1_module ext_ssram_lane1
    (
      .clk       (clk),
      .data      (data_1),
      .q         (q_1),
      .rdaddress (address),
      .rdclken   (1'b1),
      .reset_n   (reset_n),
      .wraddress (address),
      .wrclock   (clk),
      .wren      (~chipenable1_n & ~bwe_n & ~bw_n[1])
    );

  assign data_2 = logic_vector_gasket[23 : 16];
  //ext_ssram_lane2, which is an e_ram
  ext_ssram_lane2_module ext_ssram_lane2
    (
      .clk       (clk),
      .data      (data_2),
      .q         (q_2),
      .rdaddress (address),
      .rdclken   (1'b1),
      .reset_n   (reset_n),
      .wraddress (address),
      .wrclock   (clk),
      .wren      (~chipenable1_n & ~bwe_n & ~bw_n[2])
    );

  assign data_3 = logic_vector_gasket[31 : 24];
  //ext_ssram_lane3, which is an e_ram
  ext_ssram_lane3_module ext_ssram_lane3
    (
      .clk       (clk),
      .data      (data_3),
      .q         (q_3),
      .rdaddress (address),
      .rdclken   (1'b1),
      .reset_n   (reset_n),
      .wraddress (address),
      .wrclock   (clk),
      .wren      (~chipenable1_n & ~bwe_n & ~bw_n[3])
    );

  assign data = (~chipenable1_n & ~outputenable_n)? {q_3,
    q_2,
    q_1,
    q_0}: {32{1'bz}};


//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule


//synthesis translate_off



// <ALTERA_NOTE> CODE INSERTED BETWEEN HERE

// AND HERE WILL BE PRESERVED </ALTERA_NOTE>


// If user logic components use Altsync_Ram with convert_hex2ver.dll,
// set USE_convert_hex2ver in the user comments section above

// `ifdef USE_convert_hex2ver
// `else
// `define NO_PLI 1
// `endif

`include "c:/altera/91sp2/quartus/eda/sim_lib/altera_mf.v"
`include "c:/altera/91sp2/quartus/eda/sim_lib/220model.v"
`include "c:/altera/91sp2/quartus/eda/sim_lib/sgate.v"
`include "c:/altera/91sp2/quartus/eda/sim_lib/stratixii_atoms.v"
`include "ddr_sdram_auk_ddr_dqs_group.v"
`include "ddr_sdram_auk_ddr_clk_gen.v"
`include "ddr_sdram_auk_ddr_datapath.v"
`include "ddr_sdram.vo"
`include "fir_dma.vo"
`include "pll.v"
`include "altpllpll.v"
`include "custom_dma_burst_2.v"
`include "sysid.v"
`include "custom_dma_burst_5.v"
`include "jtag_uart.v"
`include "custom_dma_burst_0.v"
`include "pipeline_bridge.v"
`include "ddr_sdram_test_component.v"
`include "cpu_test_bench.v"
`include "cpu_mult_cell.v"
`include "cpu_oci_test_bench.v"
`include "cpu_jtag_debug_module_tck.v"
`include "cpu_jtag_debug_module_sysclk.v"
`include "cpu_jtag_debug_module_wrapper.v"
`include "cpu.vo"
`include "custom_dma_clock_0.v"
`include "custom_dma_burst_1.v"
`include "timestamp_timer.v"
`include "custom_dma_burst_3.v"
`include "custom_dma_burst_4.v"

`timescale 1ns / 1ps

module test_bench 
;


  wire             adsc_n_to_the_ext_ssram;
  wire    [  3: 0] bw_n_to_the_ext_ssram;
  wire             bwe_n_to_the_ext_ssram;
  wire             chipenable1_n_to_the_ext_ssram;
  wire             clk;
  wire             clk_to_sdram_from_the_ddr_sdram;
  wire             clk_to_sdram_n_from_the_ddr_sdram;
  wire             custom_dma_burst_0_downstream_debugaccess;
  wire    [ 20: 0] custom_dma_burst_0_downstream_nativeaddress;
  wire    [ 31: 0] custom_dma_burst_1_upstream_writedata;
  wire             custom_dma_burst_3_downstream_debugaccess;
  wire    [ 24: 0] custom_dma_burst_3_downstream_nativeaddress;
  wire    [ 31: 0] custom_dma_burst_3_upstream_writedata;
  wire             custom_dma_burst_4_downstream_debugaccess;
  wire    [ 24: 0] custom_dma_burst_4_downstream_nativeaddress;
  wire             custom_dma_burst_5_downstream_debugaccess;
  wire    [ 24: 0] custom_dma_burst_5_downstream_nativeaddress;
  wire    [ 31: 0] custom_dma_burst_5_upstream_readdata_from_sa;
  wire             custom_dma_burst_5_upstream_readdatavalid_from_sa;
  wire             custom_dma_clock_0_out_endofpacket;
  wire    [ 12: 0] ddr_a_from_the_ddr_sdram;
  wire    [  1: 0] ddr_ba_from_the_ddr_sdram;
  wire             ddr_cas_n_from_the_ddr_sdram;
  wire             ddr_cke_from_the_ddr_sdram;
  wire             ddr_cs_n_from_the_ddr_sdram;
  wire    [  1: 0] ddr_dm_from_the_ddr_sdram;
  wire    [ 15: 0] ddr_dq_to_and_from_the_ddr_sdram;
  wire    [  1: 0] ddr_dqs_to_and_from_the_ddr_sdram;
  wire             ddr_ras_n_from_the_ddr_sdram;
  wire             ddr_we_n_from_the_ddr_sdram;
  wire    [  5: 0] dqs_delay_ctrl_to_the_ddr_sdram;
  wire             dqsupdate_to_the_ddr_sdram;
  wire    [ 20: 0] ext_ssram_bus_address;
  wire    [ 31: 0] ext_ssram_bus_data;
  reg              external_clk;
  wire             jtag_uart_avalon_jtag_slave_dataavailable_from_sa;
  wire             jtag_uart_avalon_jtag_slave_readyfordata_from_sa;
  wire             outputenable_n_to_the_ext_ssram;
  wire             pipeline_bridge_s1_endofpacket_from_sa;
  reg              reset_n;
  wire             sdram_write_clk;
  wire             ssram_clk;
  wire             stratix_dll_control_from_the_ddr_sdram;
  wire             system_clk;
  wire             write_clk_to_the_ddr_sdram;


// <ALTERA_NOTE> CODE INSERTED BETWEEN HERE
//  add your signals and additional architecture here
// AND HERE WILL BE PRESERVED </ALTERA_NOTE>

  //Set us up the Dut
  custom_dma DUT
    (
      .adsc_n_to_the_ext_ssram                (adsc_n_to_the_ext_ssram),
      .bw_n_to_the_ext_ssram                  (bw_n_to_the_ext_ssram),
      .bwe_n_to_the_ext_ssram                 (bwe_n_to_the_ext_ssram),
      .chipenable1_n_to_the_ext_ssram         (chipenable1_n_to_the_ext_ssram),
      .clk_to_sdram_from_the_ddr_sdram        (clk_to_sdram_from_the_ddr_sdram),
      .clk_to_sdram_n_from_the_ddr_sdram      (clk_to_sdram_n_from_the_ddr_sdram),
      .ddr_a_from_the_ddr_sdram               (ddr_a_from_the_ddr_sdram),
      .ddr_ba_from_the_ddr_sdram              (ddr_ba_from_the_ddr_sdram),
      .ddr_cas_n_from_the_ddr_sdram           (ddr_cas_n_from_the_ddr_sdram),
      .ddr_cke_from_the_ddr_sdram             (ddr_cke_from_the_ddr_sdram),
      .ddr_cs_n_from_the_ddr_sdram            (ddr_cs_n_from_the_ddr_sdram),
      .ddr_dm_from_the_ddr_sdram              (ddr_dm_from_the_ddr_sdram),
      .ddr_dq_to_and_from_the_ddr_sdram       (ddr_dq_to_and_from_the_ddr_sdram),
      .ddr_dqs_to_and_from_the_ddr_sdram      (ddr_dqs_to_and_from_the_ddr_sdram),
      .ddr_ras_n_from_the_ddr_sdram           (ddr_ras_n_from_the_ddr_sdram),
      .ddr_we_n_from_the_ddr_sdram            (ddr_we_n_from_the_ddr_sdram),
      .dqs_delay_ctrl_to_the_ddr_sdram        (dqs_delay_ctrl_to_the_ddr_sdram),
      .dqsupdate_to_the_ddr_sdram             (dqsupdate_to_the_ddr_sdram),
      .ext_ssram_bus_address                  (ext_ssram_bus_address),
      .ext_ssram_bus_data                     (ext_ssram_bus_data),
      .external_clk                           (external_clk),
      .outputenable_n_to_the_ext_ssram        (outputenable_n_to_the_ext_ssram),
      .reset_n                                (reset_n),
      .sdram_write_clk                        (sdram_write_clk),
      .ssram_clk                              (ssram_clk),
      .stratix_dll_control_from_the_ddr_sdram (stratix_dll_control_from_the_ddr_sdram),
      .system_clk                             (system_clk),
      .write_clk_to_the_ddr_sdram             (write_clk_to_the_ddr_sdram)
    );

  ext_ssram the_ext_ssram
    (
      .address        (ext_ssram_bus_address[20 : 2]),
      .adsc_n         (adsc_n_to_the_ext_ssram),
      .bw_n           (bw_n_to_the_ext_ssram),
      .bwe_n          (bwe_n_to_the_ext_ssram),
      .chipenable1_n  (chipenable1_n_to_the_ext_ssram),
      .clk            (system_clk),
      .data           (ext_ssram_bus_data),
      .outputenable_n (outputenable_n_to_the_ext_ssram),
      .reset_n        (reset_n)
    );

  ddr_sdram_test_component the_ddr_sdram_test_component
    (
      .clk       (system_clk),
      .ddr_a     (ddr_a_from_the_ddr_sdram),
      .ddr_ba    (ddr_ba_from_the_ddr_sdram),
      .ddr_cas_n (ddr_cas_n_from_the_ddr_sdram),
      .ddr_cke   (ddr_cke_from_the_ddr_sdram),
      .ddr_cs_n  (ddr_cs_n_from_the_ddr_sdram),
      .ddr_dm    (ddr_dm_from_the_ddr_sdram),
      .ddr_dq    (ddr_dq_to_and_from_the_ddr_sdram),
      .ddr_dqs   (ddr_dqs_to_and_from_the_ddr_sdram),
      .ddr_ras_n (ddr_ras_n_from_the_ddr_sdram),
      .ddr_we_n  (ddr_we_n_from_the_ddr_sdram)
    );

  initial
    external_clk = 1'b0;
  always
    #10 external_clk <= ~external_clk;
  
  initial 
    begin
      reset_n <= 0;
      #200 reset_n <= 1;
    end

endmodule


//synthesis translate_on