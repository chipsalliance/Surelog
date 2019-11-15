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
`timescale 1ps / 1ps
// synthesis translate_on

// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

//------------------------------------------------------------------------------
//Parameters:
//Device Family                      : Stratix II
//DQ_PER_DQS                         : 8
//NON-DQS MODE                       : false
//use Resynch clock                  : true
//Resynch clock edge                 : rising
//Postamble Clock Edge               : rising
//Postamble Clock Cycle              : 1
//Intermediate Resynch               : false
//Intermediate Postamble             : false
//Pipeline read Data                 : false
//Enable Postamble Logic             : true
//Postamble Regs Per DQS             : 1
//Stratix Insert DQS delay buffers   : 0
//------------------------------------------------------------------------------
module ddr_sdram_auk_ddr_dqs_group (
                                     // inputs:
                                      capture_clk,
                                      clk,
                                      control_be,
                                      control_doing_rd,
                                      control_doing_wr,
                                      control_dqs_burst,
                                      control_wdata,
                                      control_wdata_valid,
                                      dqs_delay_ctrl,
                                      dqsupdate,
                                      postamble_clk,
                                      reset_n,
                                      resynch_clk,
                                      write_clk,

                                     // outputs:
                                      control_rdata,
                                      ddr_dm,
                                      ddr_dq,
                                      ddr_dqs
                                   )
  /* synthesis ALTERA_ATTRIBUTE = "MESSAGE_DISABLE=14130;SUPPRESS_DA_RULE_INTERNAL=C101;SUPPRESS_DA_RULE_INTERNAL=C103;SUPPRESS_DA_RULE_INTERNAL=C105;SUPPRESS_DA_RULE_INTERNAL=C106;SUPPRESS_DA_RULE_INTERNAL=R104;SUPPRESS_DA_RULE_INTERNAL=A102;SUPPRESS_DA_RULE_INTERNAL=A103;SUPPRESS_DA_RULE_INTERNAL=C104;SUPPRESS_DA_RULE_INTERNAL=D101;SUPPRESS_DA_RULE_INTERNAL=D102;SUPPRESS_DA_RULE_INTERNAL=D103;SUPPRESS_DA_RULE_INTERNAL=R102;SUPPRESS_DA_RULE_INTERNAL=R105" */ ;

  parameter gDLL_INPUT_FREQUENCY = "10000ps";
  parameter gSTRATIXII_DQS_OUT_MODE = "delay_chain2";
  parameter gSTRATIXII_DQS_PHASE = 6000;
  parameter gSTRATIXII_DLL_DELAY_BUFFER_MODE = "low";


  output  [ 15: 0] control_rdata;
  output           ddr_dm;
  inout   [  7: 0] ddr_dq;
  inout            ddr_dqs;
  input            capture_clk;
  input            clk;
  input   [  1: 0] control_be;
  input            control_doing_rd;
  input            control_doing_wr;
  input            control_dqs_burst;
  input   [ 15: 0] control_wdata;
  input            control_wdata_valid;
  input   [  5: 0] dqs_delay_ctrl;
  input            dqsupdate;
  input            postamble_clk;
  input            reset_n;
  input            resynch_clk;
  input            write_clk;

  wire             ZERO;
  wire    [  7: 0] ZEROS;
  wire    [ 13: 0] ZEROS_14;
  wire    [  1: 0] be;
  wire    [ 15: 0] control_rdata;
  wire             ddr_dm;
  wire    [  7: 0] ddr_dq;
  wire             ddr_dqs;
  wire    [ 15: 0] delayed_dq_captured;
  reg     [  1: 0] dm_out;
  wire             doing_rd;
  reg              doing_rd_delayed;
  reg     [  2: 0] doing_rd_pipe;
  wire             doing_wr;
  reg              doing_wr_r;
  wire             dq_capture_clk;
  wire    [ 15: 0] dq_captured_0;
  wire    [  7: 0] dq_captured_falling;
  wire    [  7: 0] dq_captured_rising;
  reg     [  0: 0] dq_enable_reset;
  reg              dq_oe;
  wire             dqs_burst;
  wire    [  0: 0] dqs_clk;
  wire             dqs_oe;
  reg     [  0: 0] dqs_oe_r;
  wire    [ 15: 0] inter_rdata;
  wire    [  0: 0] not_dqs_clk;
  wire    [ 15: 0] rdata;
  wire             reset;
  reg     [ 15: 0] resynched_data;
  wire             tmp_dmout0;
  wire             tmp_dmout1;
  wire    [  0: 0] undelayed_dqs;
  wire    [ 15: 0] wdata;
  reg     [ 15: 0] wdata_r;
  wire             wdata_valid;
  //


  assign ZERO = 1'b0;
  assign ZEROS = 0;
  assign ZEROS_14 = 0;
  assign reset = ~reset_n;
  assign not_dqs_clk = ~dqs_clk;
  // rename user i/f signals, outputs
  assign control_rdata = rdata;

  // rename user i/f signals, inputs
  assign wdata = control_wdata;

  assign wdata_valid = control_wdata_valid;
  assign doing_wr = control_doing_wr;
  assign doing_rd = control_doing_rd;
  assign be = control_be;
  assign dqs_burst = control_dqs_burst;
  //-----------------------------------------------------------------------------
  //DQS pin and its logic
  //Generate the output enable for DQS from the signal that indicates we're
  //doing a write. The DQS burst signal is generated by the controller to keep
  //the DQS toggling for the required burst length.
  //-----------------------------------------------------------------------------

  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          dqs_oe_r <= 1'b0;
          doing_wr_r <= 1'b0;
        end
      else 
        begin
          dqs_oe_r <= dqs_oe;
          doing_wr_r <= doing_wr;
        end
    end


  assign dqs_oe = doing_wr | dqs_burst;
  //-----------------------------------------------------------------------------
  //DM pins and their logic
  //Although these don't get tristated like DQ, they do share the same IO timing.
  //-----------------------------------------------------------------------------
  assign tmp_dmout0 = dm_out[0];
  assign tmp_dmout1 = dm_out[1];
  altddio_out dm_pin
    (
      .aclr (reset),
      .aset (),
      .datain_h (tmp_dmout0),
      .datain_l (tmp_dmout1),
      .dataout (ddr_dm),
      .oe (1'b1),
      .outclock (write_clk),
      .outclocken (1'b1)
    );

  defparam dm_pin.extend_oe_disable = "UNUSED",
           dm_pin.intended_device_family = "Stratix II",
           dm_pin.invert_output = "OFF",
           dm_pin.lpm_hint = "UNUSED",
           dm_pin.lpm_type = "altddio_out",
           dm_pin.oe_reg = "UNUSED",
           dm_pin.power_up_high = "OFF",
           dm_pin.width = 1;

  //-----------------------------------------------------------------------------
  //Data mask registers
  //These are the last registers before the registers in the altddio_out. They
  //are clocked off the system clock but feed registers which are clocked off the
  //write clock, so their output is the beginning of 3/4 cycle path.
  //-----------------------------------------------------------------------------
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          dm_out <= {2{1'b1}};
      else if (doing_wr)
          // don't latch in data unless it's valid
          dm_out <= ~be;

      else 
        dm_out <= {2{1'b1}};
    end


  //-----------------------------------------------------------------------------
  //Logic to disable the capture registers (particularly during DQS postamble)
  //The output of the dq_enable_reset register holds the dq_enable register in
  //reset (which *enables* the dq capture registers). The controller releases
  //the dq_enable register so that it is clocked by the last falling edge of the
  //read dqs signal. This disables the dq capture registers during and after the
  //dqs postamble so that the output of the dq capture registers can be safely
  //resynchronised.
  //Postamble Clock Cycle  : 1
  //Postamble Clock Edge   : rising
  //Postamble Regs Per DQS : 1
  //-----------------------------------------------------------------------------

  //Use a rising edge for postamble
  //The registers which generate the reset signal to the above registers
  //Can be clocked off the resynch or system clock
  always @(posedge postamble_clk or negedge reset_n)
    begin
      if (reset_n == 0)
          dq_enable_reset <= 1'b0;
      else 
        dq_enable_reset <= doing_rd_delayed;
    end


  //pipeline the doing_rd signal to enable and disable the DQ capture regs at the right time
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          doing_rd_pipe <= 0;
      else 
        //shift bits up
        doing_rd_pipe <= {doing_rd_pipe[1 : 0], doing_rd};

    end


  //It's safe to clock from falling edge of clk to postamble_clk, so use falling edge clock
  always @(negedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          doing_rd_delayed <= 1'b0;
      else 
        doing_rd_delayed <= doing_rd_pipe[1];
    end


  //-----------------------------------------------------------------------------
  //Decide which clock to use for capturing the DQ data
  //-----------------------------------------------------------------------------
  //Use DQS to capture DQ read data
  assign dq_capture_clk = ~dqs_clk;

  //-----------------------------------------------------------------------------
  //DQ pins and their logic
  //-----------------------------------------------------------------------------
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          dq_oe <= 1'b0;
      else 
        dq_oe <= doing_wr;
    end


  stratixii_io \g_dq_io:0:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[0]),
      .ddiodatain (wdata_r[8]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[0]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[0]),
      .regout (dq_captured_falling[0]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:0:dq_io .bus_hold = "false",
           \g_dq_io:0:dq_io .ddio_mode = "bidir",
           \g_dq_io:0:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:0:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:0:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:0:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:0:dq_io .dqs_input_frequency = "none",
           \g_dq_io:0:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:0:dq_io .dqs_out_mode = "none",
           \g_dq_io:0:dq_io .dqs_phase_shift = 0,
           \g_dq_io:0:dq_io .extend_oe_disable = "false",
           \g_dq_io:0:dq_io .gated_dqs = "false",
           \g_dq_io:0:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:0:dq_io .input_async_reset = "clear",
           \g_dq_io:0:dq_io .input_power_up = "low",
           \g_dq_io:0:dq_io .input_register_mode = "register",
           \g_dq_io:0:dq_io .input_sync_reset = "none",
           \g_dq_io:0:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:0:dq_io .oe_async_reset = "clear",
           \g_dq_io:0:dq_io .oe_power_up = "low",
           \g_dq_io:0:dq_io .oe_register_mode = "register",
           \g_dq_io:0:dq_io .oe_sync_reset = "none",
           \g_dq_io:0:dq_io .open_drain_output = "false",
           \g_dq_io:0:dq_io .operation_mode = "bidir",
           \g_dq_io:0:dq_io .output_async_reset = "clear",
           \g_dq_io:0:dq_io .output_power_up = "low",
           \g_dq_io:0:dq_io .output_register_mode = "register",
           \g_dq_io:0:dq_io .output_sync_reset = "none",
           \g_dq_io:0:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:0:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:0:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:0:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:0:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:1:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[1]),
      .ddiodatain (wdata_r[9]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[1]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[1]),
      .regout (dq_captured_falling[1]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:1:dq_io .bus_hold = "false",
           \g_dq_io:1:dq_io .ddio_mode = "bidir",
           \g_dq_io:1:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:1:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:1:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:1:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:1:dq_io .dqs_input_frequency = "none",
           \g_dq_io:1:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:1:dq_io .dqs_out_mode = "none",
           \g_dq_io:1:dq_io .dqs_phase_shift = 0,
           \g_dq_io:1:dq_io .extend_oe_disable = "false",
           \g_dq_io:1:dq_io .gated_dqs = "false",
           \g_dq_io:1:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:1:dq_io .input_async_reset = "clear",
           \g_dq_io:1:dq_io .input_power_up = "low",
           \g_dq_io:1:dq_io .input_register_mode = "register",
           \g_dq_io:1:dq_io .input_sync_reset = "none",
           \g_dq_io:1:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:1:dq_io .oe_async_reset = "clear",
           \g_dq_io:1:dq_io .oe_power_up = "low",
           \g_dq_io:1:dq_io .oe_register_mode = "register",
           \g_dq_io:1:dq_io .oe_sync_reset = "none",
           \g_dq_io:1:dq_io .open_drain_output = "false",
           \g_dq_io:1:dq_io .operation_mode = "bidir",
           \g_dq_io:1:dq_io .output_async_reset = "clear",
           \g_dq_io:1:dq_io .output_power_up = "low",
           \g_dq_io:1:dq_io .output_register_mode = "register",
           \g_dq_io:1:dq_io .output_sync_reset = "none",
           \g_dq_io:1:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:1:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:1:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:1:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:1:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:2:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[2]),
      .ddiodatain (wdata_r[10]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[2]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[2]),
      .regout (dq_captured_falling[2]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:2:dq_io .bus_hold = "false",
           \g_dq_io:2:dq_io .ddio_mode = "bidir",
           \g_dq_io:2:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:2:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:2:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:2:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:2:dq_io .dqs_input_frequency = "none",
           \g_dq_io:2:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:2:dq_io .dqs_out_mode = "none",
           \g_dq_io:2:dq_io .dqs_phase_shift = 0,
           \g_dq_io:2:dq_io .extend_oe_disable = "false",
           \g_dq_io:2:dq_io .gated_dqs = "false",
           \g_dq_io:2:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:2:dq_io .input_async_reset = "clear",
           \g_dq_io:2:dq_io .input_power_up = "low",
           \g_dq_io:2:dq_io .input_register_mode = "register",
           \g_dq_io:2:dq_io .input_sync_reset = "none",
           \g_dq_io:2:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:2:dq_io .oe_async_reset = "clear",
           \g_dq_io:2:dq_io .oe_power_up = "low",
           \g_dq_io:2:dq_io .oe_register_mode = "register",
           \g_dq_io:2:dq_io .oe_sync_reset = "none",
           \g_dq_io:2:dq_io .open_drain_output = "false",
           \g_dq_io:2:dq_io .operation_mode = "bidir",
           \g_dq_io:2:dq_io .output_async_reset = "clear",
           \g_dq_io:2:dq_io .output_power_up = "low",
           \g_dq_io:2:dq_io .output_register_mode = "register",
           \g_dq_io:2:dq_io .output_sync_reset = "none",
           \g_dq_io:2:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:2:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:2:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:2:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:2:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:3:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[3]),
      .ddiodatain (wdata_r[11]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[3]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[3]),
      .regout (dq_captured_falling[3]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:3:dq_io .bus_hold = "false",
           \g_dq_io:3:dq_io .ddio_mode = "bidir",
           \g_dq_io:3:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:3:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:3:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:3:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:3:dq_io .dqs_input_frequency = "none",
           \g_dq_io:3:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:3:dq_io .dqs_out_mode = "none",
           \g_dq_io:3:dq_io .dqs_phase_shift = 0,
           \g_dq_io:3:dq_io .extend_oe_disable = "false",
           \g_dq_io:3:dq_io .gated_dqs = "false",
           \g_dq_io:3:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:3:dq_io .input_async_reset = "clear",
           \g_dq_io:3:dq_io .input_power_up = "low",
           \g_dq_io:3:dq_io .input_register_mode = "register",
           \g_dq_io:3:dq_io .input_sync_reset = "none",
           \g_dq_io:3:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:3:dq_io .oe_async_reset = "clear",
           \g_dq_io:3:dq_io .oe_power_up = "low",
           \g_dq_io:3:dq_io .oe_register_mode = "register",
           \g_dq_io:3:dq_io .oe_sync_reset = "none",
           \g_dq_io:3:dq_io .open_drain_output = "false",
           \g_dq_io:3:dq_io .operation_mode = "bidir",
           \g_dq_io:3:dq_io .output_async_reset = "clear",
           \g_dq_io:3:dq_io .output_power_up = "low",
           \g_dq_io:3:dq_io .output_register_mode = "register",
           \g_dq_io:3:dq_io .output_sync_reset = "none",
           \g_dq_io:3:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:3:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:3:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:3:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:3:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:4:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[4]),
      .ddiodatain (wdata_r[12]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[4]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[4]),
      .regout (dq_captured_falling[4]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:4:dq_io .bus_hold = "false",
           \g_dq_io:4:dq_io .ddio_mode = "bidir",
           \g_dq_io:4:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:4:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:4:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:4:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:4:dq_io .dqs_input_frequency = "none",
           \g_dq_io:4:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:4:dq_io .dqs_out_mode = "none",
           \g_dq_io:4:dq_io .dqs_phase_shift = 0,
           \g_dq_io:4:dq_io .extend_oe_disable = "false",
           \g_dq_io:4:dq_io .gated_dqs = "false",
           \g_dq_io:4:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:4:dq_io .input_async_reset = "clear",
           \g_dq_io:4:dq_io .input_power_up = "low",
           \g_dq_io:4:dq_io .input_register_mode = "register",
           \g_dq_io:4:dq_io .input_sync_reset = "none",
           \g_dq_io:4:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:4:dq_io .oe_async_reset = "clear",
           \g_dq_io:4:dq_io .oe_power_up = "low",
           \g_dq_io:4:dq_io .oe_register_mode = "register",
           \g_dq_io:4:dq_io .oe_sync_reset = "none",
           \g_dq_io:4:dq_io .open_drain_output = "false",
           \g_dq_io:4:dq_io .operation_mode = "bidir",
           \g_dq_io:4:dq_io .output_async_reset = "clear",
           \g_dq_io:4:dq_io .output_power_up = "low",
           \g_dq_io:4:dq_io .output_register_mode = "register",
           \g_dq_io:4:dq_io .output_sync_reset = "none",
           \g_dq_io:4:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:4:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:4:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:4:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:4:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:5:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[5]),
      .ddiodatain (wdata_r[13]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[5]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[5]),
      .regout (dq_captured_falling[5]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:5:dq_io .bus_hold = "false",
           \g_dq_io:5:dq_io .ddio_mode = "bidir",
           \g_dq_io:5:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:5:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:5:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:5:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:5:dq_io .dqs_input_frequency = "none",
           \g_dq_io:5:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:5:dq_io .dqs_out_mode = "none",
           \g_dq_io:5:dq_io .dqs_phase_shift = 0,
           \g_dq_io:5:dq_io .extend_oe_disable = "false",
           \g_dq_io:5:dq_io .gated_dqs = "false",
           \g_dq_io:5:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:5:dq_io .input_async_reset = "clear",
           \g_dq_io:5:dq_io .input_power_up = "low",
           \g_dq_io:5:dq_io .input_register_mode = "register",
           \g_dq_io:5:dq_io .input_sync_reset = "none",
           \g_dq_io:5:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:5:dq_io .oe_async_reset = "clear",
           \g_dq_io:5:dq_io .oe_power_up = "low",
           \g_dq_io:5:dq_io .oe_register_mode = "register",
           \g_dq_io:5:dq_io .oe_sync_reset = "none",
           \g_dq_io:5:dq_io .open_drain_output = "false",
           \g_dq_io:5:dq_io .operation_mode = "bidir",
           \g_dq_io:5:dq_io .output_async_reset = "clear",
           \g_dq_io:5:dq_io .output_power_up = "low",
           \g_dq_io:5:dq_io .output_register_mode = "register",
           \g_dq_io:5:dq_io .output_sync_reset = "none",
           \g_dq_io:5:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:5:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:5:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:5:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:5:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:6:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[6]),
      .ddiodatain (wdata_r[14]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[6]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[6]),
      .regout (dq_captured_falling[6]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:6:dq_io .bus_hold = "false",
           \g_dq_io:6:dq_io .ddio_mode = "bidir",
           \g_dq_io:6:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:6:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:6:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:6:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:6:dq_io .dqs_input_frequency = "none",
           \g_dq_io:6:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:6:dq_io .dqs_out_mode = "none",
           \g_dq_io:6:dq_io .dqs_phase_shift = 0,
           \g_dq_io:6:dq_io .extend_oe_disable = "false",
           \g_dq_io:6:dq_io .gated_dqs = "false",
           \g_dq_io:6:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:6:dq_io .input_async_reset = "clear",
           \g_dq_io:6:dq_io .input_power_up = "low",
           \g_dq_io:6:dq_io .input_register_mode = "register",
           \g_dq_io:6:dq_io .input_sync_reset = "none",
           \g_dq_io:6:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:6:dq_io .oe_async_reset = "clear",
           \g_dq_io:6:dq_io .oe_power_up = "low",
           \g_dq_io:6:dq_io .oe_register_mode = "register",
           \g_dq_io:6:dq_io .oe_sync_reset = "none",
           \g_dq_io:6:dq_io .open_drain_output = "false",
           \g_dq_io:6:dq_io .operation_mode = "bidir",
           \g_dq_io:6:dq_io .output_async_reset = "clear",
           \g_dq_io:6:dq_io .output_power_up = "low",
           \g_dq_io:6:dq_io .output_register_mode = "register",
           \g_dq_io:6:dq_io .output_sync_reset = "none",
           \g_dq_io:6:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:6:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:6:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:6:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:6:dq_io .tie_off_output_clock_enable = "false";

  stratixii_io \g_dq_io:7:dq_io 
    (
      .areset (reset),
      .combout (),
      .datain (wdata_r[7]),
      .ddiodatain (wdata_r[15]),
      .ddioinclk (ZEROS[0]),
      .ddioregout (dq_captured_rising[7]),
      .delayctrlin (),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (),
      .dqsupdateen (),
      .inclk (dq_capture_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dq_oe),
      .offsetctrlin (),
      .outclk (write_clk),
      .outclkena (1'b1),
      .padio (ddr_dq[7]),
      .regout (dq_captured_falling[7]),
      .sreset (),
      .terminationcontrol ()
    );

  defparam \g_dq_io:7:dq_io .bus_hold = "false",
           \g_dq_io:7:dq_io .ddio_mode = "bidir",
           \g_dq_io:7:dq_io .ddioinclk_input = "negated_inclk",
           \g_dq_io:7:dq_io .dqs_ctrl_latches_enable = "false",
           \g_dq_io:7:dq_io .dqs_delay_buffer_mode = "none",
           \g_dq_io:7:dq_io .dqs_edge_detect_enable = "false",
           \g_dq_io:7:dq_io .dqs_input_frequency = "none",
           \g_dq_io:7:dq_io .dqs_offsetctrl_enable = "false",
           \g_dq_io:7:dq_io .dqs_out_mode = "none",
           \g_dq_io:7:dq_io .dqs_phase_shift = 0,
           \g_dq_io:7:dq_io .extend_oe_disable = "false",
           \g_dq_io:7:dq_io .gated_dqs = "false",
           \g_dq_io:7:dq_io .inclk_input = "dqs_bus",
           \g_dq_io:7:dq_io .input_async_reset = "clear",
           \g_dq_io:7:dq_io .input_power_up = "low",
           \g_dq_io:7:dq_io .input_register_mode = "register",
           \g_dq_io:7:dq_io .input_sync_reset = "none",
           \g_dq_io:7:dq_io .lpm_type = "stratixii_io",
           \g_dq_io:7:dq_io .oe_async_reset = "clear",
           \g_dq_io:7:dq_io .oe_power_up = "low",
           \g_dq_io:7:dq_io .oe_register_mode = "register",
           \g_dq_io:7:dq_io .oe_sync_reset = "none",
           \g_dq_io:7:dq_io .open_drain_output = "false",
           \g_dq_io:7:dq_io .operation_mode = "bidir",
           \g_dq_io:7:dq_io .output_async_reset = "clear",
           \g_dq_io:7:dq_io .output_power_up = "low",
           \g_dq_io:7:dq_io .output_register_mode = "register",
           \g_dq_io:7:dq_io .output_sync_reset = "none",
           \g_dq_io:7:dq_io .sim_dqs_delay_increment = 0,
           \g_dq_io:7:dq_io .sim_dqs_intrinsic_delay = 0,
           \g_dq_io:7:dq_io .sim_dqs_offset_increment = 0,
           \g_dq_io:7:dq_io .tie_off_oe_clock_enable = "false",
           \g_dq_io:7:dq_io .tie_off_output_clock_enable = "false";

  //-----------------------------------------------------------------------------
  //Write data registers
  //These are the last registers before the registers in the altddio_bidir. They
  //are clocked off the system clock but feed registers which are clocked off the
  //write clock, so their output is the beginning of 3/4 cycle path.
  //-----------------------------------------------------------------------------
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          wdata_r <= 0;
      else if (wdata_valid)
          //don't latch in data unless it's valid
          wdata_r <= wdata;

    end


  //Concatenate the rising and falling edge data to make a single bus
  assign dq_captured_0 = {dq_captured_falling, dq_captured_rising};

  //Apply delays in 1 chunks to avoid having to use transport delays
  assign #2500 delayed_dq_captured = dq_captured_0;

  //-----------------------------------------------------------------------------
  //Resynchronisation registers
  //These registers resychronise the captured read data from the DQS clock
  //domain back into an internal PLL clock domain. 
  //-----------------------------------------------------------------------------
  //Use a rising edge for resynch
  always @(posedge resynch_clk or negedge reset_n)
    begin
      if (reset_n == 0)
          resynched_data <= 0;
      else 
        resynched_data <= delayed_dq_captured;
    end


  //don't insert pipeline registers
  assign inter_rdata = resynched_data;

  //don't insert pipeline registers
  assign rdata = inter_rdata;


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  stratixii_io dqs_io
    (
      .areset (1'b1),
      .combout (undelayed_dqs),
      .datain (dqs_oe_r),
      .ddiodatain (ZEROS[0]),
      .ddioinclk (),
      .ddioregout (),
      .delayctrlin (dqs_delay_ctrl),
      .devclrn (),
      .devoe (),
      .devpor (),
      .dqsbusout (dqs_clk),
      .dqsupdateen (dqsupdate),
      .inclk (not_dqs_clk),
      .inclkena (1'b1),
      .linkin (),
      .linkout (),
      .oe (dqs_oe),
      .offsetctrlin (),
      .outclk (clk),
      .outclkena (1'b1),
      .padio (ddr_dqs),
      .regout (),
      .sreset (),
      .terminationcontrol ()
    );

  defparam dqs_io.bus_hold = "false",
           dqs_io.ddio_mode = "output",
           dqs_io.ddioinclk_input = "inclk",
           dqs_io.dqs_ctrl_latches_enable = "true",
           dqs_io.dqs_delay_buffer_mode = gSTRATIXII_DLL_DELAY_BUFFER_MODE,
           dqs_io.dqs_edge_detect_enable = "false",
           dqs_io.dqs_input_frequency = gDLL_INPUT_FREQUENCY,
           dqs_io.dqs_offsetctrl_enable = "false",
           dqs_io.dqs_out_mode = gSTRATIXII_DQS_OUT_MODE,
           dqs_io.dqs_phase_shift = 6000,
           dqs_io.extend_oe_disable = "true",
           dqs_io.gated_dqs = "true",
           dqs_io.inclk_input = "dqs_bus",
           dqs_io.input_async_reset = "preset",
           dqs_io.input_power_up = "high",
           dqs_io.input_register_mode = "register",
           dqs_io.input_sync_reset = "clear",
           dqs_io.lpm_type = "stratixii_io",
           dqs_io.oe_async_reset = "none",
           dqs_io.oe_power_up = "low",
           dqs_io.oe_register_mode = "register",
           dqs_io.oe_sync_reset = "none",
           dqs_io.open_drain_output = "false",
           dqs_io.operation_mode = "bidir",
           dqs_io.output_async_reset = "none",
           dqs_io.output_power_up = "low",
           dqs_io.output_register_mode = "register",
           dqs_io.output_sync_reset = "none",
           dqs_io.sim_dqs_delay_increment = 36,
           dqs_io.sim_dqs_intrinsic_delay = 900,
           dqs_io.sim_dqs_offset_increment = 0,
           dqs_io.tie_off_oe_clock_enable = "false",
           dqs_io.tie_off_output_clock_enable = "false";


//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  stratixii_io dqs_io
//    (
//      .areset (dq_enable_reset),
//      .combout (undelayed_dqs),
//      .datain (dqs_oe_r),
//      .ddiodatain (ZEROS[0]),
//      .ddioinclk (),
//      .ddioregout (),
//      .delayctrlin (dqs_delay_ctrl),
//      .devclrn (),
//      .devoe (),
//      .devpor (),
//      .dqsbusout (dqs_clk),
//      .dqsupdateen (dqsupdate),
//      .inclk (not_dqs_clk),
//      .inclkena (1'b1),
//      .linkin (),
//      .linkout (),
//      .oe (dqs_oe),
//      .offsetctrlin (),
//      .outclk (clk),
//      .outclkena (1'b1),
//      .padio (ddr_dqs),
//      .regout (),
//      .sreset (1'b1),
//      .terminationcontrol ()
//    );
//
//  defparam dqs_io.bus_hold = "false",
//           dqs_io.ddio_mode = "output",
//           dqs_io.ddioinclk_input = "negated_inclk",
//           dqs_io.dqs_ctrl_latches_enable = "true",
//           dqs_io.dqs_delay_buffer_mode = gSTRATIXII_DLL_DELAY_BUFFER_MODE,
//           dqs_io.dqs_edge_detect_enable = "false",
//           dqs_io.dqs_input_frequency = gDLL_INPUT_FREQUENCY,
//           dqs_io.dqs_offsetctrl_enable = "false",
//           dqs_io.dqs_out_mode = gSTRATIXII_DQS_OUT_MODE,
//           dqs_io.dqs_phase_shift = 6000,
//           dqs_io.extend_oe_disable = "true",
//           dqs_io.gated_dqs = "true",
//           dqs_io.inclk_input = "dqs_bus",
//           dqs_io.input_async_reset = "preset",
//           dqs_io.input_power_up = "high",
//           dqs_io.input_register_mode = "register",
//           dqs_io.input_sync_reset = "clear",
//           dqs_io.lpm_type = "stratixii_io",
//           dqs_io.oe_async_reset = "none",
//           dqs_io.oe_power_up = "low",
//           dqs_io.oe_register_mode = "register",
//           dqs_io.oe_sync_reset = "none",
//           dqs_io.open_drain_output = "false",
//           dqs_io.operation_mode = "bidir",
//           dqs_io.output_async_reset = "none",
//           dqs_io.output_power_up = "low",
//           dqs_io.output_register_mode = "register",
//           dqs_io.output_sync_reset = "none",
//           dqs_io.sim_dqs_delay_increment = 36,
//           dqs_io.sim_dqs_intrinsic_delay = 900,
//           dqs_io.sim_dqs_offset_increment = 0,
//           dqs_io.tie_off_oe_clock_enable = "false",
//           dqs_io.tie_off_output_clock_enable = "false";
//
//synthesis read_comments_as_HDL off

endmodule

