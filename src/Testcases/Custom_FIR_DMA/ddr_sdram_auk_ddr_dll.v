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

module ddr_sdram_auk_ddr_dll (
                               // inputs:
                                addnsub,
                                clk,
                                offset,
                                reset_n,
                                stratix_dll_control,

                               // outputs:
                                delayctrlout,
                                dqsupdate
                             )
  /* synthesis ALTERA_ATTRIBUTE = "MESSAGE_DISABLE=14130;MESSAGE_DISABLE=14110" */ ;

  output  [  5: 0] delayctrlout;
  output           dqsupdate;
  input            addnsub;
  input            clk;
  input   [  5: 0] offset;
  input            reset_n;
  input            stratix_dll_control;

  wire    [  5: 0] delayctrlout;
  wire             dqsupdate;
  //------------------------------------------------------------
  //Instantiate Stratix II DLL
  //------------------------------------------------------------

  stratixii_dll dll
    (
      .addnsub (addnsub),
      .aload (),
      .clk (clk),
      .delayctrlout (delayctrlout),
      .devclrn (),
      .devpor (),
      .dqsupdate (dqsupdate),
      .offset (offset),
      .offsetctrlout (),
      .upndnin (),
      .upndninclkena (),
      .upndnout ()
    );

  defparam dll.delay_buffer_mode = "low",
           dll.delay_chain_length = 12,
           dll.delayctrlout_mode = "normal",
           dll.input_frequency = "10000ps",
           dll.jitter_reduction = "false",
           dll.lpm_type = "stratixii_dll",
           dll.offsetctrlout_mode = "dynamic_addnsub",
           dll.sim_loop_delay_increment = 144,
           dll.sim_loop_intrinsic_delay = 3600,
           dll.sim_valid_lock = 1,
           dll.sim_valid_lockcount = 27,
           dll.static_delay_ctrl = 0,
           dll.static_offset = "0",
           dll.use_upndnin = "false",
           dll.use_upndninclkena = "false";


endmodule

