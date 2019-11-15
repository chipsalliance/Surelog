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

//----------------------------------------------------------------------------------
//Parameters:
//Number of memory clock output pairs    : 1
//----------------------------------------------------------------------------------

module ddr_sdram_auk_ddr_clk_gen (
                                   // inputs:
                                    clk,
                                    reset_n,

                                   // outputs:
                                    clk_to_sdram,
                                    clk_to_sdram_n
                                 )
;

  output           clk_to_sdram;
  output           clk_to_sdram_n;
  input            clk;
  input            reset_n;

  wire             clk_n;
  wire             clk_to_sdram;
  wire             clk_to_sdram_n;
  wire             gnd_signal;
  wire             vcc_signal;
  assign clk_n = ~clk;
  assign vcc_signal = {1{1'b1}};
  assign gnd_signal = 0;
  //------------------------------------------------------------
  //Stratix/Cyclone can drive clocks out on normal pins using
  //ALTDDIO_OUT megafunction
  //------------------------------------------------------------
  //Instantiate DDR IOs for driving the SDRAM clock off-chip

  altddio_out ddr_clk_out_p
    (
      .aclr (),
      .aset (),
      .datain_h (gnd_signal),
      .datain_l (vcc_signal),
      .dataout (clk_to_sdram),
      .oe (),
      .outclock (clk_n),
      .outclocken ()
    );

  defparam ddr_clk_out_p.extend_oe_disable = "UNUSED",
           ddr_clk_out_p.intended_device_family = "Stratix II",
           ddr_clk_out_p.invert_output = "OFF",
           ddr_clk_out_p.lpm_hint = "UNUSED",
           ddr_clk_out_p.lpm_type = "altddio_out",
           ddr_clk_out_p.oe_reg = "UNUSED",
           ddr_clk_out_p.power_up_high = "OFF",
           ddr_clk_out_p.width = 1;

  altddio_out ddr_clk_out_n
    (
      .aclr (),
      .aset (),
      .datain_h (gnd_signal),
      .datain_l (vcc_signal),
      .dataout (clk_to_sdram_n),
      .oe (),
      .outclock (clk),
      .outclocken ()
    );

  defparam ddr_clk_out_n.extend_oe_disable = "UNUSED",
           ddr_clk_out_n.intended_device_family = "Stratix II",
           ddr_clk_out_n.invert_output = "OFF",
           ddr_clk_out_n.lpm_hint = "UNUSED",
           ddr_clk_out_n.lpm_type = "altddio_out",
           ddr_clk_out_n.oe_reg = "UNUSED",
           ddr_clk_out_n.power_up_high = "OFF",
           ddr_clk_out_n.width = 1;


endmodule

