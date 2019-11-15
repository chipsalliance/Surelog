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

module pll (
             // inputs:
              address,
              chipselect,
              clk,
              read,
              reset_n,
              write,
              writedata,

             // outputs:
              c0,
              c1,
              c2,
              readdata,
              resetrequest
           )
;

  output           c0;
  output           c1;
  output           c2;
  output  [ 15: 0] readdata;
  output           resetrequest;
  input   [  2: 0] address;
  input            chipselect;
  input            clk;
  input            read;
  input            reset_n;
  input            write;
  input   [ 15: 0] writedata;

  wire             always_one;
  wire             areset_n;
  wire             c0;
  wire             c1;
  wire             c2;
  wire             control_reg_en;
  wire    [ 15: 0] control_reg_in;
  reg     [ 15: 0] control_reg_out;
  reg              count_done;
  reg     [  5: 0] countup;
  wire             inclk0;
  reg              not_areset /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  wire    [ 15: 0] readdata;
  wire             resetrequest;
  wire    [ 15: 0] status_reg_in;
  reg     [ 15: 0] status_reg_out;
initial
  begin
    countup = 1'b0;
    count_done = 1'b0;
    not_areset = 1'b0;
  end
  assign status_reg_in[15 : 1] = 15'b000000000000000;
  assign resetrequest = ~count_done;
  //Up counter that stops counting when it reaches max value
  always @(posedge clk or negedge areset_n)
    begin
      if (areset_n == 0)
          countup <= 0;
      else if (count_done != 1'b1)
          countup <= countup + 1;
    end


  //Count_done signal, which is also the resetrequest_n
  always @(posedge clk or negedge areset_n)
    begin
      if (areset_n == 0)
          count_done <= 0;
      else if (countup == 6'b111111)
          count_done <= 1'b1;
    end


  //Creates a reset generator that will reset internal counters that are independent of global system reset
  always @(posedge clk or negedge 1'b1)
    begin
      if (1'b1 == 0)
          not_areset <= 0;
      else 
        not_areset <= always_one;
    end


  assign always_one = 1'b1;
  assign status_reg_in[0] = 1'b0;
  assign areset_n = not_areset;
  assign inclk0 = clk;
  //Mux status and control registers to the readdata output using address as select
  assign readdata = (address[0] == 0)? status_reg_out :
    ({control_reg_out[15 : 2], ~control_reg_out[1], control_reg_out[0]} );

  //Status register - Read-Only
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          status_reg_out <= 0;
      else 
        status_reg_out <= status_reg_in;
    end


  //Control register - R/W
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          control_reg_out <= 0;
      else if (control_reg_en)
          control_reg_out <= {control_reg_in[15 : 2], ~control_reg_in[1], control_reg_in[0]};
    end


  assign control_reg_in = writedata;
  assign control_reg_en = (address == 3'b001) && write && chipselect;
  //s1, which is an e_avalon_slave
  altpllpll the_pll
    (
      .c0 (c0),
      .c1 (c1),
      .c2 (c2),
      .inclk0 (inclk0)
    );



endmodule

