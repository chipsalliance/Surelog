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

module pipeline_bridge_downstream_adapter (
                                            // inputs:
                                             m1_clk,
                                             m1_endofpacket,
                                             m1_readdata,
                                             m1_readdatavalid,
                                             m1_reset_n,
                                             m1_waitrequest,
                                             s1_address,
                                             s1_arbiterlock,
                                             s1_arbiterlock2,
                                             s1_burstcount,
                                             s1_byteenable,
                                             s1_chipselect,
                                             s1_debugaccess,
                                             s1_nativeaddress,
                                             s1_read,
                                             s1_write,
                                             s1_writedata,

                                            // outputs:
                                             m1_address,
                                             m1_arbiterlock,
                                             m1_arbiterlock2,
                                             m1_burstcount,
                                             m1_byteenable,
                                             m1_chipselect,
                                             m1_debugaccess,
                                             m1_nativeaddress,
                                             m1_read,
                                             m1_write,
                                             m1_writedata,
                                             s1_endofpacket,
                                             s1_readdata,
                                             s1_readdatavalid,
                                             s1_waitrequest
                                          )
;

  output  [ 11: 0] m1_address;
  output           m1_arbiterlock;
  output           m1_arbiterlock2;
  output           m1_burstcount;
  output  [  3: 0] m1_byteenable;
  output           m1_chipselect;
  output           m1_debugaccess;
  output  [  9: 0] m1_nativeaddress;
  output           m1_read;
  output           m1_write;
  output  [ 31: 0] m1_writedata;
  output           s1_endofpacket;
  output  [ 31: 0] s1_readdata;
  output           s1_readdatavalid;
  output           s1_waitrequest;
  input            m1_clk;
  input            m1_endofpacket;
  input   [ 31: 0] m1_readdata;
  input            m1_readdatavalid;
  input            m1_reset_n;
  input            m1_waitrequest;
  input   [ 11: 0] s1_address;
  input            s1_arbiterlock;
  input            s1_arbiterlock2;
  input            s1_burstcount;
  input   [  3: 0] s1_byteenable;
  input            s1_chipselect;
  input            s1_debugaccess;
  input   [  9: 0] s1_nativeaddress;
  input            s1_read;
  input            s1_write;
  input   [ 31: 0] s1_writedata;

  reg     [ 11: 0] m1_address;
  reg              m1_arbiterlock;
  reg              m1_arbiterlock2;
  reg              m1_burstcount;
  reg     [  3: 0] m1_byteenable;
  reg              m1_chipselect;
  reg              m1_debugaccess;
  reg     [  9: 0] m1_nativeaddress;
  reg              m1_read;
  reg              m1_write;
  reg     [ 31: 0] m1_writedata;
  wire             s1_endofpacket;
  wire    [ 31: 0] s1_readdata;
  wire             s1_readdatavalid;
  wire             s1_waitrequest;
  //s1, which is an e_avalon_adapter_slave
  //m1, which is an e_avalon_adapter_master
  assign s1_endofpacket = m1_endofpacket;
  assign s1_readdata = m1_readdata;
  assign s1_readdatavalid = m1_readdatavalid;
  assign s1_waitrequest = m1_waitrequest;
  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_address <= 0;
      else if (~m1_waitrequest)
          m1_address <= s1_address;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_arbiterlock <= 0;
      else if (~m1_waitrequest)
          m1_arbiterlock <= s1_arbiterlock;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_arbiterlock2 <= 0;
      else if (~m1_waitrequest)
          m1_arbiterlock2 <= s1_arbiterlock2;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_burstcount <= 0;
      else if (~m1_waitrequest)
          m1_burstcount <= s1_burstcount;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_byteenable <= 0;
      else if (~m1_waitrequest)
          m1_byteenable <= s1_byteenable;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_chipselect <= 0;
      else if (~m1_waitrequest)
          m1_chipselect <= s1_chipselect;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_debugaccess <= 0;
      else if (~m1_waitrequest)
          m1_debugaccess <= s1_debugaccess;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_nativeaddress <= 0;
      else if (~m1_waitrequest)
          m1_nativeaddress <= s1_nativeaddress;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_read <= 0;
      else if (~m1_waitrequest)
          m1_read <= s1_read;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_write <= 0;
      else if (~m1_waitrequest)
          m1_write <= s1_write;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          m1_writedata <= 0;
      else if (~m1_waitrequest)
          m1_writedata <= s1_writedata;
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge_upstream_adapter (
                                          // inputs:
                                           m1_clk,
                                           m1_endofpacket,
                                           m1_readdata,
                                           m1_readdatavalid,
                                           m1_reset_n,
                                           m1_waitrequest,
                                           s1_address,
                                           s1_arbiterlock,
                                           s1_arbiterlock2,
                                           s1_burstcount,
                                           s1_byteenable,
                                           s1_chipselect,
                                           s1_clk,
                                           s1_debugaccess,
                                           s1_flush,
                                           s1_nativeaddress,
                                           s1_read,
                                           s1_reset_n,
                                           s1_write,
                                           s1_writedata,

                                          // outputs:
                                           m1_address,
                                           m1_arbiterlock,
                                           m1_arbiterlock2,
                                           m1_burstcount,
                                           m1_byteenable,
                                           m1_chipselect,
                                           m1_debugaccess,
                                           m1_nativeaddress,
                                           m1_read,
                                           m1_write,
                                           m1_writedata,
                                           s1_endofpacket,
                                           s1_readdata,
                                           s1_readdatavalid,
                                           s1_waitrequest
                                        )
;

  output  [ 11: 0] m1_address;
  output           m1_arbiterlock;
  output           m1_arbiterlock2;
  output           m1_burstcount;
  output  [  3: 0] m1_byteenable;
  output           m1_chipselect;
  output           m1_debugaccess;
  output  [  9: 0] m1_nativeaddress;
  output           m1_read;
  output           m1_write;
  output  [ 31: 0] m1_writedata;
  output           s1_endofpacket;
  output  [ 31: 0] s1_readdata;
  output           s1_readdatavalid;
  output           s1_waitrequest;
  input            m1_clk;
  input            m1_endofpacket;
  input   [ 31: 0] m1_readdata;
  input            m1_readdatavalid;
  input            m1_reset_n;
  input            m1_waitrequest;
  input   [ 11: 0] s1_address;
  input            s1_arbiterlock;
  input            s1_arbiterlock2;
  input            s1_burstcount;
  input   [  3: 0] s1_byteenable;
  input            s1_chipselect;
  input            s1_clk;
  input            s1_debugaccess;
  input            s1_flush;
  input   [  9: 0] s1_nativeaddress;
  input            s1_read;
  input            s1_reset_n;
  input            s1_write;
  input   [ 31: 0] s1_writedata;

  wire    [ 11: 0] m1_address;
  wire             m1_arbiterlock;
  wire             m1_arbiterlock2;
  wire             m1_burstcount;
  wire    [  3: 0] m1_byteenable;
  wire             m1_chipselect;
  wire             m1_debugaccess;
  wire    [  9: 0] m1_nativeaddress;
  wire             m1_read;
  wire             m1_write;
  wire    [ 31: 0] m1_writedata;
  reg              s1_endofpacket;
  reg     [ 31: 0] s1_readdata;
  reg              s1_readdatavalid;
  wire             s1_waitrequest;
  //s1, which is an e_avalon_adapter_slave
  //m1, which is an e_avalon_adapter_master
  always @(posedge s1_clk or negedge s1_reset_n)
    begin
      if (s1_reset_n == 0)
          s1_readdatavalid <= 0;
      else if (s1_flush)
          s1_readdatavalid <= 0;
      else 
        s1_readdatavalid <= m1_readdatavalid;
    end


  assign s1_waitrequest = m1_waitrequest;
  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          s1_endofpacket <= 0;
      else if (m1_readdatavalid)
          s1_endofpacket <= m1_endofpacket;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          s1_readdata <= 0;
      else if (m1_readdatavalid)
          s1_readdata <= m1_readdata;
    end


  assign m1_address = s1_address;
  assign m1_arbiterlock = s1_arbiterlock;
  assign m1_arbiterlock2 = s1_arbiterlock2;
  assign m1_burstcount = s1_burstcount;
  assign m1_byteenable = s1_byteenable;
  assign m1_chipselect = s1_chipselect;
  assign m1_debugaccess = s1_debugaccess;
  assign m1_nativeaddress = s1_nativeaddress;
  assign m1_read = s1_read;
  assign m1_write = s1_write;
  assign m1_writedata = s1_writedata;

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge_waitrequest_adapter (
                                             // inputs:
                                              m1_clk,
                                              m1_endofpacket,
                                              m1_readdata,
                                              m1_readdatavalid,
                                              m1_reset_n,
                                              m1_waitrequest,
                                              reset_n,
                                              s1_address,
                                              s1_arbiterlock,
                                              s1_arbiterlock2,
                                              s1_burstcount,
                                              s1_byteenable,
                                              s1_chipselect,
                                              s1_debugaccess,
                                              s1_nativeaddress,
                                              s1_read,
                                              s1_write,
                                              s1_writedata,

                                             // outputs:
                                              m1_address,
                                              m1_arbiterlock,
                                              m1_arbiterlock2,
                                              m1_burstcount,
                                              m1_byteenable,
                                              m1_chipselect,
                                              m1_debugaccess,
                                              m1_nativeaddress,
                                              m1_read,
                                              m1_write,
                                              m1_writedata,
                                              s1_endofpacket,
                                              s1_readdata,
                                              s1_readdatavalid,
                                              s1_waitrequest
                                           )
;

  output  [ 11: 0] m1_address;
  output           m1_arbiterlock;
  output           m1_arbiterlock2;
  output           m1_burstcount;
  output  [  3: 0] m1_byteenable;
  output           m1_chipselect;
  output           m1_debugaccess;
  output  [  9: 0] m1_nativeaddress;
  output           m1_read;
  output           m1_write;
  output  [ 31: 0] m1_writedata;
  output           s1_endofpacket;
  output  [ 31: 0] s1_readdata;
  output           s1_readdatavalid;
  output           s1_waitrequest;
  input            m1_clk;
  input            m1_endofpacket;
  input   [ 31: 0] m1_readdata;
  input            m1_readdatavalid;
  input            m1_reset_n;
  input            m1_waitrequest;
  input            reset_n;
  input   [ 11: 0] s1_address;
  input            s1_arbiterlock;
  input            s1_arbiterlock2;
  input            s1_burstcount;
  input   [  3: 0] s1_byteenable;
  input            s1_chipselect;
  input            s1_debugaccess;
  input   [  9: 0] s1_nativeaddress;
  input            s1_read;
  input            s1_write;
  input   [ 31: 0] s1_writedata;

  reg     [ 11: 0] d1_s1_address;
  reg              d1_s1_arbiterlock;
  reg              d1_s1_arbiterlock2;
  reg              d1_s1_burstcount;
  reg     [  3: 0] d1_s1_byteenable;
  reg              d1_s1_chipselect;
  reg              d1_s1_debugaccess;
  reg     [  9: 0] d1_s1_nativeaddress;
  reg              d1_s1_read;
  reg              d1_s1_write;
  reg     [ 31: 0] d1_s1_writedata;
  wire    [ 11: 0] m1_address;
  wire             m1_arbiterlock;
  wire             m1_arbiterlock2;
  wire             m1_burstcount;
  wire    [  3: 0] m1_byteenable;
  wire             m1_chipselect;
  wire             m1_debugaccess;
  wire    [  9: 0] m1_nativeaddress;
  wire             m1_read;
  wire             m1_write;
  wire    [ 31: 0] m1_writedata;
  wire             s1_endofpacket;
  wire    [ 31: 0] s1_readdata;
  wire             s1_readdatavalid;
  reg              s1_waitrequest;
  wire             set_use_registered;
  reg              use_registered;
  //s1, which is an e_avalon_adapter_slave
  //m1, which is an e_avalon_adapter_master
  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          s1_waitrequest <= 0;
      else 
        s1_waitrequest <= m1_waitrequest;
    end


  assign s1_endofpacket = m1_endofpacket;
  assign s1_readdata = m1_readdata;
  assign s1_readdatavalid = m1_readdatavalid;
  //set use registered, which is an e_assign
  assign set_use_registered = m1_waitrequest & ~s1_waitrequest;

  //use registered, which is an e_register
  always @(posedge m1_clk or negedge reset_n)
    begin
      if (reset_n == 0)
          use_registered <= 0;
      else if (~m1_waitrequest & s1_waitrequest)
          use_registered <= 0;
      else if (set_use_registered)
          use_registered <= -1;
    end


  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_address <= 0;
      else if (set_use_registered)
          d1_s1_address <= s1_address;
    end


  assign m1_address = (use_registered)? d1_s1_address :
    s1_address;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_arbiterlock <= 0;
      else if (set_use_registered)
          d1_s1_arbiterlock <= s1_arbiterlock;
    end


  assign m1_arbiterlock = (use_registered)? d1_s1_arbiterlock :
    s1_arbiterlock;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_arbiterlock2 <= 0;
      else if (set_use_registered)
          d1_s1_arbiterlock2 <= s1_arbiterlock2;
    end


  assign m1_arbiterlock2 = (use_registered)? d1_s1_arbiterlock2 :
    s1_arbiterlock2;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_burstcount <= 0;
      else if (set_use_registered)
          d1_s1_burstcount <= s1_burstcount;
    end


  assign m1_burstcount = (use_registered)? d1_s1_burstcount :
    s1_burstcount;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_byteenable <= 0;
      else if (set_use_registered)
          d1_s1_byteenable <= s1_byteenable;
    end


  assign m1_byteenable = (use_registered)? d1_s1_byteenable :
    s1_byteenable;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_chipselect <= 0;
      else if (set_use_registered)
          d1_s1_chipselect <= s1_chipselect;
    end


  assign m1_chipselect = (use_registered)? d1_s1_chipselect :
    s1_chipselect;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_debugaccess <= 0;
      else if (set_use_registered)
          d1_s1_debugaccess <= s1_debugaccess;
    end


  assign m1_debugaccess = (use_registered)? d1_s1_debugaccess :
    s1_debugaccess;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_nativeaddress <= 0;
      else if (set_use_registered)
          d1_s1_nativeaddress <= s1_nativeaddress;
    end


  assign m1_nativeaddress = (use_registered)? d1_s1_nativeaddress :
    s1_nativeaddress;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_read <= 0;
      else if (set_use_registered)
          d1_s1_read <= s1_read;
    end


  assign m1_read = (use_registered)? d1_s1_read :
    s1_read;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_write <= 0;
      else if (set_use_registered)
          d1_s1_write <= s1_write;
    end


  assign m1_write = (use_registered)? d1_s1_write :
    s1_write;

  always @(posedge m1_clk or negedge m1_reset_n)
    begin
      if (m1_reset_n == 0)
          d1_s1_writedata <= 0;
      else if (set_use_registered)
          d1_s1_writedata <= s1_writedata;
    end


  assign m1_writedata = (use_registered)? d1_s1_writedata :
    s1_writedata;


endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module pipeline_bridge (
                         // inputs:
                          clk,
                          m1_endofpacket,
                          m1_readdata,
                          m1_readdatavalid,
                          m1_waitrequest,
                          reset_n,
                          s1_address,
                          s1_arbiterlock,
                          s1_arbiterlock2,
                          s1_burstcount,
                          s1_byteenable,
                          s1_chipselect,
                          s1_debugaccess,
                          s1_nativeaddress,
                          s1_read,
                          s1_write,
                          s1_writedata,

                         // outputs:
                          m1_address,
                          m1_burstcount,
                          m1_byteenable,
                          m1_chipselect,
                          m1_debugaccess,
                          m1_read,
                          m1_write,
                          m1_writedata,
                          s1_endofpacket,
                          s1_readdata,
                          s1_readdatavalid,
                          s1_waitrequest
                       )
;

  output  [ 11: 0] m1_address;
  output           m1_burstcount;
  output  [  3: 0] m1_byteenable;
  output           m1_chipselect;
  output           m1_debugaccess;
  output           m1_read;
  output           m1_write;
  output  [ 31: 0] m1_writedata;
  output           s1_endofpacket;
  output  [ 31: 0] s1_readdata;
  output           s1_readdatavalid;
  output           s1_waitrequest;
  input            clk;
  input            m1_endofpacket;
  input   [ 31: 0] m1_readdata;
  input            m1_readdatavalid;
  input            m1_waitrequest;
  input            reset_n;
  input   [  9: 0] s1_address;
  input            s1_arbiterlock;
  input            s1_arbiterlock2;
  input            s1_burstcount;
  input   [  3: 0] s1_byteenable;
  input            s1_chipselect;
  input            s1_debugaccess;
  input   [  9: 0] s1_nativeaddress;
  input            s1_read;
  input            s1_write;
  input   [ 31: 0] s1_writedata;

  wire    [ 11: 0] downstream_m1_address;
  wire             downstream_m1_arbiterlock;
  wire             downstream_m1_arbiterlock2;
  wire             downstream_m1_burstcount;
  wire    [  3: 0] downstream_m1_byteenable;
  wire             downstream_m1_chipselect;
  wire             downstream_m1_debugaccess;
  wire             downstream_m1_endofpacket;
  wire    [  9: 0] downstream_m1_nativeaddress;
  wire             downstream_m1_read;
  wire    [ 31: 0] downstream_m1_readdata;
  wire             downstream_m1_readdatavalid;
  wire             downstream_m1_waitrequest;
  wire             downstream_m1_write;
  wire    [ 31: 0] downstream_m1_writedata;
  wire    [ 11: 0] downstream_s1_address;
  wire             downstream_s1_arbiterlock;
  wire             downstream_s1_arbiterlock2;
  wire             downstream_s1_burstcount;
  wire    [  3: 0] downstream_s1_byteenable;
  wire             downstream_s1_chipselect;
  wire             downstream_s1_debugaccess;
  wire             downstream_s1_endofpacket;
  wire    [  9: 0] downstream_s1_nativeaddress;
  wire             downstream_s1_read;
  wire    [ 31: 0] downstream_s1_readdata;
  wire             downstream_s1_readdatavalid;
  wire             downstream_s1_waitrequest;
  wire             downstream_s1_write;
  wire    [ 31: 0] downstream_s1_writedata;
  wire    [ 11: 0] m1_address;
  wire             m1_arbiterlock;
  wire             m1_arbiterlock2;
  wire             m1_burstcount;
  wire    [  3: 0] m1_byteenable;
  wire             m1_chipselect;
  wire             m1_debugaccess;
  wire    [  9: 0] m1_nativeaddress;
  wire             m1_read;
  wire             m1_write;
  wire    [ 31: 0] m1_writedata;
  wire             s1_endofpacket;
  wire    [ 31: 0] s1_readdata;
  wire             s1_readdatavalid;
  wire             s1_waitrequest;
  wire    [ 11: 0] upstream_m1_address;
  wire             upstream_m1_arbiterlock;
  wire             upstream_m1_arbiterlock2;
  wire             upstream_m1_burstcount;
  wire    [  3: 0] upstream_m1_byteenable;
  wire             upstream_m1_chipselect;
  wire             upstream_m1_debugaccess;
  wire             upstream_m1_endofpacket;
  wire    [  9: 0] upstream_m1_nativeaddress;
  wire             upstream_m1_read;
  wire    [ 31: 0] upstream_m1_readdata;
  wire             upstream_m1_readdatavalid;
  wire             upstream_m1_waitrequest;
  wire             upstream_m1_write;
  wire    [ 31: 0] upstream_m1_writedata;
  wire    [ 11: 0] upstream_s1_address;
  wire             upstream_s1_arbiterlock;
  wire             upstream_s1_arbiterlock2;
  wire             upstream_s1_burstcount;
  wire    [  3: 0] upstream_s1_byteenable;
  wire             upstream_s1_chipselect;
  wire             upstream_s1_debugaccess;
  wire             upstream_s1_endofpacket;
  wire    [  9: 0] upstream_s1_nativeaddress;
  wire             upstream_s1_read;
  wire    [ 31: 0] upstream_s1_readdata;
  wire             upstream_s1_readdatavalid;
  wire             upstream_s1_waitrequest;
  wire             upstream_s1_write;
  wire    [ 31: 0] upstream_s1_writedata;
  wire    [ 11: 0] waitrequest_m1_address;
  wire             waitrequest_m1_arbiterlock;
  wire             waitrequest_m1_arbiterlock2;
  wire             waitrequest_m1_burstcount;
  wire    [  3: 0] waitrequest_m1_byteenable;
  wire             waitrequest_m1_chipselect;
  wire             waitrequest_m1_debugaccess;
  wire             waitrequest_m1_endofpacket;
  wire    [  9: 0] waitrequest_m1_nativeaddress;
  wire             waitrequest_m1_read;
  wire    [ 31: 0] waitrequest_m1_readdata;
  wire             waitrequest_m1_readdatavalid;
  wire             waitrequest_m1_waitrequest;
  wire             waitrequest_m1_write;
  wire    [ 31: 0] waitrequest_m1_writedata;
  wire    [ 11: 0] waitrequest_s1_address;
  wire             waitrequest_s1_arbiterlock;
  wire             waitrequest_s1_arbiterlock2;
  wire             waitrequest_s1_burstcount;
  wire    [  3: 0] waitrequest_s1_byteenable;
  wire             waitrequest_s1_chipselect;
  wire             waitrequest_s1_debugaccess;
  wire             waitrequest_s1_endofpacket;
  wire    [  9: 0] waitrequest_s1_nativeaddress;
  wire             waitrequest_s1_read;
  wire    [ 31: 0] waitrequest_s1_readdata;
  wire             waitrequest_s1_readdatavalid;
  wire             waitrequest_s1_waitrequest;
  wire             waitrequest_s1_write;
  wire    [ 31: 0] waitrequest_s1_writedata;
  pipeline_bridge_downstream_adapter the_pipeline_bridge_downstream_adapter
    (
      .m1_address       (downstream_m1_address),
      .m1_arbiterlock   (downstream_m1_arbiterlock),
      .m1_arbiterlock2  (downstream_m1_arbiterlock2),
      .m1_burstcount    (downstream_m1_burstcount),
      .m1_byteenable    (downstream_m1_byteenable),
      .m1_chipselect    (downstream_m1_chipselect),
      .m1_clk           (clk),
      .m1_debugaccess   (downstream_m1_debugaccess),
      .m1_endofpacket   (downstream_m1_endofpacket),
      .m1_nativeaddress (downstream_m1_nativeaddress),
      .m1_read          (downstream_m1_read),
      .m1_readdata      (downstream_m1_readdata),
      .m1_readdatavalid (downstream_m1_readdatavalid),
      .m1_reset_n       (reset_n),
      .m1_waitrequest   (downstream_m1_waitrequest),
      .m1_write         (downstream_m1_write),
      .m1_writedata     (downstream_m1_writedata),
      .s1_address       (downstream_s1_address),
      .s1_arbiterlock   (downstream_s1_arbiterlock),
      .s1_arbiterlock2  (downstream_s1_arbiterlock2),
      .s1_burstcount    (downstream_s1_burstcount),
      .s1_byteenable    (downstream_s1_byteenable),
      .s1_chipselect    (downstream_s1_chipselect),
      .s1_debugaccess   (downstream_s1_debugaccess),
      .s1_endofpacket   (downstream_s1_endofpacket),
      .s1_nativeaddress (downstream_s1_nativeaddress),
      .s1_read          (downstream_s1_read),
      .s1_readdata      (downstream_s1_readdata),
      .s1_readdatavalid (downstream_s1_readdatavalid),
      .s1_waitrequest   (downstream_s1_waitrequest),
      .s1_write         (downstream_s1_write),
      .s1_writedata     (downstream_s1_writedata)
    );

  pipeline_bridge_upstream_adapter the_pipeline_bridge_upstream_adapter
    (
      .m1_address       (upstream_m1_address),
      .m1_arbiterlock   (upstream_m1_arbiterlock),
      .m1_arbiterlock2  (upstream_m1_arbiterlock2),
      .m1_burstcount    (upstream_m1_burstcount),
      .m1_byteenable    (upstream_m1_byteenable),
      .m1_chipselect    (upstream_m1_chipselect),
      .m1_clk           (clk),
      .m1_debugaccess   (upstream_m1_debugaccess),
      .m1_endofpacket   (upstream_m1_endofpacket),
      .m1_nativeaddress (upstream_m1_nativeaddress),
      .m1_read          (upstream_m1_read),
      .m1_readdata      (upstream_m1_readdata),
      .m1_readdatavalid (upstream_m1_readdatavalid),
      .m1_reset_n       (reset_n),
      .m1_waitrequest   (upstream_m1_waitrequest),
      .m1_write         (upstream_m1_write),
      .m1_writedata     (upstream_m1_writedata),
      .s1_address       (upstream_s1_address),
      .s1_arbiterlock   (upstream_s1_arbiterlock),
      .s1_arbiterlock2  (upstream_s1_arbiterlock2),
      .s1_burstcount    (upstream_s1_burstcount),
      .s1_byteenable    (upstream_s1_byteenable),
      .s1_chipselect    (upstream_s1_chipselect),
      .s1_clk           (clk),
      .s1_debugaccess   (upstream_s1_debugaccess),
      .s1_endofpacket   (upstream_s1_endofpacket),
      .s1_flush         (1'b0),
      .s1_nativeaddress (upstream_s1_nativeaddress),
      .s1_read          (upstream_s1_read),
      .s1_readdata      (upstream_s1_readdata),
      .s1_readdatavalid (upstream_s1_readdatavalid),
      .s1_reset_n       (reset_n),
      .s1_waitrequest   (upstream_s1_waitrequest),
      .s1_write         (upstream_s1_write),
      .s1_writedata     (upstream_s1_writedata)
    );

  pipeline_bridge_waitrequest_adapter the_pipeline_bridge_waitrequest_adapter
    (
      .m1_address       (waitrequest_m1_address),
      .m1_arbiterlock   (waitrequest_m1_arbiterlock),
      .m1_arbiterlock2  (waitrequest_m1_arbiterlock2),
      .m1_burstcount    (waitrequest_m1_burstcount),
      .m1_byteenable    (waitrequest_m1_byteenable),
      .m1_chipselect    (waitrequest_m1_chipselect),
      .m1_clk           (clk),
      .m1_debugaccess   (waitrequest_m1_debugaccess),
      .m1_endofpacket   (waitrequest_m1_endofpacket),
      .m1_nativeaddress (waitrequest_m1_nativeaddress),
      .m1_read          (waitrequest_m1_read),
      .m1_readdata      (waitrequest_m1_readdata),
      .m1_readdatavalid (waitrequest_m1_readdatavalid),
      .m1_reset_n       (reset_n),
      .m1_waitrequest   (waitrequest_m1_waitrequest),
      .m1_write         (waitrequest_m1_write),
      .m1_writedata     (waitrequest_m1_writedata),
      .reset_n          (reset_n),
      .s1_address       (waitrequest_s1_address),
      .s1_arbiterlock   (waitrequest_s1_arbiterlock),
      .s1_arbiterlock2  (waitrequest_s1_arbiterlock2),
      .s1_burstcount    (waitrequest_s1_burstcount),
      .s1_byteenable    (waitrequest_s1_byteenable),
      .s1_chipselect    (waitrequest_s1_chipselect),
      .s1_debugaccess   (waitrequest_s1_debugaccess),
      .s1_endofpacket   (waitrequest_s1_endofpacket),
      .s1_nativeaddress (waitrequest_s1_nativeaddress),
      .s1_read          (waitrequest_s1_read),
      .s1_readdata      (waitrequest_s1_readdata),
      .s1_readdatavalid (waitrequest_s1_readdatavalid),
      .s1_waitrequest   (waitrequest_s1_waitrequest),
      .s1_write         (waitrequest_s1_write),
      .s1_writedata     (waitrequest_s1_writedata)
    );

  assign m1_nativeaddress = downstream_m1_nativeaddress;
  assign downstream_s1_nativeaddress = upstream_m1_nativeaddress;
  assign upstream_s1_nativeaddress = waitrequest_m1_nativeaddress;
  assign waitrequest_s1_nativeaddress = s1_nativeaddress;
  assign m1_debugaccess = downstream_m1_debugaccess;
  assign downstream_s1_debugaccess = upstream_m1_debugaccess;
  assign upstream_s1_debugaccess = waitrequest_m1_debugaccess;
  assign waitrequest_s1_debugaccess = s1_debugaccess;
  assign m1_arbiterlock = downstream_m1_arbiterlock;
  assign downstream_s1_arbiterlock = upstream_m1_arbiterlock;
  assign upstream_s1_arbiterlock = waitrequest_m1_arbiterlock;
  assign waitrequest_s1_arbiterlock = s1_arbiterlock;
  assign m1_writedata = downstream_m1_writedata;
  assign downstream_s1_writedata = upstream_m1_writedata;
  assign upstream_s1_writedata = waitrequest_m1_writedata;
  assign waitrequest_s1_writedata = s1_writedata;
  assign m1_chipselect = downstream_m1_chipselect;
  assign downstream_s1_chipselect = upstream_m1_chipselect;
  assign upstream_s1_chipselect = waitrequest_m1_chipselect;
  assign waitrequest_s1_chipselect = s1_chipselect;
  assign m1_burstcount = downstream_m1_burstcount;
  assign downstream_s1_burstcount = upstream_m1_burstcount;
  assign upstream_s1_burstcount = waitrequest_m1_burstcount;
  assign waitrequest_s1_burstcount = s1_burstcount;
  assign m1_byteenable = downstream_m1_byteenable;
  assign downstream_s1_byteenable = upstream_m1_byteenable;
  assign upstream_s1_byteenable = waitrequest_m1_byteenable;
  assign waitrequest_s1_byteenable = s1_byteenable;
  assign m1_arbiterlock2 = downstream_m1_arbiterlock2;
  assign downstream_s1_arbiterlock2 = upstream_m1_arbiterlock2;
  assign upstream_s1_arbiterlock2 = waitrequest_m1_arbiterlock2;
  assign waitrequest_s1_arbiterlock2 = s1_arbiterlock2;
  assign m1_read = downstream_m1_read;
  assign downstream_s1_read = upstream_m1_read;
  assign upstream_s1_read = waitrequest_m1_read;
  assign waitrequest_s1_read = s1_read;
  assign m1_write = downstream_m1_write;
  assign downstream_s1_write = upstream_m1_write;
  assign upstream_s1_write = waitrequest_m1_write;
  assign waitrequest_s1_write = s1_write;
  assign waitrequest_s1_address = {s1_address, 2'b0};
  assign upstream_s1_address = waitrequest_m1_address;
  assign downstream_s1_address = upstream_m1_address;
  assign m1_address = downstream_m1_address;
  assign downstream_m1_readdatavalid = m1_readdatavalid;
  assign upstream_m1_readdatavalid = downstream_s1_readdatavalid;
  assign waitrequest_m1_readdatavalid = upstream_s1_readdatavalid;
  assign s1_readdatavalid = waitrequest_s1_readdatavalid;
  assign downstream_m1_waitrequest = m1_waitrequest;
  assign upstream_m1_waitrequest = downstream_s1_waitrequest;
  assign waitrequest_m1_waitrequest = upstream_s1_waitrequest;
  assign s1_waitrequest = waitrequest_s1_waitrequest;
  assign downstream_m1_endofpacket = m1_endofpacket;
  assign upstream_m1_endofpacket = downstream_s1_endofpacket;
  assign waitrequest_m1_endofpacket = upstream_s1_endofpacket;
  assign s1_endofpacket = waitrequest_s1_endofpacket;
  assign downstream_m1_readdata = m1_readdata;
  assign upstream_m1_readdata = downstream_s1_readdata;
  assign waitrequest_m1_readdata = upstream_s1_readdata;
  assign s1_readdata = waitrequest_s1_readdata;
  //s1, which is an e_avalon_slave
  //m1, which is an e_avalon_master

endmodule

