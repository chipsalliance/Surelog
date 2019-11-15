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

module custom_dma_clock_0_edge_to_pulse (
                                          // inputs:
                                           clock,
                                           data_in,
                                           reset_n,

                                          // outputs:
                                           data_out
                                        )
;

  output           data_out;
  input            clock;
  input            data_in;
  input            reset_n;

  reg              data_in_d1;
  wire             data_out;
  always @(posedge clock or negedge reset_n)
    begin
      if (reset_n == 0)
          data_in_d1 <= 0;
      else 
        data_in_d1 <= data_in;
    end


  assign data_out = data_in ^ data_in_d1;

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_clock_0_slave_FSM (
                                      // inputs:
                                       master_read_done_token,
                                       master_write_done_token,
                                       slave_clk,
                                       slave_read,
                                       slave_reset_n,
                                       slave_write,

                                      // outputs:
                                       slave_read_request,
                                       slave_waitrequest,
                                       slave_write_request
                                    )
;

  output           slave_read_request;
  output           slave_waitrequest;
  output           slave_write_request;
  input            master_read_done_token;
  input            master_write_done_token;
  input            slave_clk;
  input            slave_read;
  input            slave_reset_n;
  input            slave_write;

  reg              next_slave_read_request;
  reg     [  2: 0] next_slave_state;
  reg              next_slave_write_request;
  reg              slave_read_request;
  reg     [  2: 0] slave_state;
  reg              slave_waitrequest;
  reg              slave_write_request;
  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_read_request <= 0;
      else if (1)
          slave_read_request <= next_slave_read_request;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_write_request <= 0;
      else if (1)
          slave_write_request <= next_slave_write_request;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_state <= 3'b001;
      else if (1)
          slave_state <= next_slave_state;
    end


  always @(master_read_done_token or master_write_done_token or slave_read or slave_read_request or slave_state or slave_write or slave_write_request)
    begin
      case (slave_state) // synthesis parallel_case
      
          3'b001: begin
              //read request: go from IDLE state to READ_WAIT state
              if (slave_read)
                begin
                  next_slave_state = 3'b010;
                  slave_waitrequest = 1;
                  next_slave_read_request = !slave_read_request;
                  next_slave_write_request = slave_write_request;
                end
              else if (slave_write)
                begin
                  next_slave_state = 3'b100;
                  slave_waitrequest = 1;
                  next_slave_read_request = slave_read_request;
                  next_slave_write_request = !slave_write_request;
                end
              else 
                begin
                  next_slave_state = slave_state;
                  slave_waitrequest = 0;
                  next_slave_read_request = slave_read_request;
                  next_slave_write_request = slave_write_request;
                end
          end // 3'b001 
      
          3'b010: begin
              //stay in READ_WAIT state until master passes read done token
              if (master_read_done_token)
                begin
                  next_slave_state = 3'b001;
                  slave_waitrequest = 0;
                end
              else 
                begin
                  next_slave_state = 3'b010;
                  slave_waitrequest = 1;
                end
              next_slave_read_request = slave_read_request;
              next_slave_write_request = slave_write_request;
          end // 3'b010 
      
          3'b100: begin
              //stay in WRITE_WAIT state until master passes write done token
              if (master_write_done_token)
                begin
                  next_slave_state = 3'b001;
                  slave_waitrequest = 0;
                end
              else 
                begin
                  next_slave_state = 3'b100;
                  slave_waitrequest = 1;
                end
              next_slave_read_request = slave_read_request;
              next_slave_write_request = slave_write_request;
          end // 3'b100 
      
          default: begin
              next_slave_state = 3'b001;
              slave_waitrequest = 0;
              next_slave_read_request = slave_read_request;
              next_slave_write_request = slave_write_request;
          end // default
      
      endcase // slave_state
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_clock_0_master_FSM (
                                       // inputs:
                                        master_clk,
                                        master_reset_n,
                                        master_waitrequest,
                                        slave_read_request_token,
                                        slave_write_request_token,

                                       // outputs:
                                        master_read,
                                        master_read_done,
                                        master_write,
                                        master_write_done
                                     )
;

  output           master_read;
  output           master_read_done;
  output           master_write;
  output           master_write_done;
  input            master_clk;
  input            master_reset_n;
  input            master_waitrequest;
  input            slave_read_request_token;
  input            slave_write_request_token;

  reg              master_read;
  reg              master_read_done;
  reg     [  2: 0] master_state;
  reg              master_write;
  reg              master_write_done;
  reg              next_master_read;
  reg              next_master_read_done;
  reg     [  2: 0] next_master_state;
  reg              next_master_write;
  reg              next_master_write_done;
  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_read_done <= 0;
      else if (1)
          master_read_done <= next_master_read_done;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_write_done <= 0;
      else if (1)
          master_write_done <= next_master_write_done;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_read <= 0;
      else if (1)
          master_read <= next_master_read;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_write <= 0;
      else if (1)
          master_write <= next_master_write;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_state <= 3'b001;
      else if (1)
          master_state <= next_master_state;
    end


  always @(master_read or master_read_done or master_state or master_waitrequest or master_write or master_write_done or slave_read_request_token or slave_write_request_token)
    begin
      case (master_state) // synthesis parallel_case
      
          3'b001: begin
              //if read request token from slave then goto READ_WAIT state
              if (slave_read_request_token)
                begin
                  next_master_state = 3'b010;
                  next_master_read = 1;
                  next_master_write = 0;
                end
              else if (slave_write_request_token)
                begin
                  next_master_state = 3'b100;
                  next_master_read = 0;
                  next_master_write = 1;
                end
              else 
                begin
                  next_master_state = master_state;
                  next_master_read = 0;
                  next_master_write = 0;
                end
              next_master_read_done = master_read_done;
              next_master_write_done = master_write_done;
          end // 3'b001 
      
          3'b010: begin
              //stay in READ_WAIT state until master wait is deasserted
              if (!master_waitrequest)
                begin
                  next_master_state = 3'b001;
                  next_master_read_done = !master_read_done;
                  next_master_read = 0;
                end
              else 
                begin
                  next_master_state = 3'b010;
                  next_master_read_done = master_read_done;
                  next_master_read = master_read;
                end
              next_master_write_done = master_write_done;
              next_master_write = 0;
          end // 3'b010 
      
          3'b100: begin
              //stay in WRITE_WAIT state until slave wait is deasserted
              if (!master_waitrequest)
                begin
                  next_master_state = 3'b001;
                  next_master_write = 0;
                  next_master_write_done = !master_write_done;
                end
              else 
                begin
                  next_master_state = 3'b100;
                  next_master_write = master_write;
                  next_master_write_done = master_write_done;
                end
              next_master_read_done = master_read_done;
              next_master_read = 0;
          end // 3'b100 
      
          default: begin
              next_master_state = 3'b001;
              next_master_write = 0;
              next_master_write_done = master_write_done;
              next_master_read = 0;
              next_master_read_done = master_read_done;
          end // default
      
      endcase // master_state
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module custom_dma_clock_0_bit_pipe (
                                     // inputs:
                                      clk1,
                                      clk2,
                                      data_in,
                                      reset_clk1_n,
                                      reset_clk2_n,

                                     // outputs:
                                      data_out
                                   )
;

  output           data_out;
  input            clk1;
  input            clk2;
  input            data_in;
  input            reset_clk1_n;
  input            reset_clk2_n;

  reg              data_in_d1 /* synthesis ALTERA_ATTRIBUTE = "{-to \"*\"} CUT=ON ; PRESERVE_REGISTER=ON"  */;
  reg              data_out /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  always @(posedge clk1 or negedge reset_clk1_n)
    begin
      if (reset_clk1_n == 0)
          data_in_d1 <= 0;
      else 
        data_in_d1 <= data_in;
    end


  always @(posedge clk2 or negedge reset_clk2_n)
    begin
      if (reset_clk2_n == 0)
          data_out <= 0;
      else 
        data_out <= data_in_d1;
    end



endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

//Clock Domain Crossing Adaptercustom_dma_clock_0


module custom_dma_clock_0 (
                            // inputs:
                             master_clk,
                             master_endofpacket,
                             master_readdata,
                             master_reset_n,
                             master_waitrequest,
                             slave_address,
                             slave_byteenable,
                             slave_clk,
                             slave_nativeaddress,
                             slave_read,
                             slave_reset_n,
                             slave_write,
                             slave_writedata,

                            // outputs:
                             master_address,
                             master_byteenable,
                             master_nativeaddress,
                             master_read,
                             master_write,
                             master_writedata,
                             slave_endofpacket,
                             slave_readdata,
                             slave_waitrequest
                          )
;

  output  [  3: 0] master_address;
  output  [  1: 0] master_byteenable;
  output  [  2: 0] master_nativeaddress;
  output           master_read;
  output           master_write;
  output  [ 15: 0] master_writedata;
  output           slave_endofpacket;
  output  [ 15: 0] slave_readdata;
  output           slave_waitrequest;
  input            master_clk;
  input            master_endofpacket;
  input   [ 15: 0] master_readdata;
  input            master_reset_n;
  input            master_waitrequest;
  input   [  3: 0] slave_address;
  input   [  1: 0] slave_byteenable;
  input            slave_clk;
  input   [  2: 0] slave_nativeaddress;
  input            slave_read;
  input            slave_reset_n;
  input            slave_write;
  input   [ 15: 0] slave_writedata;

  reg     [  3: 0] master_address /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  reg     [  1: 0] master_byteenable /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  reg     [  2: 0] master_nativeaddress /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  wire             master_read;
  wire             master_read_done;
  wire             master_read_done_sync;
  wire             master_read_done_token;
  wire             master_write;
  wire             master_write_done;
  wire             master_write_done_sync;
  wire             master_write_done_token;
  reg     [ 15: 0] master_writedata /* synthesis ALTERA_ATTRIBUTE = "PRESERVE_REGISTER=ON"  */;
  reg     [  3: 0] slave_address_d1 /* synthesis ALTERA_ATTRIBUTE = "{-to \"*\"} CUT=ON ; PRESERVE_REGISTER=ON"  */;
  reg     [  1: 0] slave_byteenable_d1 /* synthesis ALTERA_ATTRIBUTE = "{-to \"*\"} CUT=ON ; PRESERVE_REGISTER=ON"  */;
  wire             slave_endofpacket;
  reg     [  2: 0] slave_nativeaddress_d1 /* synthesis ALTERA_ATTRIBUTE = "{-to \"*\"} CUT=ON ; PRESERVE_REGISTER=ON"  */;
  wire             slave_read_request;
  wire             slave_read_request_sync;
  wire             slave_read_request_token;
  reg     [ 15: 0] slave_readdata /* synthesis ALTERA_ATTRIBUTE = "{-from \"*\"} CUT=ON"  */;
  reg     [ 15: 0] slave_readdata_p1;
  wire             slave_waitrequest;
  wire             slave_write_request;
  wire             slave_write_request_sync;
  wire             slave_write_request_token;
  reg     [ 15: 0] slave_writedata_d1 /* synthesis ALTERA_ATTRIBUTE = "{-to \"*\"} CUT=ON ; PRESERVE_REGISTER=ON"  */;
  //in, which is an e_avalon_slave
  //out, which is an e_avalon_master
  altera_std_synchronizer the_altera_std_synchronizer
    (
      .clk (slave_clk),
      .din (master_read_done),
      .dout (master_read_done_sync),
      .reset_n (slave_reset_n)
    );

  defparam the_altera_std_synchronizer.depth = 2;

  altera_std_synchronizer the_altera_std_synchronizer1
    (
      .clk (slave_clk),
      .din (master_write_done),
      .dout (master_write_done_sync),
      .reset_n (slave_reset_n)
    );

  defparam the_altera_std_synchronizer1.depth = 2;

  //read_done_edge_to_pulse, which is an e_instance
  custom_dma_clock_0_edge_to_pulse read_done_edge_to_pulse
    (
      .clock    (slave_clk),
      .data_in  (master_read_done_sync),
      .data_out (master_read_done_token),
      .reset_n  (slave_reset_n)
    );

  //write_done_edge_to_pulse, which is an e_instance
  custom_dma_clock_0_edge_to_pulse write_done_edge_to_pulse
    (
      .clock    (slave_clk),
      .data_in  (master_write_done_sync),
      .data_out (master_write_done_token),
      .reset_n  (slave_reset_n)
    );

  //slave_FSM, which is an e_instance
  custom_dma_clock_0_slave_FSM slave_FSM
    (
      .master_read_done_token  (master_read_done_token),
      .master_write_done_token (master_write_done_token),
      .slave_clk               (slave_clk),
      .slave_read              (slave_read),
      .slave_read_request      (slave_read_request),
      .slave_reset_n           (slave_reset_n),
      .slave_waitrequest       (slave_waitrequest),
      .slave_write             (slave_write),
      .slave_write_request     (slave_write_request)
    );

  altera_std_synchronizer the_altera_std_synchronizer2
    (
      .clk (master_clk),
      .din (slave_read_request),
      .dout (slave_read_request_sync),
      .reset_n (master_reset_n)
    );

  defparam the_altera_std_synchronizer2.depth = 2;

  altera_std_synchronizer the_altera_std_synchronizer3
    (
      .clk (master_clk),
      .din (slave_write_request),
      .dout (slave_write_request_sync),
      .reset_n (master_reset_n)
    );

  defparam the_altera_std_synchronizer3.depth = 2;

  //read_request_edge_to_pulse, which is an e_instance
  custom_dma_clock_0_edge_to_pulse read_request_edge_to_pulse
    (
      .clock    (master_clk),
      .data_in  (slave_read_request_sync),
      .data_out (slave_read_request_token),
      .reset_n  (master_reset_n)
    );

  //write_request_edge_to_pulse, which is an e_instance
  custom_dma_clock_0_edge_to_pulse write_request_edge_to_pulse
    (
      .clock    (master_clk),
      .data_in  (slave_write_request_sync),
      .data_out (slave_write_request_token),
      .reset_n  (master_reset_n)
    );

  //master_FSM, which is an e_instance
  custom_dma_clock_0_master_FSM master_FSM
    (
      .master_clk                (master_clk),
      .master_read               (master_read),
      .master_read_done          (master_read_done),
      .master_reset_n            (master_reset_n),
      .master_waitrequest        (master_waitrequest),
      .master_write              (master_write),
      .master_write_done         (master_write_done),
      .slave_read_request_token  (slave_read_request_token),
      .slave_write_request_token (slave_write_request_token)
    );

  //endofpacket_bit_pipe, which is an e_instance
  custom_dma_clock_0_bit_pipe endofpacket_bit_pipe
    (
      .clk1         (slave_clk),
      .clk2         (master_clk),
      .data_in      (master_endofpacket),
      .data_out     (slave_endofpacket),
      .reset_clk1_n (slave_reset_n),
      .reset_clk2_n (master_reset_n)
    );

  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          slave_readdata_p1 <= 0;
      else if (master_read & ~master_waitrequest)
          slave_readdata_p1 <= master_readdata;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_readdata <= 0;
      else 
        slave_readdata <= slave_readdata_p1;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_writedata_d1 <= 0;
      else 
        slave_writedata_d1 <= slave_writedata;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_writedata <= 0;
      else 
        master_writedata <= slave_writedata_d1;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_address_d1 <= 0;
      else 
        slave_address_d1 <= slave_address;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_address <= 0;
      else 
        master_address <= slave_address_d1;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_nativeaddress_d1 <= 0;
      else 
        slave_nativeaddress_d1 <= slave_nativeaddress;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_nativeaddress <= 0;
      else 
        master_nativeaddress <= slave_nativeaddress_d1;
    end


  always @(posedge slave_clk or negedge slave_reset_n)
    begin
      if (slave_reset_n == 0)
          slave_byteenable_d1 <= 0;
      else 
        slave_byteenable_d1 <= slave_byteenable;
    end


  always @(posedge master_clk or negedge master_reset_n)
    begin
      if (master_reset_n == 0)
          master_byteenable <= 0;
      else 
        master_byteenable <= slave_byteenable_d1;
    end



endmodule

