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

module ddr_sdram_example_driver (
                                  // inputs:
                                   clk,
                                   local_rdata,
                                   local_rdata_valid,
                                   local_ready,
                                   reset_n,

                                  // outputs:
                                   local_bank_addr,
                                   local_be,
                                   local_burstbegin,
                                   local_col_addr,
                                   local_cs_addr,
                                   local_read_req,
                                   local_row_addr,
                                   local_size,
                                   local_wdata,
                                   local_write_req,
                                   pnf_per_byte,
                                   pnf_persist,
                                   test_complete
                                )
  /* synthesis ALTERA_ATTRIBUTE = "MESSAGE_DISABLE=12300;MESSAGE_DISABLE=14130;MESSAGE_DISABLE=14110" */ ;

  output  [  1: 0] local_bank_addr;
  output  [  3: 0] local_be;
  output           local_burstbegin;
  output  [  8: 0] local_col_addr;
  output           local_cs_addr;
  output           local_read_req;
  output  [ 12: 0] local_row_addr;
  output  [  2: 0] local_size;
  output  [ 31: 0] local_wdata;
  output           local_write_req;
  output  [  3: 0] pnf_per_byte;
  output           pnf_persist;
  output           test_complete;
  input            clk;
  input   [ 31: 0] local_rdata;
  input            local_rdata_valid;
  input            local_ready;
  input            reset_n;

  wire    [  2: 0] LOCAL_BURST_LEN_s;
  wire    [  1: 0] MAX_BANK;
  wire             MAX_CHIPSEL;
  wire    [  8: 0] MAX_COL;
  wire    [ 12: 0] MAX_ROW;
  wire             MIN_CHIPSEL;
  wire             avalon_burst_mode;
  wire             avalon_read_burst_max_address;
  reg     [  1: 0] bank_addr;
  wire    [  3: 0] be;
  reg     [  2: 0] burst_beat_count;
  reg              burst_begin;
  reg     [  8: 0] col_addr;
  wire    [  3: 0] compare;
  reg     [  3: 0] compare_reg;
  reg     [  3: 0] compare_valid;
  reg     [  3: 0] compare_valid_reg;
  reg              cs_addr;
  wire    [ 31: 0] dgen_data;
  reg              dgen_enable;
  reg     [ 31: 0] dgen_ldata;
  reg              dgen_load;
  wire             dgen_pause;
  reg              last_rdata_valid;
  reg              last_wdata_req;
  wire    [  1: 0] local_bank_addr;
  wire    [  3: 0] local_be;
  wire             local_burstbegin;
  wire    [  8: 0] local_col_addr;
  wire             local_cs_addr;
  wire             local_read_req;
  wire    [ 12: 0] local_row_addr;
  wire    [  2: 0] local_size;
  wire    [ 31: 0] local_wdata;
  wire             local_write_req;
  wire    [  3: 0] pnf_per_byte;
  reg              pnf_persist;
  reg              pnf_persist1;
  wire             reached_max_address;
  reg              reached_max_count;
  reg              read_req;
  reg     [  7: 0] reads_remaining;
  reg              reset_address;
  reg     [ 12: 0] row_addr;
  wire    [  2: 0] size;
  reg     [  3: 0] state;
  reg              test_complete;
  reg              wait_first_write_data;
  wire    [ 31: 0] wdata;
  wire             wdata_req;
  reg              write_req;
  reg     [  7: 0] writes_remaining;
  assign local_burstbegin = burst_begin;
  assign avalon_burst_mode = 1;
  assign MIN_CHIPSEL = 0;
  assign MAX_CHIPSEL = 0;
  assign MAX_ROW = 3;
  assign MAX_BANK = 3;
  assign MAX_COL = 16;
  //


  assign local_cs_addr = cs_addr;

  assign local_row_addr = row_addr;
  assign local_bank_addr = bank_addr;
  assign local_col_addr = col_addr;
  assign local_write_req = write_req;
  assign local_read_req = read_req;
  assign local_wdata = wdata;
  assign wdata = dgen_data;
  //The LOCAL_BURST_LEN_s is a signal used insted of the parameter LOCAL_BURST_LEN
  assign LOCAL_BURST_LEN_s = 4;
  //LOCAL INTERFACE (AVALON)
  assign wdata_req = write_req && local_ready;

  // Generate new data (enable lfsr) when writing or reading valid data
  assign dgen_pause = ~ (wdata_req | local_rdata_valid);

  //


  assign local_be = be;

  assign be = {4{1'b1}};
  assign pnf_per_byte = compare_valid_reg;
  assign local_size = size;
  //FIX
  assign size = LOCAL_BURST_LEN_s[2 : 0];

  assign reached_max_address = (col_addr >= (MAX_COL - (4 * 2))) && (row_addr == MAX_ROW) && (bank_addr == MAX_BANK) && (cs_addr == MAX_CHIPSEL);
  assign avalon_read_burst_max_address = (col_addr >= (MAX_COL - (4 * 4))) && (row_addr == MAX_ROW) && (bank_addr == MAX_BANK) && (cs_addr == MAX_CHIPSEL);
  example_lfsr8 LFSRGEN_0_lfsr_inst
    (
      .clk (clk),
      .data (dgen_data[7 : 0]),
      .enable (dgen_enable),
      .ldata (dgen_ldata[7 : 0]),
      .load (dgen_load),
      .pause (dgen_pause),
      .reset_n (reset_n)
    );

  defparam LFSRGEN_0_lfsr_inst.seed = 1;

  // 8 bit comparator per local byte lane
  assign compare[0] = dgen_data[7 : 0] == local_rdata[7 : 0];

  example_lfsr8 LFSRGEN_1_lfsr_inst
    (
      .clk (clk),
      .data (dgen_data[15 : 8]),
      .enable (dgen_enable),
      .ldata (dgen_ldata[15 : 8]),
      .load (dgen_load),
      .pause (dgen_pause),
      .reset_n (reset_n)
    );

  defparam LFSRGEN_1_lfsr_inst.seed = 11;

  // 8 bit comparator per local byte lane
  assign compare[1] = dgen_data[15 : 8] == local_rdata[15 : 8];

  example_lfsr8 LFSRGEN_2_lfsr_inst
    (
      .clk (clk),
      .data (dgen_data[23 : 16]),
      .enable (dgen_enable),
      .ldata (dgen_ldata[23 : 16]),
      .load (dgen_load),
      .pause (dgen_pause),
      .reset_n (reset_n)
    );

  defparam LFSRGEN_2_lfsr_inst.seed = 21;

  // 8 bit comparator per local byte lane
  assign compare[2] = dgen_data[23 : 16] == local_rdata[23 : 16];

  example_lfsr8 LFSRGEN_3_lfsr_inst
    (
      .clk (clk),
      .data (dgen_data[31 : 24]),
      .enable (dgen_enable),
      .ldata (dgen_ldata[31 : 24]),
      .load (dgen_load),
      .pause (dgen_pause),
      .reset_n (reset_n)
    );

  defparam LFSRGEN_3_lfsr_inst.seed = 31;

  // 8 bit comparator per local byte lane
  assign compare[3] = dgen_data[31 : 24] == local_rdata[31 : 24];

  //
  //-----------------------------------------------------------------
  //Main clocked process
  //-----------------------------------------------------------------
  //Read / Write control state machine & address counter
  //-----------------------------------------------------------------
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          //Reset - asynchronously force all register outputs LOW
          state <= 1'b0;

          write_req <= 1'b0;
          read_req <= 1'b0;
          burst_begin <= 0;
          burst_beat_count <= 0;
          cs_addr <= 0;
          row_addr <= 0;
          bank_addr <= 0;
          col_addr <= 0;
          dgen_enable <= 1'b0;
          dgen_load <= 1'b0;
          wait_first_write_data <= 1'b0;
          reached_max_count <= 1'b0;
          test_complete <= 1'b0;
          writes_remaining <= 0;
          reads_remaining <= 0;
          reset_address <= 1'b0;
        end
      else 
        begin
          reset_address <= 1'b0;
          reached_max_count <= reached_max_address;
          read_req <= 1'b0;
          write_req <= 1'b0;
          dgen_load <= 1'b0;
          test_complete <= 1'b0;
          if (last_wdata_req)
              wait_first_write_data <= 0;
          if (write_req && local_ready)
            begin
              if (wdata_req)
                  writes_remaining <= writes_remaining + (size - 1);
              else 
                writes_remaining <= writes_remaining + size;
            end
          else if ((wdata_req) && (writes_remaining > 0))
              //size
              writes_remaining <= writes_remaining - 1'b1;

          else 
            writes_remaining <= writes_remaining;
          if (read_req && local_ready)
            begin
              if (local_rdata_valid)
                  reads_remaining <= reads_remaining + (size - 1);
              else 
                reads_remaining <= reads_remaining + size;
            end
          else if ((local_rdata_valid) && (reads_remaining > 0))
              reads_remaining <= reads_remaining - 1'b1;
          else 
            reads_remaining <= reads_remaining;
          case (state)
          
              4'd0: begin
                  reached_max_count <= 0;
                  if (avalon_burst_mode == 0)
                    begin
                      if (1 == 0)
                          state <= 5;
                      else 
                        state <= 1;
                    end
                  else 
                    begin
                      burst_begin <= 1;
                      write_req <= 1'b1;
                      state <= 10;
                    end
                  dgen_enable <= 1'b1;
                  //Reset just in case!
                  writes_remaining <= 0;
          
                  reads_remaining <= 0;
              end // 4'd0 
          
              4'd1: begin
                  write_req <= 1'b1;
                  dgen_enable <= 1'b1;
                  if (local_ready && write_req)
                      if (reached_max_count)
                        begin
                          state <= 2;
                          write_req <= 1'b0;
                          reset_address <= 1'b1;
                        end
              end // 4'd1 
          
              4'd10: begin
                  reset_address <= 1'b0;
                  write_req <= 1'b1;
                  burst_begin <= 0;
                  if (local_ready)
                    begin
                      burst_beat_count <= burst_beat_count + 1;
                      state <= 12;
                    end
              end // 4'd10 
          
              4'd11: begin
                  reset_address <= 1'b0;
                  read_req <= 1'b1;
                  if (! local_ready)
                    begin
                      burst_begin <= 0;
                      state <= 13;
                    end
                  if (avalon_read_burst_max_address)
                    begin
                      read_req <= 1'b0;
                      reset_address <= 1'b1;
                      test_complete <= 1'b1;
                      burst_beat_count <= 0;
                      state <= 4;
                    end
              end // 4'd11 
          
              4'd12: begin
                  write_req <= 1'b1;
                  if (local_ready)
                      if (burst_beat_count == size - 1)
                        begin
                          if (reached_max_count)
                            begin
                              write_req <= 1'b0;
                              burst_beat_count <= 0;
                              reset_address <= 1'b1;
                              dgen_enable <= 1'b0;
                              state <= 2;
                            end
                          else 
                            begin
                              burst_begin <= 1;
                              write_req <= 1'b1;
                              burst_beat_count <= 0;
                              state <= 10;
                            end
                        end
                      else 
                        burst_beat_count <= burst_beat_count + 1;
              end // 4'd12 
          
              4'd13: begin
                  read_req <= 1'b1;
                  if (local_ready)
                    begin
                      burst_begin <= 1;
                      read_req <= 1'b1;
                      state <= 11;
                    end
                  else if (avalon_read_burst_max_address)
                    begin
                      read_req <= 1'b0;
                      reset_address <= 1'b1;
                      test_complete <= 1'b1;
                      dgen_enable <= 1'b0;
                      state <= 4;
                    end
              end // 4'd13 
          
              4'd2: begin
                  if (avalon_burst_mode == 0)
                    begin
                      if (writes_remaining == 0)
                        begin
                          state <= 3;
                          dgen_enable <= 1'b0;
                        end
                    end
                  else 
                    begin
                      dgen_enable <= 1'b1;
                      burst_begin <= 1;
                      read_req <= 1'b1;
                      reset_address <= 1'b0;
                      state <= 11;
                    end
              end // 4'd2 
          
              4'd3: begin
                  read_req <= 1'b1;
                  dgen_enable <= 1'b1;
                  if (local_ready && read_req)
                      if (reached_max_count)
                        begin
                          state <= 4;
                          read_req <= 1'b0;
                          reset_address <= 1'b1;
                        end
              end // 4'd3 
          
              4'd4: begin
                  if (avalon_burst_mode == 0)
                    begin
                      if (reads_remaining == 0)
                        begin
                          state <= 0;
                          dgen_enable <= 1'b0;
                          test_complete <= 1'b1;
                        end
                    end
                  else 
                    begin
                      if (reads_remaining == 1)
                          dgen_enable <= 1'b0;
                      if (reads_remaining == 0)
                        begin
                          dgen_enable <= 1'b1;
                          burst_begin <= 1;
                          write_req <= 1'b1;
                          read_req <= 1'b0;
                          reset_address <= 1'b0;
                          burst_beat_count <= 0;
                          state <= 10;
                        end
                    end
              end // 4'd4 
          
              4'd5: begin
                  write_req <= 1'b1;
                  dgen_enable <= 1'b1;
                  wait_first_write_data <= 1'b1;
                  if (local_ready)
                    begin
                      state <= 6;
                      write_req <= 1'b0;
                    end
              end // 4'd5 
          
              4'd6: begin
                  if (writes_remaining == 0)
                    begin
                      state <= 7;
                      dgen_load <= 1'b1;
                    end
              end // 4'd6 
          
              4'd7: begin
                  read_req <= 1'b1;
                  dgen_enable <= 1'b1;
                  if (local_ready)
                    begin
                      state <= 8;
                      read_req <= 1'b0;
                    end
              end // 4'd7 
          
              4'd8: begin
                  if (reads_remaining == 0)
                      if (1)
                        begin
                          reset_address <= 1'b1;
                          dgen_enable <= 1'b0;
                          state <= 0;
                          test_complete <= 1'b1;
                        end
                      else 
                        state <= 5;
              end // 4'd8 
          
          endcase // state
          if (reset_address)
            begin
              //(others => '0')
              cs_addr <= MIN_CHIPSEL;

              row_addr <= 0;
              bank_addr <= 0;
              col_addr <= 0;
            end
          else if ((((local_ready && write_req) && (state == 1))) || ((local_ready && read_req) && (state == 3)) || ((local_ready) && ((state == 7) || (state == 10) || (state == 11) || (state == 13))))
              if (col_addr >= MAX_COL)
                begin
                  col_addr <= 0;
                  if (row_addr == MAX_ROW)
                    begin
                      row_addr <= 0;
                      if (bank_addr == MAX_BANK)
                        begin
                          bank_addr <= 0;
                          if (cs_addr == MAX_CHIPSEL)
                              //reached_max_count <= TRUE
                              //(others => '0')
                              cs_addr <= MIN_CHIPSEL;

                          else 
                            cs_addr <= cs_addr + 1'b1;
                        end
                      else 
                        bank_addr <= bank_addr + 1'b1;
                    end
                  else 
                    row_addr <= row_addr + 1'b1;
                end
              else 
                col_addr <= col_addr + (4 * 2);
        end
    end


  //------------------------------------------------------------
  //LFSR re-load data storage
  //Comparator masking and test pass signal generation
  //------------------------------------------------------------
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
        begin
          dgen_ldata <= 0;
          last_wdata_req <= 1'b0;
          //all ones
          compare_valid <= {4{1'b1}};

          //all ones
          compare_valid_reg <= {4{1'b1}};

          pnf_persist <= 1'b1;
          pnf_persist1 <= 1'b1;
          //all ones
          compare_reg <= {4{1'b1}};

          last_rdata_valid <= 1'b0;
        end
      else 
        begin
          last_wdata_req <= wdata_req;
          last_rdata_valid <= local_rdata_valid;
          compare_reg <= compare;
          if (wdata_req)
              //Store the data from the first write in a burst 
              //Used to reload the lfsr for the first read in a burst in WRITE 1, READ 1 mode

              if (wait_first_write_data)
                  dgen_ldata <= dgen_data;
          //Enable the comparator result when read data is valid
          if (last_rdata_valid)
              compare_valid <= compare_reg;
          //Create the overall persistent passnotfail output
          if (~&compare_valid)
              pnf_persist1 <= 1'b0;
          //Extra register stage to help Tco / Fmax on comparator output pins
          compare_valid_reg <= compare_valid;

          pnf_persist <= pnf_persist1;
        end
    end



endmodule

