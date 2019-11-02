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

module ddr_sdram_test_component_ram_module (
                                             // inputs:
                                              data,
                                              rdaddress,
                                              rdclken,
                                              wraddress,
                                              wrclock,
                                              wren,

                                             // outputs:
                                              q
                                           )
;

  output  [ 31: 0] q;
  input   [ 31: 0] data;
  input   [ 23: 0] rdaddress;
  input            rdclken;
  input   [ 23: 0] wraddress;
  input            wrclock;
  input            wren;

  reg     [ 31: 0] mem_array [16777215: 0];
  wire    [ 31: 0] q;
  reg     [ 23: 0] read_address;

//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  always @(rdaddress)
    begin
      read_address = rdaddress;
    end


  // Data read is asynchronous.
  assign q = mem_array[read_address];

initial
    $readmemh("ddr_sdram.dat", mem_array);
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
//      .wraddress (wraddress),
//      .wrclock (wrclock),
//      .wren (wren)
//    );
//
//  defparam lpm_ram_dp_component.lpm_file = "UNUSED",
//           lpm_ram_dp_component.lpm_hint = "USE_EAB=ON",
//           lpm_ram_dp_component.lpm_indata = "REGISTERED",
//           lpm_ram_dp_component.lpm_outdata = "UNREGISTERED",
//           lpm_ram_dp_component.lpm_rdaddress_control = "UNREGISTERED",
//           lpm_ram_dp_component.lpm_width = 32,
//           lpm_ram_dp_component.lpm_widthad = 24,
//           lpm_ram_dp_component.lpm_wraddress_control = "REGISTERED",
//           lpm_ram_dp_component.suppress_memory_conversion_warnings = "ON";
//
//synthesis read_comments_as_HDL off

endmodule



// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ddr_sdram_test_component (
                                  // inputs:
                                   clk,
                                   ddr_a,
                                   ddr_ba,
                                   ddr_cas_n,
                                   ddr_cke,
                                   ddr_cs_n,
                                   ddr_dm,
                                   ddr_ras_n,
                                   ddr_we_n,

                                  // outputs:
                                   ddr_dq,
                                   ddr_dqs
                                )
;

  inout   [ 15: 0] ddr_dq;
  inout   [  1: 0] ddr_dqs;
  input            clk;
  input   [ 12: 0] ddr_a;
  input   [  1: 0] ddr_ba;
  input            ddr_cas_n;
  input            ddr_cke;
  input            ddr_cs_n;
  input   [  1: 0] ddr_dm;
  input            ddr_ras_n;
  input            ddr_we_n;

  wire    [ 23: 0] CODE;
  wire    [ 12: 0] a;
  wire    [  7: 0] addr_col;
  wire    [  1: 0] ba;
  reg     [  2: 0] burstlength;
  reg              burstmode;
  reg              cas2;
  reg              cas25;
  reg              cas3;
  wire             cas_n;
  wire             cke;
  wire    [  2: 0] cmd_code;
  wire             cs_n;
  wire    [  2: 0] current_row;
  wire    [ 15: 0] ddr_dq;
  wire    [  1: 0] ddr_dqs;
  wire    [  1: 0] dm;
  reg     [  3: 0] dm_captured;
  reg     [ 31: 0] dq_captured;
  wire    [ 15: 0] dq_out_0;
  wire    [ 15: 0] dq_temp;
  wire             dq_valid;
  wire    [  1: 0] dqs_out_0;
  wire    [  1: 0] dqs_temp;
  wire             dqs_valid;
  reg              dqs_valid_temp;
  reg     [ 15: 0] first_half_dq;
  reg     [  2: 0] index;
  wire    [ 31: 0] mem_bytes;
  reg     [ 12: 0] open_rows [  7: 0];
  wire             ras_n;
  reg     [ 23: 0] rd_addr_pipe_0;
  reg     [ 23: 0] rd_addr_pipe_1;
  reg     [ 23: 0] rd_addr_pipe_2;
  reg     [ 23: 0] rd_addr_pipe_3;
  reg     [ 23: 0] rd_addr_pipe_4;
  reg     [ 23: 0] rd_addr_pipe_5;
  reg     [ 23: 0] rd_burst_counter;
  reg     [  5: 0] rd_valid_pipe;
  wire    [ 23: 0] read_addr_delayed;
  reg              read_cmd;
  wire    [ 31: 0] read_data;
  wire    [ 15: 0] read_dq;
  wire             read_valid;
  reg              read_valid_r;
  reg              read_valid_r2;
  reg              read_valid_r3;
  reg              read_valid_r4;
  wire    [ 23: 0] rmw_address;
  reg     [ 31: 0] rmw_temp;
  reg     [ 15: 0] second_half_dq;
  wire    [ 23: 0] txt_code;
  wire             we_n;
  wire    [ 23: 0] wr_addr_delayed;
  reg     [ 23: 0] wr_addr_pipe_0;
  reg     [ 23: 0] wr_addr_pipe_1;
  reg     [ 23: 0] wr_addr_pipe_2;
  reg     [ 23: 0] wr_addr_pipe_3;
  reg     [ 23: 0] wr_burst_counter;
  reg              write_cmd;
  wire             write_to_ram;
  reg              write_to_ram_r;
  reg              write_valid;
  reg              write_valid_r;
  reg              write_valid_r2;
  reg              write_valid_r3;
initial
  begin
    $write("\n");
    $write("**********************************************************************\n");
    $write("This testbench includes an SOPC Builder generated Altera memory model:\n");
    $write("'ddr_sdram_test_component.v', to simulate accesses to the DDR SDRAM memory.\n");
    $write(" \n");
    $write("Initial contents are loaded from the file: 'ddr_sdram.dat'.\n");
    $write("**********************************************************************\n");
  end
  //Synchronous write when (CODE == 24'h205752 (write))
  ddr_sdram_test_component_ram_module ddr_sdram_test_component_ram
    (
      .data      (rmw_temp),
      .q         (read_data),
      .rdaddress (rmw_address),
      .rdclken   (1'b1),
      .wraddress (wr_addr_delayed),
      .wrclock   (clk),
      .wren      (write_to_ram_r)
    );

  assign cke = ddr_cke;
  assign cs_n = ddr_cs_n;
  assign ras_n = ddr_ras_n;
  assign cas_n = ddr_cas_n;
  assign we_n = ddr_we_n;
  assign dm = ddr_dm;
  assign ba = ddr_ba;
  assign a = ddr_a;
  assign cmd_code = {ras_n, cas_n, we_n};
  assign CODE = (&cs_n) ? 24'h494e48 : txt_code;
  assign addr_col = a[8 : 1];
  assign current_row = {cs_n,ba};
  // Decode commands into their actions
  always @(posedge clk)
    begin
      // No Activity if the clock is
      if (cke)
        begin
          // This is a read command
          if (cmd_code == 3'b101)
              read_cmd <= 1'b1;
          else 
            read_cmd <= 1'b0;
          // This is a write command
          if (cmd_code == 3'b100)
              write_cmd <= 1'b1;
          else 
            write_cmd <= 1'b0;
          // This is an activate - store the chip/row/bank address in the same order as the DDR controller
          if (cmd_code == 3'b011)
              open_rows[current_row] <= a;
          //Load mode register - set CAS latency, burst mode and length
          if (cmd_code == 3'b000 && ba == 2'b00)
            begin
              burstmode <= a[3];
              burstlength <= a[2 : 0] << 1;
              //Decode CAS Latency from bits a[6..4]
              if (a[6 : 4] == 3'b010)
                begin
                  cas2 <= 1'b1;
                  index <= 3'b001;
                end
              else //CAS Latency = 2.5 
              if (a[6 : 4] == 3'b110)
                begin
                  cas25 <= 1'b1;
                  index <= 3'b001;
                end
              else 
                begin
                  cas3 <= 1'b1;
                  index <= 3'b010;
                end
            end
          rd_valid_pipe[5 : 1] <= rd_valid_pipe[4 : 0];
          rd_addr_pipe_5 <= rd_addr_pipe_4;
          rd_addr_pipe_4 <= rd_addr_pipe_3;
          rd_addr_pipe_3 <= rd_addr_pipe_2;
          rd_addr_pipe_2 <= rd_addr_pipe_1;
          rd_addr_pipe_1 <= rd_addr_pipe_0;
          rd_valid_pipe[0] <= cmd_code == 3'b101;
          wr_addr_pipe_3 <= wr_addr_pipe_2;
          wr_addr_pipe_2 <= wr_addr_pipe_1;
          wr_addr_pipe_1 <= wr_addr_pipe_0;
        end
    end


  // Burst support - make the wr_addr & rd_addr keep counting
  always @(posedge clk)
    begin
      // Reset write address otherwise if the first write is partial it breaks!
      if (cmd_code == 3'b000 && ba == 2'b00)
        begin
          wr_addr_pipe_0 <= 0;
          wr_burst_counter <= 0;
        end
      else if (cmd_code == 3'b100)
        begin
          wr_addr_pipe_0 <= {ba,open_rows[current_row],addr_col};
          wr_burst_counter[23 : 2] <= {ba,open_rows[current_row],addr_col[7 : 2]};
          wr_burst_counter[1 : 0] <= addr_col[1 : 0] + 1;
        end
      else if (write_cmd || write_to_ram)
        begin
          wr_addr_pipe_0 <= wr_burst_counter;
          wr_burst_counter[1 : 0] <= wr_burst_counter[1 : 0] + 1;
        end
      else 
        wr_addr_pipe_0 <= 0;
      // Reset read address otherwise if the first write is partial it breaks!
      if (cmd_code == 3'b000 && ba == 2'b00)
          rd_addr_pipe_0 <= 0;
      else if (cmd_code == 3'b101)
        begin
          rd_addr_pipe_0 <= {ba,open_rows[current_row],addr_col};
          rd_burst_counter[23 : 2] <= {ba,open_rows[current_row],addr_col[7 : 2]};
          rd_burst_counter[1 : 0] <= addr_col[1 : 0] + 1;
        end
      else if (read_cmd || dq_valid || read_valid)
        begin
          rd_addr_pipe_0 <= rd_burst_counter;
          rd_burst_counter[1 : 0] <= rd_burst_counter[1 : 0] + 1;
        end
      else 
        rd_addr_pipe_0 <= 0;
    end


  // read data transition from single to double clock rate
  always @(posedge clk)
    begin
      first_half_dq <= read_data[31 : 16];
      second_half_dq <= read_data[15 : 0];
    end


  assign read_dq = clk  ? second_half_dq : first_half_dq;
  assign dqs_temp = dqs_valid ? {2{clk}} : {2{1'bz}};
  assign dq_temp = dq_valid  ? read_dq : {16{1'bz}};
  assign #2.5 dqs_out_0 = dqs_temp;
  assign #2.5 dq_out_0 = dq_temp;
  assign #2.5 ddr_dqs = dqs_out_0;
  assign #2.5 ddr_dq = dq_out_0;
  //Pipelining registers for burst counting
  always @(posedge clk)
    begin
      write_valid <= write_cmd;
      write_valid_r <= write_valid;
      read_valid_r <= read_valid;
      write_valid_r2 <= write_valid_r;
      write_valid_r3 <= write_valid_r2;
      write_to_ram_r <= write_to_ram;
      read_valid_r2 <= read_valid_r;
      read_valid_r3 <= read_valid_r2;
      read_valid_r4 <= read_valid_r3;
    end


  assign write_to_ram = write_valid || write_valid_r || write_valid_r2 || write_valid_r3;
  assign dq_valid = read_valid_r || read_valid_r2 || read_valid_r3 || read_valid_r4;
  assign dqs_valid = dq_valid || dqs_valid_temp;
  // 
  always @(negedge clk)
    begin
      dqs_valid_temp <= read_valid;
    end


  //capture first half of write data with rising edge of DQS, for simulation use only 1 DQS pin
  always @(posedge ddr_dqs[0])
    begin
      dq_captured[15 : 0] <= ddr_dq[15 : 0];
      dm_captured[1 : 0] <= ddr_dm[1 : 0];
    end


  //capture second half of write data with falling edge of DQS, for simulation use only 1 DQS pin
  always @(negedge ddr_dqs[0])
    begin
      dq_captured[31 : 16] <= ddr_dq[15 : 0];
      dm_captured[3 : 2] <= ddr_dm[1 : 0];
    end


  //Support for incomplete writes, do a read-modify-write with mem_bytes and the write data
  always @(posedge clk)
    begin
      if (write_to_ram)
          rmw_temp[7 : 0] <= dm_captured[0] ? mem_bytes[7 : 0] : dq_captured[7 : 0];
    end


  always @(posedge clk)
    begin
      if (write_to_ram)
          rmw_temp[15 : 8] <= dm_captured[1] ? mem_bytes[15 : 8] : dq_captured[15 : 8];
    end


  always @(posedge clk)
    begin
      if (write_to_ram)
          rmw_temp[23 : 16] <= dm_captured[2] ? mem_bytes[23 : 16] : dq_captured[23 : 16];
    end


  always @(posedge clk)
    begin
      if (write_to_ram)
          rmw_temp[31 : 24] <= dm_captured[3] ? mem_bytes[31 : 24] : dq_captured[31 : 24];
    end


  assign mem_bytes = (rmw_address == wr_addr_delayed && write_to_ram_r) ? rmw_temp : read_data;
  assign rmw_address = (write_to_ram) ? wr_addr_pipe_1 : read_addr_delayed;
  assign wr_addr_delayed = wr_addr_pipe_2;
  //use index to select which pipeline stage drives addr
  assign read_addr_delayed = (index == 0)? rd_addr_pipe_0 :
    (index == 1)? rd_addr_pipe_1 :
    (index == 2)? rd_addr_pipe_2 :
    (index == 3)? rd_addr_pipe_3 :
    (index == 4)? rd_addr_pipe_4 :
    rd_addr_pipe_5;

  //use index to select which pipeline stage drives valid
  assign read_valid = (index == 0)? rd_valid_pipe[0] :
    (index == 1)? rd_valid_pipe[1] :
    (index == 2)? rd_valid_pipe[2] :
    (index == 3)? rd_valid_pipe[3] :
    (index == 4)? rd_valid_pipe[4] :
    rd_valid_pipe[5];


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  assign txt_code = (cmd_code == 3'h0)? 24'h4c4d52 :
    (cmd_code == 3'h1)? 24'h415246 :
    (cmd_code == 3'h2)? 24'h505245 :
    (cmd_code == 3'h3)? 24'h414354 :
    (cmd_code == 3'h4)? 24'h205752 :
    (cmd_code == 3'h5)? 24'h205244 :
    (cmd_code == 3'h6)? 24'h425354 :
    (cmd_code == 3'h7)? 24'h4e4f50 :
    24'h424144;


//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on

endmodule

