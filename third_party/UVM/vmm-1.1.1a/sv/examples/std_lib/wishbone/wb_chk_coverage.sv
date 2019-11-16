// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 


interface wb_chk_coverage_if( not_resetting,
             wb_clk, wb_ack, wb_cyc, wb_err, 
             wb_lock, wb_rty, wb_stb, wb_we); 

     input wire not_resetting;
     input wire wb_clk; 
     input wire wb_ack; 
     input wire wb_cyc; 
     input wire wb_err; 
     input wire wb_lock; 
     input wire wb_rty; 
     input wire wb_stb; 
     input wb_we; 

     parameter int max_burst_blocks = 1024; // 1k 
     parameter int slave_latency = 16; //16 clk cycles
     parameter int master_latency = 16; //16 clk cycles
     parameter int coverage_level_1 = -1;
     parameter int coverage_level_2 = 0;
     parameter int coverage_level_3 = 0;

     wire valid_cycle = wb_cyc && wb_stb;
     wire valid_response = wb_ack && wb_stb;

     generate

        if( ( coverage_level_1&1) != 0) begin : cov_level_1_0
          cover_single_reads : cover property(
            @ ( posedge wb_clk) 
               ( ( not_resetting && wb_cyc && !wb_we ) throughout( 
                  $rose ( wb_cyc) ##1 (valid_response)[=1])) ##1 !wb_cyc);
        end
   
        if( ( coverage_level_1&2) != 0) begin : cov_level_1_1
          cover_single_writes : cover property(
            @ ( posedge wb_clk) 
               ( ( not_resetting && wb_cyc && wb_we ) throughout( 
                  $rose ( wb_cyc) ##1 ( valid_response)[=1])) ##1 !wb_cyc);
        end
      
        if( ( coverage_level_1&4) != 0) begin : cov_level_1_2
          cover_block_reads : cover property(
            @ ( posedge wb_clk) 
               ( ( not_resetting && wb_cyc && !wb_we ) throughout( 
                  $rose ( wb_cyc) ##1 valid_response[=2:$])) ##1 !wb_cyc);
        end
   
        if( ( coverage_level_1&8) != 0) begin : cov_level_1_3
          cover_block_writes : cover property(
            @ ( posedge wb_clk) 
               ( ( not_resetting && wb_cyc && wb_we ) throughout( 
                  $rose ( wb_cyc) ##1 valid_response[=2:$])) ##1 !wb_cyc);
        end
   
        if( ( coverage_level_1&16) != 0) begin : cov_level_1_4
          cover_rmw_cycles : cover property(
            @ ( posedge wb_clk) 
               ( ( not_resetting && wb_cyc) throughout( 
                  $rose ( wb_cyc) ##0 ( ( valid_response && !wb_we) [->1]) ##1 
                     ( ( valid_response)&&wb_we[=1]))) ##1 !wb_cyc);
        end
   
        if( ( coverage_level_1&32) != 0) begin : cov_level_1_5
          cover_abnormal_terminations : cover property(
            @ ( posedge wb_clk) 
               ( not_resetting && valid_cycle && wb_err));
        end
   
        if( ( coverage_level_1&64) != 0) begin : cov_level_1_6
          cover_normal_terminations : cover property(
            @ ( posedge wb_clk) 
               ( not_resetting && valid_cycle && wb_ack));
        end

        if( ( coverage_level_1&128) != 0) begin : cov_level_1_7
          cover_nb_of_retry : cover property(
            @ ( posedge wb_clk) 
               ( not_resetting && valid_cycle && wb_rty));
        end
   
      /*  if( coverage_level_2 > 0) begin : cov_level_2
   
           clocking wb_cg_clk @ ( posedge wb_clk)
              input not_resetting 
           endclocking
   
           covergroup wb_range_cov ( bit not_resetting , event clk,
                           int min_value, int max_value, int data,
                           string msg) @( clk);
              coverpoint data iff( not_resetting) {
                 bins good[] : {[min_value : max_value]};
                 bins bad[]  : default;
              } 
              option.per_instance = 1;
              option.comment      = msg;
           endgroup
   
           function int f_get_block_size( int block_size);
              f_get_block_size = block_size;
           endfunction
              
           sequence detect_block_size( sig);
             int cnt;
             @ ( posedge wb_clk) 
               not_resetting throughout( 
                 ( ( wb_cyc && sig ) throughout( 
                   $rose ( wb_cyc), cnt = 0 ##1 ( valid_cycle[->1], cnt=cnt+1)[*1:$]))
                      ##1 (!wb_cyc)[->], f_get_block_size( cnt));
           endsequence
   
           sequence detect_slave_resp_delay( sig);
             int cnt;
             @ ( posedge wb_clk) 
               ( not_resetting  && wb_cyc) throughout( 
                  ( $rose ( wb_stb) || ( wb_ack && wb_stb)), cnt = 1 ##1 
                     (  ( wb_stb) throughout( ( (!sig),cnt=cnt+1)*[0:$] ##1
                                         sig, f_get_block_size( cnt)))); 
                    
           endsequence 
           sequence detect_master_resp_delay;
             int cnt;
             @ ( posedge wb_clk) 
               ( not_resetting  && wb_cyc) throughout(
                  $rose ( wb_cyc), cnt = 1 ##1
                     ( (!wb_stb),cnt=cnt+1)*[0:$] ##1
                         wb_stb, f_get_block_size( cnt)); 
                    
           endsequence 
   
           if( ( coverage_level_2&1) != 0) begin : 0
              wb_range_cov cover_blocks_transferred_during_read = new(
                               wb_cg_clk.not_resetting,
                               detect_block_size( !wb_we).ended,
                               1,
                               max_burst_blocks,
                               f_get_block_size,
                               "No of blocks transferred during read");
           end
   
           if( ( coverage_level_2&2) != 0) begin : 1
              wb_range_cov cover_blocks_transferred_during_read = new(
                               wb_cg_clk.not_resetting,
                               detect_block_size( wb_we).ended,
                               1,
                               max_burst_blocks,
                               f_get_block_size,
                               "No of blocks transferred during write");
           end
   
           if( ( coverage_level_2&4) != 0) begin : 2
              wb_range_cov cover_ack_delay = new(
                               wb_cg_clk.not_resetting,
                               detect_slave_resp_delay( wb_ack).ended,
                               1,
                               slave_latency,
                               f_get_block_size,
                               "Observed delay between STB and ACK");
           end
   
           if( ( coverage_level_2&8) != 0) begin : 3
              wb_range_cov cover_ack_delay = new(
                               wb_cg_clk.not_resetting,
                               detect_slave_resp_delay( wb_err).ended,
                               1,
                               slave_latency,
                               f_get_block_size,
                               "Observed delay between STB and ERR");
           end
   
           if( ( coverage_level_2&16) != 0) begin : 4
              wb_range_cov cover_rty_delay = new(
                               wb_cg_clk.not_resetting,
                               detect_slave_resp_delay( wb_rty).ended,
                               1,
                               slave_latency,
                               f_get_block_size,
                               "Observed delay between STB and RTY");
           end
           if( ( coverage_level_2&32) != 0) begin : 5
              wb_range_cov cover_rty_delay = new(
                               wb_cg_clk.not_resetting,
                               detect_master_resp_delay.ended,
                               1,
                               master_latency,
                               f_get_block_size,
                               "Observed delay between CYC and STB");
           end
           if( ( coverage_level_2&64) != 0) begin : 6
              int cyc_cnt;
              always @ ( posedge clk) begin 
                 if( $fell( wb_cyc)) begin
                    cyc_cnt <= 1;
                 else
                    cyc_cnt <= cyc_cnt+1;
              end
   
              wb_range_cov cover_rty_delay = new(
                               wb_cg_clk.not_resetting,
                               $rose( wb_cyc),
                               1,
                               32'hffffffff,
                               f_get_block_size,
                               "Observed delay between negedge CYC_O and posedge CYC_O");
           end
        end  */
   
        if( ( coverage_level_3&1) != 0) begin : cov_level_3_0
          cover_read_block_transfer_exactly_max_blocks : cover property(
            @ ( posedge wb_clk) 
               not_resetting throughout( 
                 ( wb_cyc && !wb_we ) throughout( 
                   $rose ( wb_cyc) ##1
                     valid_cycle[=max_burst_blocks])));
        end
   
        if( ( coverage_level_3&2) != 0) begin : cov_level_3_1
          cover_read_block_transfer_exactly_max_blocks : cover property(
            @ ( posedge wb_clk) 
               ( not_resetting && wb_cyc && wb_we ) throughout( 
                   $rose ( wb_cyc) ##1
                     valid_cycle[=max_burst_blocks]));
        end
   
        if( ( coverage_level_3&4) != 0) begin : cov_level_3_2
          cover_slave_response_exactly_at_slave_resp_delay : cover property(
             @ ( posedge wb_clk) 
               ( not_resetting  && wb_cyc) throughout( 
                  ( $rose ( wb_stb) || ( wb_ack && wb_stb)) ##1
                     (!( wb_ack || wb_rty || wb_err))[*(slave_latency-1)] ##1
                        ( wb_ack || wb_rty || wb_err)));
        end
        if( ( coverage_level_3&8) != 0) begin : cov_level_3_3
          cover_master_response_exactly_at_master_resp_delay : cover property(
             @ ( posedge wb_clk) 
               ( not_resetting  && wb_cyc) throughout( 
                  ( $rose( wb_cyc) ##0 ( !wb_stb)[*master_latency] ##1
                       wb_stb)));


        end
     endgenerate
   endinterface
