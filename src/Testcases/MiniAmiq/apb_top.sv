
/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        apb_top.sv
 * PROJECT:     svaunit
 * Description: APB top for SVAUNIT tests
 *******************************************************************************/

`ifndef APB_TOP_SV
`define APB_TOP_SV

`include "amiq_svaunit_ex_simple_pkg.sv"
`timescale 1ns/1ps

// APB top for SVAUNIT tests
module apb_top;
   // Enable SVAUNIT
   `SVAUNIT_UTILS

   // Import package for APB unit tests
   import amiq_svaunit_ex_apb_test_pkg::*;

   // APB clock
   reg clock;

   generate
      genvar maxim_low_time;

      for(maxim_low_time = 10; maxim_low_time < 11; maxim_low_time++) begin
         // APB interface
         amiq_apb_if #(.ready_low_max_time(maxim_low_time)) apb_if(.clk(clock));

         initial begin
            // Register a reference to APB virtual interface to config_db
            uvm_config_db#(virtual amiq_apb_if#(.ready_low_max_time(maxim_low_time)))::set(uvm_root::get(), "*",
               $sformatf("apb_vif%0d", maxim_low_time), apb_if);

            // Interface initialization
            apb_if.sel    <=    '0;
            apb_if.addr   <= 32'b0;
            apb_if.write  <=  1'b0;
            apb_if.wdata  <= 32'b0;
            apb_if.prot   <=  3'b0;
            apb_if.enable <=  1'b0;
            apb_if.strb   <=  4'b0;

            apb_if.ready  <=  1'b0;
            apb_if.rdata  <= 32'b0;
            apb_if.slverr <=  1'b0;
         end
      end
   endgenerate

   initial begin
      // Start test specified with UVM_TESTNAME
      run_test();
   end

   // Clock generation
   initial begin
      clock = 0;
      forever begin
         #5ns;
         clock = ~clock;
      end
   end

endmodule

`endif
