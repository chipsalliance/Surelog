
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
 * NAME:        amiq_svaunit_ex_simple_test_head_sequence.sv
 * PROJECT:     svaunit
 * Description: Example of a sequence which starts another sequence
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_SIMPLE_TEST_HEAD_SEQUENCE_SV
`define AMIQ_SVAUNIT_EX_SIMPLE_TEST_HEAD_SEQUENCE_SV

// Example of a sequence which starts another sequence
class amiq_svaunit_ex_simple_test_head_sequence extends svaunit_base_sequence;

   `uvm_object_utils(amiq_svaunit_ex_simple_test_head_sequence)

   // Pointer to sequence used to check scenario
   local amiq_svaunit_ex_simple_test_sequence seq;

   // Reference to virtual interface containing the SVA
   local virtual an_interface an_vif;

   /* Constructor for an amiq_svaunit_ex_simple_test_head_sequence
    * @param name : instance name for amiq_svaunit_ex_simple_test_head_sequence object
    */
   function new(string name = "amiq_svaunit_ex_simple_test_head_sequence");
      super.new(name);

      // Get the reference to an_interface from UVM config db
      if (!uvm_config_db#(virtual an_interface)::get(uvm_root::get(), "*", "VIF", an_vif)) begin
         `uvm_fatal("SVAUNIT_NO_VIF_ERR",
            $sformatf("SVA interface for amiq_svaunit_ex_simple_test_head_sequence is not set!"))
      end
   endfunction

   // Initialize signals
   virtual task pre_body();
      super.pre_body();

      an_vif.enable <=  1'b0;
      an_vif.ready  <=  1'b0;
      an_vif.sel    <=  1'b0;
      an_vif.slverr <=  1'b0;
   endtask

   // Create scenarios for AN_SVA
   virtual task body();
      `uvm_info(get_test_name(), "START RUN PHASE", UVM_LOW)

      vpiw.disable_all_assertions();
      vpiw.enable_assertion("AN_SVA");

      repeat(2) @(posedge an_vif.clk);
      repeat(2) begin
         @(posedge an_vif.clk);
         vpiw.fail_if_sva_not_succeeded("AN_SVA", "The assertion should have succeeded");
      end

      // Enable error scenario
      an_vif.slverr <= 1'b1;
      @(posedge an_vif.clk);

      repeat(2) begin
         @(posedge an_vif.clk);
         vpiw.fail_if_sva_succeeded("AN_SVA", "The assertion should have failed");
      end

      an_vif.slverr <= 1'b0;
      @(posedge  an_vif.clk);
      @(posedge  an_vif.clk);
      vpiw.fail_if_sva_not_succeeded("top.an_if.AN_SVA", "The assertion should have succeeded");
      an_vif.slverr <= 1'b1;
      @(posedge  an_vif.clk);
      an_vif.slverr <= 1'b0;
      @(posedge  an_vif.clk);
      vpiw.fail_if_sva_succeeded("AN_SVA", "The assertion should have failed");
      @(posedge  an_vif.clk);

      `uvm_info(get_test_name(), "END RUN PHASE", UVM_LOW)

      `uvm_do(seq)
   endtask
endclass

`endif
