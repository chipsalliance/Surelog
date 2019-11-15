
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
 * MODULE:      amiq_apb_if.sv
 * PROJECT:     svaunit
 * Description: AMBA APB interface
 *******************************************************************************/

`ifndef AMIQ_APB_IF_SV
`define AMIQ_APB_IF_SV

`ifndef AMIQ_APB_MAX_DATA_WIDTH
//maximum data width
`define AMIQ_APB_MAX_DATA_WIDTH 32
`endif

`ifndef AMIQ_APB_MAX_ADDR_WIDTH
//maximum address width
`define AMIQ_APB_MAX_ADDR_WIDTH 32
`endif

//PPROT width
`define AMIQ_APB_PROT_WIDTH 3

`ifndef AMIQ_APB_MAX_STROBE_WIDTH
//maximum strobe width
`define AMIQ_APB_MAX_STROBE_WIDTH 4
`endif

`ifndef AMIQ_APB_MAX_SEL_WIDTH
//maximum sel width
`define AMIQ_APB_MAX_SEL_WIDTH 16
`endif

//AMBA APB interface
interface amiq_apb_if#(ready_low_max_time = 100) (input clk);
   import uvm_pkg::*;
`include "uvm_macros.svh"

   //reset signal
   logic reset_n;

   //Select signal
   logic[`AMIQ_APB_MAX_SEL_WIDTH-1:0] sel;

   //Address bus
   logic[`AMIQ_APB_MAX_ADDR_WIDTH-1:0] addr;

   //Direction signal
   logic write;

   //Write data bus
   logic[`AMIQ_APB_MAX_DATA_WIDTH-1:0] wdata;

   //Protection bus
   logic[`AMIQ_APB_PROT_WIDTH-1:0] prot;

   //Enable signal
   logic enable;

   //Write strobe bus
   logic[`AMIQ_APB_MAX_STROBE_WIDTH:0] strb;

   //Ready signal
   logic ready;

   //Read data bus
   logic[`AMIQ_APB_MAX_DATA_WIDTH-1:0] rdata;

   //Error signal
   logic slverr;

   //Switch which indicates that the agent uses error signal ( 1 - on; 0 - off)
   bit has_error_signal = 1;

   //-------------------------------------------------------------------------------------------
   //--- SWITCHES TO ENABLE CHECKS
   //--- They are initialized with 1 at start of simulation
   //-------------------------------------------------------------------------------------------

   //Switch to enable maximum number of clock cycles during when a signal can be kept low ( 1 - on; 0 - off)
   bit en_ready_low_max_time = 1;

   //Switch to enable reset checks ( 1 - on; 0 - off)
   bit en_rst_checks = 1;

   //Switch to enable X/Z checks ( 1 - on; 0 - off)
   bit en_x_z_checks = 1;

   //Switch to enable protocol checks ( 1 - on; 0 - off)
   bit en_protocol_checks = 1;

   //-------------------------------------------------------------------------------------------
   //--- X/Z CHECKS
   //--- Switch on/off by toggling en_x_z_checks field
   //-------------------------------------------------------------------------------------------

   //Property definition for sel signal valid values
   property amiq_apb_sel_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(sel) == 0;
   endproperty
   //Check that sel signal is not x nor z
   AMIQ_APB_ILLEGAL_SEL_VALUE_ERR: assert property (amiq_apb_sel_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_VALUE_ERR",
         $sformatf("[%0t] Found illegal sel value, %0b. sel should not be x nor z.",
            $time, sel))
   //Cover the amiq_apb_sel_valid_values_p property
   AMIQ_APB_ILLEGAL_SEL_VALUE_CVR: cover property (amiq_apb_sel_valid_values_p);

   //Property definition for addr signal valid values
   property amiq_apb_addr_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(addr) == 0;
   endproperty
   //Check that addr signal is not x nor z
   AMIQ_APB_ILLEGAL_ADDR_VALUE_ERR: assert property (amiq_apb_addr_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ADDR_VALUE_ERR",
         $sformatf("[%0t] Found illegal addr value, %0b. addr should not be x nor z.",
            $time, addr))
   //Cover the amiq_apb_addr_valid_values_p property
   AMIQ_APB_ILLEGAL_ADDR_VALUE_CVR: cover property (amiq_apb_addr_valid_values_p);

   //Property definition for write signal valid values
   property amiq_apb_write_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(write) == 0;
   endproperty
   //Check that write signal is not x nor z
   AMIQ_APB_ILLEGAL_WRITE_VALUE_ERR: assert property (amiq_apb_write_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_WRITE_VALUE_ERR",
         $sformatf("[%0t] Found illegal write value, %0b. write should not be x nor z.",
            $time, write))
   //Cover the amiq_apb_write_valid_values_p property
   AMIQ_APB_ILLEGAL_WRITE_VALUE_CVR: cover property (amiq_apb_write_valid_values_p);

   //Property definition for prot signal valid values
   property amiq_apb_prot_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(prot) == 0;
   endproperty
   //Check that prot signal is not x nor z
   AMIQ_APB_ILLEGAL_PROT_VALUE_ERR: assert property (amiq_apb_prot_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_PROT_VALUE_ERR",
         $sformatf("[%0t] Found illegal prot value, %0b. prot should not be x nor z.",
            $time, prot))
   //Cover the amiq_apb_prot_valid_values_p property
   AMIQ_APB_ILLEGAL_PROT_VALUE_CVR: cover property (amiq_apb_prot_valid_values_p);

   //Property definition for enable signal valid values
   property amiq_apb_enable_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(enable) == 0;
   endproperty
   //Check that enable signal is not x nor z
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_ERR: assert property (amiq_apb_enable_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_VALUE_ERR",
         $sformatf("[%0t] Found illegal enable value, %0b. enable should not be x nor z.",
            $time, enable))
   //Cover the amiq_apb_enable_valid_values_p property
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_CVR: cover property (amiq_apb_enable_valid_values_p);

   //Property definition for strb signal valid values
   property amiq_apb_strb_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(strb) == 0;
   endproperty
   //Check that strb signal is not x nor z
   AMIQ_APB_ILLEGAL_STRB_VALUE_ERR: assert property (amiq_apb_strb_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_STRB_VALUE_ERR",
         $sformatf("[%0t] Found illegal strb value, %0b. strb should not be x nor z.",
            $time, strb))
   //Cover the amiq_apb_strb_valid_values_p property
   AMIQ_APB_ILLEGAL_STRB_VALUE_CVR: cover property (amiq_apb_strb_valid_values_p);

   //Property definition for ready signal valid values
   property amiq_apb_ready_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(ready) == 0;
   endproperty
   //Check that ready signal is not x nor z
   AMIQ_APB_ILLEGAL_READY_VALUE_ERR: assert property (amiq_apb_ready_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_READY_VALUE_ERR",
         $sformatf("[%0t] Found illegal ready value, %0b. ready should not be x nor z.",
            $time, ready))
   //Cover the amiq_apb_ready_valid_values_p property
   AMIQ_APB_ILLEGAL_READY_VALUE_CVR: cover property (amiq_apb_ready_valid_values_p);

   //Property definition for slverr signal valid values
   property amiq_apb_slverr_valid_values_p;
      @(posedge clk) disable iff(!reset_n || !en_x_z_checks)
         $isunknown(slverr) == 0;
   endproperty
   //Check that slverr signal is not x nor z
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_ERR: assert property (amiq_apb_slverr_valid_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SLVERR_VALUE_ERR",
         $sformatf("[%0t] Found illegal slverr value, %0b. slverr should not be x nor z.",
            $time, slverr))
   //Cover the amiq_apb_slverr_valid_values_p property
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_CVR: cover property (amiq_apb_slverr_valid_values_p);


   //-------------------------------------------------------------------------------------------
   //--- POST RESET CHECKS
   //--- Switch on/off by toggling en_rst_checks field
   //-------------------------------------------------------------------------------------------

   //Property definition for sel signal valid value post reset
   property amiq_apb_sel_post_reset_p;
      @(posedge clk) disable iff(!en_rst_checks)
         $rose(reset_n) |-> $past(sel) == 0;
   endproperty
   //Check that after reset sel is LOW
   AMIQ_APB_ILLEGAL_SEL_VALUE_POST_RESET_ERR: assert property (amiq_apb_sel_post_reset_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_VALUE_POST_RESET_ERR",
         $sformatf("[%0t] Found illegal sel value, %0b after reset.",
            $time, sel))
   //Cover the amiq_apb_sel_post_reset_p property
   AMIQ_APB_ILLEGAL_SEL_VALUE_POST_RESET_CVR: cover property (amiq_apb_sel_post_reset_p);

   //Property definition for enable signal valid value post reset
   property amiq_apb_enable_post_reset_p;
      @(posedge clk) disable iff(!en_rst_checks)
         $rose(reset_n) |-> $past(enable) == 0;
   endproperty
   //Check that after reset enable is LOW
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_POST_RESET_ERR: assert property (amiq_apb_enable_post_reset_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_VALUE_POST_RESET_ERR",
         $sformatf("[%0t] Found illegal enable value, %0b after reset.",
            $time, enable))
   //Cover the amiq_apb_enable_post_reset_p property
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_POST_RESET_CVR: cover property (amiq_apb_enable_post_reset_p);

   //Property definition for slverr signal valid value post reset
   property amiq_apb_slverr_post_reset_p;
      @(posedge clk) disable iff(!en_rst_checks)
         $rose(reset_n) |-> $past(slverr) == 0;
   endproperty
   //Check that after reset slverr is LOW
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_POST_RESET_ERR: assert property (amiq_apb_slverr_post_reset_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SLVERR_VALUE_POST_RESET_ERR",
         $sformatf("[%0t] Found illegal slverr value, %0b after reset.",
            $time, slverr))
   //Cover the amiq_apb_slverr_post_reset_p property
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_POST_RESET_CVR: cover property (amiq_apb_slverr_post_reset_p);


   //-------------------------------------------------------------------------------------------
   //--- PROTOCOL CHECKS
   //--- Switch on/off by toggling en_protocol_checks field
   //-------------------------------------------------------------------------------------------
   //{{{ Specific checks for sel signal
   //Property definition for sel signal valid value when enable is asserted
   property amiq_apb_sel_validity_during_transfer_phases_p;
      @(posedge enable) disable iff(!reset_n || !en_protocol_checks) (|sel);
   endproperty
   //Check that sel is HIGH when enable is asserted
   AMIQ_APB_ILLEGAL_SEL_TRANSITION_TR_PHASES_ERR: assert property (amiq_apb_sel_validity_during_transfer_phases_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_TRANSITION_TR_PHASES_ERR",
         $sformatf("[%0t] sel must be stable during setup-access transitions.",
            $time))
   //Cover the amiq_apb_sel_validity_during_transfer_phases_p property
   AMIQ_APB_ILLEGAL_SEL_TRANSITION_TR_PHASES_CVR: cover property (amiq_apb_sel_validity_during_transfer_phases_p);

   //Property definition for sel signal valid value
   property amiq_apb_sel_legal_values_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks) $onehot0(sel);
   endproperty
   //Check that sel has legal values
   AMIQ_APB_ILLEGAL_SEL_LEGAL_VALUES_ERR: assert property (amiq_apb_sel_legal_values_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_LEGAL_VALUES_ERR",
         $sformatf("[%0t] sel has not legal value.",
            $time))
   //Cover the amiq_apb_sel_legal_values_p property
   AMIQ_APB_ILLEGAL_SEL_LEGAL_VALUES_CVR: cover property (amiq_apb_sel_legal_values_p);

   //Property definition for sel signal stability during a transfer
   property amiq_apb_sel_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         enable |-> $stable(sel);
   endproperty
   //Check that sel is stable (HIGH) during a transfer
   AMIQ_APB_ILLEGAL_SEL_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_sel_stability_during_transfer_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] sel must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_sel_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_SEL_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_sel_stability_during_transfer_p);

   //Property definition for the minimum number of clock cycles during which sel signal must be asserted in a transfer
   property amiq_apb_sel_minimum_time_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         $rose(|sel) |-> not(##1 $fell(|sel));
   endproperty
   //Check that sel is asserted at least two clock cycles during a transfer
   AMIQ_APB_ILLEGAL_SEL_MINIMUM_TIME_ERR: assert property(amiq_apb_sel_minimum_time_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SEL_MINIMUM_TIME_ERR",
         $sformatf("[%0t] sel must be asserted at least two clock cycles.",
            $time))
   //Cover the amiq_apb_sel_minimum_time_p property
   AMIQ_APB_ILLEGAL_SEL_MINIMUM_TIME_CVR: cover property(amiq_apb_sel_minimum_time_p);

   //Property definition for enable fall event towards sel fall event
   property amiq_apb_enable_fall_towards_sel_fall_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         $fell(|sel) |-> (($past(enable) == 1) && (enable === 0));
   endproperty
   //Check that when sel is falling, enable is also falling
   AMIQ_APB_ILLEGAL_ENABLE_FALL_TOWARDS_SEL_FALL_ERR: assert property(amiq_apb_enable_fall_towards_sel_fall_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_FALL_TOWARDS_SEL_FALL_ERR",
         $sformatf("[%0t] sel and enable must fell in the same time.",
            $time))
   //Cover the amiq_apb_enable_fall_towards_sel_fall_p property
   AMIQ_APB_ILLEGAL_ENABLE_FALL_TOWARDS_SEL_FALL_CVR: cover property(amiq_apb_enable_fall_towards_sel_fall_p);
   //}}}

   //{{{ Specific checks for addr signal
   //Property definition for addr stability during a transfer
   property amiq_apb_addr_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable |-> ($stable(addr) and ##[1: $] $fell(enable));
   endproperty
   //Check that addr is stable during a transfer
   AMIQ_APB_ILLEGAL_ADDR_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_addr_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_ADDR_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] addr must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_addr_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_ADDR_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_addr_stability_during_transfer_p);
   //}}}

   //{{{ Specific checks for write signal
   //Property definition for write stability during a transfer
   property amiq_apb_write_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable |-> ($stable(write) and ##[1: $] $fell(enable));
   endproperty
   //Check that write is stable during a transfer
   AMIQ_APB_ILLEGAL_WRITE_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_write_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_WRITE_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] write must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_write_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_WRITE_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_write_stability_during_transfer_p);
   //}}}

   //{{{ Specific checks for wdata signal
   //Property definition for wdata stability during a transfer
   property amiq_apb_wdata_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable and write |-> ($stable(wdata) and ##[1: $] $fell(enable));
   endproperty
   //Check that wdata is stable during a write transfer
   AMIQ_APB_ILLEGAL_WDATA_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_wdata_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_WDATA_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] wdata must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_wdata_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_WDATA_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_wdata_stability_during_transfer_p);
   //}}}

   //{{{ Specific checks for prot signal
   //Property definition for prot stability during a transfer
   property amiq_apb_prot_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable |-> ($stable(prot) and ##[1: $] $fell(enable));
   endproperty
   //Check that prot is stable during a transfer
   AMIQ_APB_ILLEGAL_PROT_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_prot_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_PROT_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] prot must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_prot_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_PROT_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_prot_stability_during_transfer_p);
   //}}}

   //{{{ Specific checks for enable signal
   //Property definition for enable assertion towards a transfer
   property amiq_apb_enable_assertion_time_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and !enable |=> (enable);
   endproperty
   //Check that at the beginning of a transfer, enable is asserted at the next clock cycle
   AMIQ_APB_ILLEGAL_ENABLE_ASSERTION_TIME_ERR: assert property (amiq_apb_enable_assertion_time_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_ASSERTION_TIME_ERR",
         $sformatf("[%0t] enable must be asserted one clock cycle after a transfer starts.",
            $time))
   //Cover the amiq_apb_enable_assertion_time_p property
   AMIQ_APB_ILLEGAL_ENABLE_ASSERTION_TIME_CVR: cover property (amiq_apb_enable_assertion_time_p);

   //Property definition for enable stability during ready changes
   property amiq_apb_enable_stability_during_ready_changes_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         !ready and enable |=> enable;
   endproperty
   //Check that enable is stable during ready changes (when ready is asserted during a transfer, after a LOW period)
   AMIQ_APB_ILLEGAL_ENABLE_TRANSITION_DURING_READY_CHANGES_ERR: assert property (
         amiq_apb_enable_stability_during_ready_changes_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_TRANSITION_DURING_READY_CHANGES_ERR",
         $sformatf("[%0t] enable must be stable during ready changes.",
            $time))
   //Cover the amiq_apb_enable_stability_during_ready_changes_p property
   AMIQ_APB_ILLEGAL_ENABLE_TRANSITION_DURING_READY_CHANGES_CVR: cover property (
      amiq_apb_enable_stability_during_ready_changes_p);

   //Property definition for enable valid value between transfers
   property amiq_apb_enable_value_between_transfers_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         !(|sel) |-> !enable;
   endproperty
   //Check that between two transfers enable is kept LOW
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_BETWEEN_TRANSFERS_ERR: assert property(amiq_apb_enable_value_between_transfers_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_VALUE_BETWEEN_TRANSFERS_ERR",
         $sformatf("[%0t] enable must be LOW between two transfers.",
            $time))
   //Cover the amiq_apb_enable_value_between_transfers_p property
   AMIQ_APB_ILLEGAL_ENABLE_VALUE_BETWEEN_TRANSFERS_CVR: cover property(amiq_apb_enable_value_between_transfers_p);

   //Property definition for enable de-assertion time during access phase
   property amiq_apb_enable_deassertion_time_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and ready and enable |=> !enable;
   endproperty
   //Check that enable is de-asserted one clock cycle after the assertion of ready during access phase
   AMIQ_APB_ILLEGAL_ENABLE_DEASSERTION_TIME_ERR: assert property(amiq_apb_enable_deassertion_time_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_ENABLE_DEASSERTION_TIME_ERR",
         $sformatf("[%0t] enable must be de-asserted one clock cycle after the assertion of ready during access phase.",
            $time))
   //Cover the amiq_apb_enable_deassertion_time_p property
   AMIQ_APB_ILLEGAL_ENABLE_DEASSERTION_TIME_CVR: cover property(amiq_apb_enable_deassertion_time_p);
   //}}}

   //{{{ Specific checks for strb signal
   //Property definition for strb stability during a transfer
   property amiq_apb_strb_stability_during_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable |-> ($stable(strb) and ##[1: $] $fell(enable));
   endproperty
   //Check that strb is stable during a transfer
   AMIQ_APB_ILLEGAL_STRB_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_strb_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_STRB_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] strb must be stable during a transfer.",
            $time))
   //Cover the amiq_apb_strb_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_STRB_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_strb_stability_during_transfer_p);

   //Property definition for valid strb value during a read transfer
   property amiq_apb_strb_value_read_transfer_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks)
         (|sel) and enable and !write |-> ($sampled(strb) === 0);
   endproperty
   //Check that strb is 0 during read transfer
   AMIQ_APB_ILLEGAL_STRB_VALUE_READ_TRANSFER_ERR: assert property (amiq_apb_strb_value_read_transfer_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_STRB_VALUE_READ_TRANSFER_ERR",
         $sformatf("[%0t] strb must be 0 during read transfer.",
            $time))
   //Cover the amiq_apb_strb_value_read_transfer_p property
   AMIQ_APB_ILLEGAL_STRB_VALUE_READ_TRANSFER_CVR: cover property (amiq_apb_strb_value_read_transfer_p);
   //}}}

   //{{{ Specific checks for ready signal
   //Property definition for the maximum number of clock cycles during which ready signal must be kept LOW
   property amiq_apb_ready_low_maximum_time_p;
      @(posedge clk) disable iff(!reset_n || !en_ready_low_max_time || !en_protocol_checks)
         (|sel) and $rose(enable) and !ready |-> ##[1: ready_low_max_time] ready;
   endproperty
   //Check that ready is not kept LOW more than a maximum number of clock cycles
   AMIQ_APB_ILLEGAL_READY_MAXIMUM_LOW_TIME_ERR: assert property (amiq_apb_ready_low_maximum_time_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_READY_MAXIMUM_LOW_TIME_ERR",
         $sformatf("[%0t] ready must be kept LOW at most maximum %d clock cycles.",
            $time, ready_low_max_time))
   //Cover the amiq_apb_ready_low_maximum_time_p property
   AMIQ_APB_ILLEGAL_READY_MAXIMUM_LOW_TIME_CVR: cover property (amiq_apb_ready_low_maximum_time_p);
   //}}}

   //{{{ Specific checks for rdata signal
   //Property definition for rdata stability during a transfer
   property amiq_apb_rdata_stability_during_transfer_p;
      @(clk) disable iff(!reset_n || !en_protocol_checks)
         (!write) and (|sel) and enable and ready and ((has_error_signal and !slverr) or !has_error_signal) and $changed
         (rdata) |-> $rose(clk);
   endproperty
   //Check that rdata is stable during the last clock cycle
   AMIQ_APB_ILLEGAL_RDATA_TRANSITION_DURING_TRANSFER_ERR: assert property (amiq_apb_rdata_stability_during_transfer_p)
   else
      `uvm_error("AMIQ_APB_ILLEGAL_RDATA_TRANSITION_DURING_TRANSFER_ERR",
         $sformatf("[%0t] rdata must be stable during the last clock cycle.",
            $time))
   //Cover the amiq_apb_rdata_stability_during_transfer_p property
   AMIQ_APB_ILLEGAL_RDATA_TRANSITION_DURING_TRANSFER_CVR: cover property (amiq_apb_rdata_stability_during_transfer_p);
   //}}}

   //{{{ Specific checks for slverr signal
   //Property definition for valid slverr value when one of sel, enable, ready signal is de-asserted
   property amiq_apb_slverr_value_condition_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks || !has_error_signal)
         !(|sel) or !enable or !ready |-> !slverr;
   endproperty
   //Check that slverr is LOW when one of sel, enable or ready is LOW
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_CONDITION_ERR: assert property (amiq_apb_slverr_value_condition_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SLVERR_VALUE_CONDITION_ERR",
         $sformatf("[%0t] slverr must be LOW when one of sel, enable or ready is LOW.",
            $time))
   //Cover the amiq_apb_slverr_value_condition_p property
   AMIQ_APB_ILLEGAL_SLVERR_VALUE_CONDITION_CVR: cover property (amiq_apb_slverr_value_condition_p);

   //Property definition for the time span between the assertion of slverr signal and the de-assertion of slverr signal
   property amiq_apb_slverr_assertion_time_p;
      @(posedge clk) disable iff(!reset_n || !en_protocol_checks || !has_error_signal)
         $past(slverr) == 0 and $rose(slverr) |=> $fell(slverr);
   endproperty
   //Check that slverr is asserted one clock cycle
   AMIQ_APB_ILLEGAL_SLVERR_ASSERTION_TIME_ERR: assert property(amiq_apb_slverr_assertion_time_p) else
      `uvm_error("AMIQ_APB_ILLEGAL_SLVERR_ASSERTION_TIME_ERR",
         $sformatf("[%0t] slverr must be HIGH only one clock cycle.",
            $time))
   //Cover the amiq_apb_slverr_assertion_time_p property
   AMIQ_APB_ILLEGAL_SLVERR_ASSERTION_TIME_CVR: cover property(amiq_apb_slverr_assertion_time_p);
//}}}
endinterface
`endif
