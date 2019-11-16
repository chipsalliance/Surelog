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


(* sva_checker *)
interface wb_slave_chk_if (
                    clk,
                    reset_n,
	            ACK_O,
                    ADR_I,
                    CYC_I,
                    DAT_I,
                    DAT_O,
                    ERR_O,
                    RTY_O,
                    SEL_I,
                    STB_I,
                    WE_I
                  ) ;
   parameter int severity_level              = 0 ;
   parameter int wb_addr_width               = 8;
   parameter int wb_data_width               = 8;
   parameter int wb_sel_width                = 8;
   parameter     msg                         = "VIOLATION" ;
   parameter int category                    = 0 ;
   parameter int coverage_level_1            = -1 ;
   parameter int coverage_level_2            = -1 ;
   parameter int coverage_level_3            = -1 ;

   localparam assert_name                    = "WB_SLAVE_CHECKER";

   input                           clk  ;
   input                           reset_n  ;
   input                           ACK_O  ;
   input   [(wb_addr_width-1):0]   ADR_I ;
   input                           CYC_I  ;
   input   [(wb_data_width-1):0]   DAT_I  ;
   input   [(wb_data_width-1):0]   DAT_O  ;
   input                           ERR_O  ;
   input                           RTY_O  ;
   input   [(wb_sel_width-1):0]    SEL_I  ;
   input                           STB_I  ;
   input                           WE_I   ;

   `include "sva_std_task.h"

 `ifdef ASSERT_ON
   
   //==========================================================
   // wb_slave_chk_01 :  when reset is applied, the control 
   //    signal ACK_O must be low.
   //==========================================================
   
   property wb_slave_chk_01_p;
      @( posedge clk) 
         disable iff( not_resetting) 
            reset_n |-> ACK_O != 1'b1;
   endproperty
   
   wb_slave_chk_01 : assert property(
      wb_slave_chk_01_p) else
         sva_checker_error( "ERROR : ACK_O is active under reset"); 

   //==========================================================
   // wb_slave_chk_02 :  when reset is applied, the control 
   //    signal ERR_O must be low.
   //==========================================================
   
   property wb_slave_chk_02_p;
      @( posedge clk) 
         disable iff( not_resetting) 
            reset_n |-> ERR_O != 1'b1;
   endproperty
   
   wb_slave_chk_02 : assert property(
      wb_slave_chk_02_p) else
         sva_checker_error( "ERROR : ERR_O is active under reset"); 
   
   //==========================================================
   // wb_slave_chk_03 :  when reset is applied, the control 
   //    signal RTY_O must be low.
   //==========================================================
   
   property wb_slave_chk_03_p;
      @( posedge clk) 
         disable iff( not_resetting) 
            reset_n |-> RTY_O != 1'b1;
   endproperty
   
   wb_slave_chk_03 : assert property(
      wb_slave_chk_03_p) else
         sva_checker_error( "ERROR : RTY_O is active under reset"); 
   
   //==========================================================
   // wb_slave_chk_04 :  when CYC_I is low, the control 
   //    signals ACK_O must be low.
   //==========================================================
   
   property wb_slave_chk_04_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I == 1'b0 |-> ACK_O != 1'b1;
   endproperty
   
   wb_slave_chk_04 : assert property(
      wb_slave_chk_04_p) else
         sva_checker_error( "ERROR : ACK_O active without CYC_I being active");
   
   //==========================================================
   // wb_slave_chk_05 :  when CYC_I is low, the control 
   //    signals ERR_O must be low.
   //==========================================================
   
   property wb_slave_chk_05_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I == 1'b0 |-> ERR_O != 1'b1;
   endproperty
   
   wb_slave_chk_05 : assert property(
      wb_slave_chk_05_p) else
         sva_checker_error( "ERROR : ERR_O active without CYC_I being active");
   
   //==========================================================
   // wb_slave_chk_06 :  when CYC_I is low, the control 
   //    signals RTY_O must be low.
   //==========================================================
   
   property wb_slave_chk_06_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I == 1'b0 |-> RTY_O != 1'b1;
   endproperty
   
   wb_slave_chk_06 : assert property(
      wb_slave_chk_06_p) else
         sva_checker_error( "ERROR : RTY_O active without CYC_I being active");
   
   //==========================================================
   // wb_slave_chk_07 :  ACK_O and ERR_O cannot be asserted 
   //    at the same time.
   //==========================================================
   
   property wb_slave_chk_07_p;
      @( posedge clk) 
         disable iff( resetting) 
            not( ACK_O && ERR_O);
   endproperty
   
   wb_slave_chk_07 : assert property(
      wb_slave_chk_07_p) else
         sva_checker_error( "ERROR : ACK_O and ERR_O asserted together");
   
   //==========================================================
   // wb_slave_chk_08 :  RTY_O and ERR_O cannot be asserted 
   //    at the same time.
   //==========================================================
   
   property wb_slave_chk_08_p;
      @( posedge clk) 
         disable iff( resetting) 
            not( RTY_O && ERR_O);
   endproperty
   
   wb_slave_chk_08 : assert property(
      wb_slave_chk_08_p) else
         sva_checker_error( "ERROR : RTY_O and ERR_O asserted together");
   
   //==========================================================
   // wb_slave_chk_09 :  RTY_O and ACK_O cannot be asserted 
   //    at the same time.
   //==========================================================
   
   property wb_slave_chk_09_p;
      @( posedge clk) 
         disable iff( resetting) 
            not( RTY_O && ACK_O);
   endproperty
   
   wb_slave_chk_09 : assert property(
      wb_slave_chk_09_p) else
         sva_checker_error( "ERROR : RTY_O and ACK_O asserted together");
   
   //==========================================================
   // wb_slave_chk_10 :  Once CYC_I and ACK_O are asserted,
   // then ACK should stay asserted until STB_I get asserted.
   //==========================================================
   
   property wb_slave_chk_10_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I && ACK_O && !STB_I |=>
                ACK_O;
   endproperty
   
   wb_slave_chk_10 : assert property(
      wb_slave_chk_10_p) else
         sva_checker_error( "ERROR : ACK_O deasserted at inappropriate time");
   
   //==========================================================
   // wb_slave_chk_11 :  Once CYC_I and ERR_O are asserted,
   // then ERR should stay asserted until STB_I get asserted.
   //==========================================================
   
   property wb_slave_chk_11_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I && ERR_O && !STB_I |=>
                ERR_O;
   endproperty
   
   wb_slave_chk_11 : assert property(
      wb_slave_chk_11_p) else
         sva_checker_error( "ERROR : ACK_O deasserted at inappropriate time");
   
   //==========================================================
   // wb_slave_chk_12 :  Once CYC_I and RTY_O are asserted,
   // then RTY should stay asserted until STB_I get asserted.
   //==========================================================
   
   property wb_slave_chk_12_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I && RTY_O && !STB_I |=>
                RTY_O;
   endproperty
   
   wb_slave_chk_12 : assert property(
      wb_slave_chk_12_p) else
         sva_checker_error( "ERROR : ACK_O deasserted at inappropriate time");
   
   //==========================================================
   // wb_slave_chk_13 :  Once CYC_I, ACK_O are asserted,
   // and WE_I is LOW then DAT_O should stay stable until STB_I 
   // get asserted.
   //==========================================================
   
   property wb_slave_chk_13_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_I && ACK_O && !STB_I && !WE_I  |=>
                $stable( DAT_O);
   endproperty
   
   wb_slave_chk_13 : assert property(
      wb_slave_chk_13_p) else
         sva_checker_error( "ERROR : DAT_O changed at inappropriate time");
`endif // ASSERT_ON
endinterface : wb_slave_chk_if 

// $Log: slave_chk.sv,v $
// Revision 1.7  2005/09/10 16:35:37  manojt
//  replaced the module with interface
//
// Revision 1.6  2005/09/09 14:39:11  janick
// Added SNPS IP notice
//
// Revision 1.5  2005/09/09 06:40:18  manojt
// corrected the checker for clean Magellan Run
//
// Revision 1.3  2005/06/06 20:48:08  manojt
// integrated with VMM testbench
//
// Revision 1.2  2005/04/15 12:38:46  manojt
// First version of VMM Wishbone checker, that is compliant with the suggested file names and module names. The checker is made specific to follow wishbone module for opencores ethernet core
//
// Revision 1.1  2005/04/15 12:21:32  manojt
// *** empty log message ***
//
