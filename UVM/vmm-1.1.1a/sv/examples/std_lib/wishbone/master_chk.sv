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


// Example 3-56 Separate Interfaces for Separate Signal Directions
(* sva_checker *)
interface wb_master_chk_if (
                    clk,
                    reset_n,
	            ACK_I,
                    ADR_O,
                    CYC_O,
                    DAT_I,
                    DAT_O,
                    ERR_I,
                    RTY_I,
                    SEL_O,
                    STB_O,
                    WE_O,
                    TAG_O
                  ) ;

   parameter int severity_level              = 0 ;
   parameter int wb_addr_width               = 8 ;
   parameter int wb_data_width               = 8 ;
   parameter int wb_sel_width                = 8 ;
   parameter int wb_tag_width                = 8 ;
   parameter     msg                         = "VIOLATION" ;
   parameter int category                    = 0 ;
   parameter int coverage_level_1            = -1 ;
   parameter int coverage_level_2            = -1 ;
   parameter int coverage_level_3            = -1 ;

   localparam assert_name                    = "WB_MASTER_CHECKER";

   input                           clk  ;
   input                           reset_n  ;
   input                           ACK_I  ;
   input   [(wb_addr_width-1):0]   ADR_O ;
   input                           CYC_O  ;
   input   [(wb_data_width-1):0]   DAT_I  ;
   input   [(wb_data_width-1):0]   DAT_O  ;
   input                           ERR_I  ;
   input                           RTY_I  ;
   input   [(wb_sel_width-1):0]    SEL_O  ;
   input                           STB_O  ;
   input                           WE_O   ;
   input   [(wb_tag_width-1):0]    TAG_O  ;

   wire    [2:0]                   CTI_O  ;
   assign  CTI_O = TAG_O[(wb_tag_width-1):(wb_tag_width-3)];

   `include "sva_std_task.h"

`ifdef ASSERT_ON
  
   //==========================================================
   // wb_master_chk_01 :  when reset is applied, the control 
   //    signal CYC_O must be low.
   //==========================================================
   
   property wb_master_chk_01_p;
      @( posedge clk) 
         disable iff( not_resetting) 
            reset_n |-> CYC_O != 1'b1;
   endproperty
   
   wb_master_chk_01 : assert property(
      wb_master_chk_01_p) else
         sva_checker_error( "ERROR : CYC_O is active under reset"); 
   
   //==========================================================
   // wb_master_chk_02 :  when reset is applied, the control 
   //    signal STB_O must be low.
   //==========================================================
   
   property wb_master_chk_02_p;
      @( posedge clk) 
         disable iff( not_resetting) 
            reset_n |-> STB_O != 1'b1;
   endproperty
   
   wb_master_chk_02 : assert property(
      wb_master_chk_02_p) else
         sva_checker_error( "ERROR : STB_O is active under reset"); 
   
   //==========================================================
   // wb_master_chk_03 :  when CYC_O is low, the control 
   //    signals STB_O must be low.
   //==========================================================
   
   property wb_master_chk_03_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O == 1'b0 |-> STB_O != 1'b1;
   endproperty
   
   wb_master_chk_03 : assert property(
      wb_master_chk_03_p) else
         sva_checker_error( "ERROR : STB_O active without CYC_O being active");
   
   //==========================================================
   // wb_master_chk_04 :  Once CYC_O and STB_O are asserted, CYC_O 
   //    should stay asserted until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_04_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> CYC_O;
   endproperty
   
   wb_master_chk_04 : assert property(
      wb_master_chk_04_p) else
         sva_checker_error( "ERROR : CYC_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_05 :  Once CYC_O and STB_O are asserted, CYC_O 
   //    should stay asserted until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_05_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> CYC_O;
   endproperty
   
   wb_master_chk_05 : assert property(
      wb_master_chk_05_p) else
         sva_checker_error( "ERROR : CYC_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_06 :  Once CYC_O and STB_O are asserted, STB_O 
   //    should stay asserted until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_06_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> STB_O;
   endproperty
   wb_master_chk_06 : assert property(
      wb_master_chk_06_p) else
         sva_checker_error( "ERROR : STB_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_07 :  Once CYC_O and STB_O are asserted, TAG_O 
   //    should stay stable until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_07_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> $stable( TAG_O);
   endproperty
   wb_master_chk_07 : assert property(
      wb_master_chk_07_p) else
         sva_checker_error( "ERROR : TAG_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_08 :  Once CYC_O and STB_O are asserted, ADR_O 
   //    should stay stable until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_08_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> $stable( ADR_O);
   endproperty
   wb_master_chk_08 : assert property(
      wb_master_chk_08_p) else
         sva_checker_error( "ERROR : ADR_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_09 :  Once CYC_O and STB_O are asserted, SEL_O 
   //    should stay stable until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_09_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> $stable( SEL_O);
   endproperty
   wb_master_chk_09 : assert property(
      wb_master_chk_09_p) else
         sva_checker_error( "ERROR : SEL_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_10 :  Once CYC_O and STB_O are asserted, WE_O 
   //    should stay stable until a response from the slave is
   //    recieved.
   //==========================================================
   
   property wb_master_chk_10_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && 
                !( ACK_I || RTY_I || ERR_I) |=> $stable( WE_O);
   endproperty
   wb_master_chk_10 : assert property(
      wb_master_chk_10_p) else
         sva_checker_error( "ERROR : WE_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_11 :  Once CYC_O, STB_O iand WE_O are asserted,
   // DAT_O  should stay stable until a response from the slave is
   // recieved.
   //==========================================================
   
   property wb_master_chk_11_p;
      @( posedge clk)
         disable iff( resetting)
            CYC_O && STB_O &&
                !( ACK_I || RTY_I || ERR_I) |=> $stable( DAT_O);
   endproperty
   wb_master_chk_11 : assert property(
      wb_master_chk_11_p) else
         sva_checker_error( "ERROR : DAT_O changed at inappropriate time");
   
   //==========================================================
   // wb_master_chk_12 :  During wishbone classic cycle, i.e. when
   // CTI_O is driven with a value 3'b000. The value should remain
   // be stable during CYC_O is asserted.
   //==========================================================
   
   property wb_master_chk_12_p;
      @( posedge clk) 
         disable iff( resetting) 
            ( CYC_O && CTI_O == 3'b000) ##1
                CYC_O |-> $stable( CTI_O);
   endproperty
   wb_master_chk_12 : assert property(
      wb_master_chk_12_p) else
         sva_checker_error( "ERROR : Wrong CTI_O change during WB classic cycles");
   
   //==========================================================
   // wb_master_chk_13 :  During wishbone burst cycles, once
   // end of burst is sigalled by CTI_O = 3'b111,  then this
   // value should be continued to be stable until CYC_O
   // is de-asserted.
   //==========================================================
   
   property wb_master_chk_13_p;
      @( posedge clk) 
         disable iff( resetting) 
            (CYC_O && CTI_O == 3'b111) 
               ##1 CYC_O |-> ( CTI_O == 3'b111);
   endproperty
   
   wb_master_chk_13 : assert property(
      wb_master_chk_13_p) else
         sva_checker_error( "ERROR : End of burst must end the burst");
   
   //==========================================================
   // wb_master_chk_14 :  A master signalling a constant address
   // burst must initiate another cycle.
   //==========================================================
   
   property wb_master_chk_14_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && ( CTI_O == 3'b001) && ACK_I |=>
                CYC_O throughout( STB_O[->1]);
   endproperty
   
   wb_master_chk_14 : assert property(
      wb_master_chk_14_p) else
         sva_checker_error( "ERROR : Constant address burst must initiate another cycle");
   
   //==========================================================
   // wb_master_chk_15 :  During a constant address burst, 
   // WE_O, SEL_O, and ADR_O must be kept constant.
   //==========================================================
   
   property wb_master_chk_15_p;
      logic [(wb_addr_width+wb_sel_width) : 0] const_data;
      @( posedge clk) 
         disable iff( resetting) 
             ( $rose( CYC_O && STB_O && ( CTI_O == 3'b001)),
               const_data = {WE_O, SEL_O, ADR_O})  |=>
                  ( const_data == {WE_O, SEL_O, ADR_O}) throughout
                       ( (!CYC_O) [->1]);
                      
   endproperty
   
   wb_master_chk_15 : assert property(
      wb_master_chk_15_p) else
         sva_checker_error( "ERROR : Constant address burst must not change ADR_O, SEL_O, and WE_O");
   
   //==========================================================
   // wb_master_chk_16 :  A master signalling an incrementing 
   // burst must initiate another cycle.
   //==========================================================
   
   property wb_master_chk_16_p;
      @( posedge clk) 
         disable iff( resetting) 
            CYC_O && STB_O && ( CTI_O == 3'b010) && ACK_I |=>
                CYC_O throughout( STB_O[->1]);
   endproperty
   
   wb_master_chk_16 : assert property(
      wb_master_chk_16_p) else
         sva_checker_error( "ERROR : Incrementing burst must initiate another cycle");
   
   //==========================================================
   // wb_master_chk_17 :  During an incrementing burst ADR_O must
   // be incremented.
   //==========================================================
   
   property wb_master_chk_17_p;
      @( posedge clk) 
         disable iff( resetting) 
             CYC_O throughout 
                ( ( CTI_O == 3'b010) ##1 
                    ( ( ( CTI_O == 3'b010) || ( CTI_O == 3'b111)) &&
                       !$stable( ADR_O))) |-> ( ADR_O >= $past(ADR_O)) ?
                              ( ( ADR_O - $past( ADR_O)) == ( wb_data_width/8)) :
                                    ( ( $past( ADR_O) - ADR_O) == ( wb_data_width/8));
   endproperty
   
   wb_master_chk_17 : assert property(
      wb_master_chk_17_p) else
         sva_checker_error( "ERROR : Linear incrementing burst must increment the ADR_O");

`endif // ASSERT_ON
endinterface : wb_master_chk_if 

// $Log: master_chk.sv,v $
// Revision 1.10  2005/09/10 16:35:37  manojt
//  replaced the module with interface
//
// Revision 1.9  2005/09/09 14:39:11  janick
// Added SNPS IP notice
//
// Revision 1.8  2005/09/09 06:40:18  manojt
// corrected the checker for clean Magellan Run
//
// Revision 1.6  2005/06/15 21:37:02  manojt
// corrected disable iff in first two checkers
//
// Revision 1.5  2005/06/06 20:48:08  manojt
// integrated with VMM testbench
//
// Revision 1.4  2005/06/01 17:59:20  edcerny
// Example 3-56
//
// Revision 1.3  2005/04/20 06:06:44  manojt
// Corrected the missed comment around log
//
// Revision 1.2  2005/04/15 12:38:46  manojt
// First version of VMM Wishbone checker, that is compliant with the suggested file names and module names. The checker is made specific to follow wishbone module for opencores ethernet core

// Revision 1.1  2005/04/15 12:21:33  manojt
// *** empty log message ***

