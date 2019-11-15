// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_arb_atomq.v
// Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
// DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
// 
// The above named program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public
// License version 2 as published by the Free Software Foundation.
// 
// The above named program is distributed in the hope that it will be 
// useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
// 
// You should have received a copy of the GNU General Public
// License along with this work; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
// 
// ========== Copyright Header End ============================================


////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////

`include	"sys.h" // system level definition file which contains the 
			// time scale definition

`include "iop.h"

// USES srcq select signals; ignore qcount code in this file

////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////

module ccx_arb_atomq(/*AUTOARG*/
   // Outputs
   q0_dataout, scan_out, 
   // Inputs
   ctl_qsel1_a_l, ctl_qsel0_a, ctl_shift_a, atom_a, rclk, reset_d1
   );	

   output         q0_dataout;  // pcx to destination pkt
   output 	  scan_out;
   
   
   input  	           ctl_qsel1_a_l;  // queue write sel
   input  	           ctl_qsel0_a;  // queue write sel
   input 		   ctl_shift_a;//grant signal

   input   atom_a;  // spache to pcx data
   
   input 		   rclk;
   //input 		   tmb_l;
   input		   reset_d1;

   wire    q0_datain_pa;
   wire    q1_datain_pa;
   wire    q1_dataout;
   wire    q1_data_out;
   wire    q0_data_out;


//HEADER SECTION

   
//DATAPATH SECTION

assign	q1_datain_pa  =  ~ctl_qsel1_a_l ? atom_a : q1_dataout;
   
   dff_s   #(1) dff_pcx_atomin_q1(
	    .din           (q1_datain_pa),
	    .q             (q1_data_out),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (),
	    .so            ());

assign	q1_dataout  =  ~reset_d1 ? q1_data_out : 1'b0;

assign q0_datain_pa = 
             ctl_qsel0_a ? atom_a :
	     ctl_shift_a ? q1_dataout : 
             q0_dataout;
  
   dff_s   #(1) dff_pcx_atomin_q0(
	    .din           (q0_datain_pa),
	    .q             (q0_data_out),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (),
	    .so            ());
   
   
assign q0_dataout = ~reset_d1 ? q0_data_out : 1'b0;
 	 
//    Global Variables:
// verilog-library-directories:("." "../../../../../common/rtl" "../rtl")
// End:


   
// Code start here 
//
endmodule



