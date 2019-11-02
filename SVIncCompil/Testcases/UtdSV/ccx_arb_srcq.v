// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_arb_srcq.v
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
/*
//
//  Module Name:        arb_srcq.v
//	Description:	module for queuing logic from source, maintained 
 //                     in arbiter.
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////
 
`include	"sys.h" // system level definition file which contains the 
			// time scale definition
`include "iop.h"
 
module ccx_arb_srcq(/*AUTOARG*/
   // Outputs
   qfull, qsel0, qsel1, shift_x, ctl_qsel0_a, ctl_qsel1_a_l, 
   ctl_shift_a, q0_hold_a, atom_a, 
   // Inputs
   req_q, atom_q, grant_a, rclk, reset_d1
   );
 
   output        qfull;
   output 	 qsel0;
   output 	 qsel1;
   output 	 shift_x;
   output 	 ctl_qsel0_a,ctl_qsel1_a_l;
   output 	 ctl_shift_a;
   output 	 q0_hold_a;
   output        atom_a;
   
   input 	 req_q;
   input 	 atom_q;
   input 	 grant_a;
   
   input 	 rclk;
   input 	 reset_d1;
   
   wire [1:0] 	 qcount_decr, qcount_decr_d1, qcount_decr_r_d1;
   wire [1:0] 	 qcount_incr;
   wire  	 qsel0,qsel1_l;
   wire 	 shift_a, shift_x, q0_hold_a_l;
   
   wire 	 shift_hi, shift_hi_d1;
   wire 	 qfull;
   wire 	 incr_a;
   wire 	 decr;
   wire 	 atom_rqqual_x, atom_rqqual_a ;
   wire 	 req_atomqual_a;
   wire 	 req_a, atom_a, qfull_a;
   
   

   //req_a generation
   //The term on the rhs of '|' handles the optimisation for
   // the Imiss following the load case, where the 2nd Imiss packet
   // is in the output queue.
   
// assign atom_rqqual_q = atom_q & req_q | atom_rqqual_a & qfull;

   dff_s #(1) dff_ccx_com_atom(
            .din           (atom_q),
	    .q             (atom_a),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
 

   dff_s #(1) dff_ccx_com_req(
            .din           (req_q),
	    .q             (req_a),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
 

   dff_s #(1) dff_ccx_com_qf(
            .din           (qfull),
	    .q             (qfull_a),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
 
 assign atom_rqqual_a = atom_a & req_a | atom_rqqual_x & qfull_a & ~reset_d1;

   dff_s #(1) dff_ccx_com_atomq(
            .din           (atom_rqqual_a),
	    .q             (atom_rqqual_x),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());


   assign req_atomqual_a = (atom_rqqual_x | req_a) & (~qfull_a & ~reset_d1);

   assign incr_a = req_atomqual_a ;
   
   
   //Qfull and Shift_hi generation

   assign qfull = qcount_incr[1];
   assign shift_hi = ~(qcount_decr[1] | qcount_decr[0]);

   dff_s #(1) dff_ccx_com_shift_hi(
            .din           (shift_hi),
	    .q             (shift_hi_d1),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
   
   
//Decrement Muxes

   assign decr = grant_a & ~reset_d1;
   
      mux2ds #(1) mx2ds_ccx_com_decr0(
	    .dout            (qcount_decr[0]),
	    .in0             (qcount_incr[0]),		    	    
            .in1             (qcount_incr[1]),
	    .sel0            (~decr),
	    .sel1            (decr));
   
      mux2ds #(1) mx2ds_ccx_com_decr1(
	    .dout            (qcount_decr[1]),
	    .in0             (qcount_incr[1]),		    	    
            .in1             (1'b0),
	    .sel0            (~decr),
	    .sel1            (decr));


//Queue state flops

   dff_s #(1) dff_ccx_com_decr0(
            .din           (qcount_decr[0]),
	    .q             (qcount_decr_d1[0]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());

   assign qcount_decr_r_d1[0] = qcount_decr_d1[0] & ~reset_d1;
   
   dff_s #(1) dff_ccx_com_decr1(
            .din           (qcount_decr[1]),
	    .q             (qcount_decr_d1[1]),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
   assign qcount_decr_r_d1[1] = qcount_decr_d1[1] & ~reset_d1;

//Increment Muxes
      mux2ds #(1) mx2ds_ccx_com_incr0(
	    .dout            (qcount_incr[0]),
	    .in0             (qcount_decr_r_d1[0]),		    	    
            .in1             (shift_hi_d1),
	    .sel0            (~incr_a),
	    .sel1            (incr_a));

      mux2ds #(1) mx2ds_ccx_com_incr1(
	    .dout            (qcount_incr[1]),
	    .in0             (qcount_decr_r_d1[1]),		    	    
            .in1             (qcount_decr_r_d1[0]),
	    .sel0            (~incr_a),
	    .sel1            (incr_a));



   //Generate Mux selects for arb dps

//   assign qsel1_l = ~(qcount_incr[1] & incr_a);
   assign qsel1 = (qcount_incr[1] & incr_a);

   assign qsel0 = qcount_incr[0] & incr_a;

   assign shift_a = qcount_incr[1] & grant_a;

      dff_s #(1) dff_ccx_com_shiftx(
            .din           (shift_a),
	    .q             (shift_x),
	    .clk           (rclk),
	    .se            (1'b0),
	    .si            (1'b0),
	    .so            ());
   
//   assign q0_hold_a_l = ~qsel0  & ~shift_x;
   assign q0_hold_a = ~(~qsel0  & ~shift_x);
   
   //Generate Mux selects for atomq ctl

   assign ctl_qsel1_a_l = ~(qcount_decr_r_d1[0] & incr_a & ~grant_a);

   assign ctl_qsel0_a = (qcount_incr[0] & incr_a) |
                        (qcount_decr_r_d1[0] & incr_a & grant_a);

   assign ctl_shift_a = qcount_decr_r_d1[1] & grant_a;

   // q1write - if cnt_decr=2'b01 in previous cycle and new req=1 in current cycle and grant=0
   // q0write - if cnt_decr=2'b01 in previous cycle and new req=1 in current cycle and grant=1 OR
   //           if cnt_incr=2'b01 and new_req=1
   // shift   - if cnt_decr=2'b10 in previous cycle and grant=1

   // qcnt is same as qcount_decr_r_d1
   //
   //---------------------------------------------------------
   //          0        1         2         3          4
   //---------------------------------------------------------
   //     req_a=1(R1)   1(R2)
   //     atm_a=0       0/1
   //
   //     grant=0       1(R1)    1(R2)      0          0
   //
   // dp: qsel0=1     qsel1=1*   shift=1
   //                 q0=(R1)    q0=(R1)    q0=(R2)
   //                            q1=(R2)
   //
   //ctl: qsel0=1     qsel0=1*    
   //                 q0=(R1)    q0=(R2)
   //
   //     qfull_a=0     0        1          0          0
   // 
   //     qcnt=0        1        1          1          0
   //---------------------------------------------------------

   //---------------------------------------------------------
   //          0        1         2         3          4
   //---------------------------------------------------------
   //     req_a=1(R1)   1(R2)
   //     atm_a=0       0/1
   //
   //     grant=0       0        1(R1)    1(R2)        0 
   //
   // dp: qsel0=1     qsel1=1             shift=1
   //                 q0=(R1)    q0=(R1)  q0=(R1)    q0=(R2)
   //                            q1=(R2)  q1=(R2)
   //
   //ctl: qsel0=1     qsel1=1    shift=1*
   //                 q0=(R1)    q0=(R1)  q0=(R2)
   //                            q1=(R2)
   //
   //     qfull_a=0     0        1          1          0 <- in cycle 4, new req can be written into dp, and ctl
   // 
   //     qcnt=0        1        2          1          0
   //---------------------------------------------------------


   // for atomic requests 2 writes are done to ctl. The value of atomic on the sparc bus 
   // is "garbage" for 2nd write. This data is not used by arbiter. 1st grant for an 
   // atomic is remembered and request(qual_req) is not set for the 2nd grant.
   // The 2nd write data will overwritten by the next new request or by shift.

endmodule 

// Lopal Variables:
// verilog-library-directories:("." "../../../../../common/rtl")
// End:

