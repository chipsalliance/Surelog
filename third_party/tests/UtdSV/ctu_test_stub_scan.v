// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_test_stub_scan.v
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
//
//    Cluster Name:  CTU
//-----------------------------------------------------------------------------

`include "sys.h"

module ctu_test_stub_scan (/*AUTOARG*/
// Outputs
se, so_0, 
// Inputs
global_shift_enable, ctu_tst_scan_disable, 
//ctu_tst_scanmode, 
ctu_tst_short_chain, long_chain_so_0, short_chain_so_0
);

   input        global_shift_enable;
   input        ctu_tst_scan_disable;
   //input        ctu_tst_scanmode;
   input 	ctu_tst_short_chain;
   input 	long_chain_so_0;
   input 	short_chain_so_0;
   
   output 	se;
   output 	so_0;

   //wire 	testmode_l;
   wire         short_chain_select;


   assign  se                 = ~ctu_tst_scan_disable & global_shift_enable;
   //assign  testmode_l         = ~ctu_tst_scanmode;
   assign  short_chain_select = ctu_tst_short_chain;
   assign  so_0               = short_chain_select ? short_chain_so_0 : long_chain_so_0;
   
endmodule 
