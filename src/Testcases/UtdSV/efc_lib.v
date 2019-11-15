// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: efc_lib.v
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
//  Description:	efuse library
*/
////////////////////////////////////////////////////////////////////////

// TRANSPARENT LATCH 
module bw_efc_latch (d,  c, q );
// synopsys template

parameter SIZE = 1;

input	[SIZE-1:0]	d ;	// data in
input			c ;	// latch control

output	[SIZE-1:0]	q ;	// output


//always @ (posedge clk)
//
//      q[SIZE-1:0]  <= (se) ? si[SIZE-1:0]  : din[SIZE-1:0] ;
//
//assign so[SIZE-1:0] = q[SIZE-1:0] ;
//    assign so = ~so_l;
//    always @ ( ck or sd or se )
//       if (~ck) so_l = ~(sd & se) ;

bw_u1_scanlg_2x u_lat[SIZE-1:0] ( 
					.so (q),
					.ck (c),
					.sd (d),
					.se(1'b1));


endmodule // dff
