// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ctu_mask_id.v
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
//    Unit Name: ctu_mask_id

// Mask programmable revision cell. The cell generates a 4-bit value based
// on the output of four 9-input XOR-trees. Each XOR-tree has an input
// connection to each of Niagara's 9 metal layers. The inputs are connected
// to 0 or 1 by means of metal straps connected to pull-downs and pull-ups.
// The cell is constructed such that only metal fill or removal is needed
// to alter the die's revision using any number of metal layer changes.

module ctu_mask_id (/*AUTOARG*/
// Outputs
mask_id
);

output [3:0] mask_id;

parameter [9:1] id3_m = 9'b0;
parameter [9:1] id2_m = 9'b0;
parameter [9:1] id1_m = 9'b0;
parameter [9:1] id0_m = 9'b0;

//        Input layer : metal 1    metal 2    metal 3    metal 4    metal 5    metal 6    metal 7    metal 8    metal 9
assign 	   mask_id[0] = id0_m[1] ^ id0_m[2] ^ id0_m[3] ^ id0_m[4] ^ id0_m[5] ^ id0_m[6] ^ id0_m[7] ^ id0_m[8] ^ id0_m[9];
assign 	   mask_id[1] = id1_m[1] ^ id1_m[2] ^ id1_m[3] ^ id1_m[4] ^ id1_m[5] ^ id1_m[6] ^ id1_m[7] ^ id1_m[8] ^ id1_m[9];
assign 	   mask_id[2] = id2_m[1] ^ id2_m[2] ^ id2_m[3] ^ id2_m[4] ^ id2_m[5] ^ id2_m[6] ^ id2_m[7] ^ id2_m[8] ^ id2_m[9];
assign 	   mask_id[3] = id3_m[1] ^ id3_m[2] ^ id3_m[3] ^ id3_m[4] ^ id3_m[5] ^ id3_m[6] ^ id3_m[7] ^ id3_m[8] ^ id3_m[9];

endmodule
