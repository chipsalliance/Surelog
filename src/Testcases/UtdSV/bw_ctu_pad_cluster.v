// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: bw_ctu_pad_cluster.v
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
//    Unit Name:  bw_ctu_pad_cluster
//    Block Name: ctu_pad_cluster
//
//-----------------------------------------------------------------------------

`include "sys.h"

module bw_ctu_pad_cluster (

// Inouts:

 jclk ,             // Differential System Clock Inputs
 tsr_testio ,       // Tempsensor test signals
 vddo ,             // 1.5V vdd
 vdda               // 1.8V analog vdd
);

 inout [1:0] jclk;
 inout [1:0] tsr_testio;
 inout       vddo;
 inout       vdda;

//synopsys translate_off


//synopsys translate_on

endmodule    

