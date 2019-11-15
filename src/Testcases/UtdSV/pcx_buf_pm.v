// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_pm.v
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
//	Description:	datapath portion of CPX
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


`include	"sys.h"
`include	"iop.h"

module pcx_buf_pm(/*AUTOARG*/
   // Outputs
   pcx_spc_grant_bufpm_pa, pcx_stall_bufpm_pq, 
   // Inputs
   pcx_spc_grant_pa, pcx_stall_pq
   );

   output [4:0]		pcx_spc_grant_bufpm_pa;
   output               pcx_stall_bufpm_pq;
   
   input [4:0]		pcx_spc_grant_pa;
   input                pcx_stall_pq;
   
   assign               pcx_spc_grant_bufpm_pa     =        pcx_spc_grant_pa;
   assign               pcx_stall_bufpm_pq         =        pcx_stall_pq;

endmodule 

