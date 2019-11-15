// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_databuf_pa.v
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

`include	"sys.h" // system level definition file which contains the 
			// time scale definition

`include "iop.h"


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


module pcx_databuf_pa(/*AUTOARG*/
   // Outputs
   spc_pcx_data_buf_pa, spc_pcx_data_buf_rdy, 
   // Inputs
   spc_pcx_data_pa, spc_pcx_data_rdy
   );

   output [123:0]spc_pcx_data_buf_pa;
   output        spc_pcx_data_buf_rdy;

   input [123:0]spc_pcx_data_pa;
   input        spc_pcx_data_rdy;

   assign spc_pcx_data_buf_pa = spc_pcx_data_pa;
   assign spc_pcx_data_buf_rdy  =  spc_pcx_data_rdy;
   
   
endmodule
