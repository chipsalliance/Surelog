// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: pcx_buf_fpio.v
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


module pcx_buf_fpio(/*AUTOARG*/
   // Outputs
   pcx_fpio_data_px, pcx_fpio_data_rdy_px, 
   // Inputs
   pcx_fpio_data_ff_px, pcx_fpio_data_rdy_arb_px
   );

   output [`PCX_WIDTH-1:0]pcx_fpio_data_px;
   output                 pcx_fpio_data_rdy_px;

   input [`PCX_WIDTH-1:0]pcx_fpio_data_ff_px;
   input                 pcx_fpio_data_rdy_arb_px;


   assign pcx_fpio_data_px[`PCX_WIDTH-1:0] = pcx_fpio_data_ff_px[`PCX_WIDTH-1:0];
   assign pcx_fpio_data_rdy_px = pcx_fpio_data_rdy_arb_px;
   
endmodule

