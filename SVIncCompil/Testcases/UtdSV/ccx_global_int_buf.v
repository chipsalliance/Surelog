// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: ccx_global_int_buf.v
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


`include	"sys.h"
`include	"iop.h"

module ccx_global_int_buf(/*AUTOARG*/
   // Outputs
   rst_l_buf, se_buf, adbginit_l_buf, 
   // Inputs
   rst_l, se, adbginit_l
   );
   output          rst_l_buf ;
   output          se_buf ;
   output          adbginit_l_buf ;
   

   input 	   rst_l ;	
   input          se ;
   input          adbginit_l ;

   
   assign               rst_l_buf    =  rst_l;
   assign               se_buf    =  se;
   assign               adbginit_l_buf  =  adbginit_l ;


endmodule 

