// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: cpx_buf_io.v
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


////////////////////////////////////////////////////////////////////////
// Local header file includes / local defines
////////////////////////////////////////////////////////////////////////


`include	"sys.h"
`include	"iop.h"

module cpx_buf_io(/*AUTOARG*/
   // Outputs
   cpx_io_grant_bufio_ca, io_cpx_req_bufio_cq_l, 
   // Inputs
   cpx_io_grant_ca, io_cpx_req_cq
   );
   output [7:0]         cpx_io_grant_bufio_ca;
   output [7:0]		io_cpx_req_bufio_cq_l;	

   

   input [7:0]          cpx_io_grant_ca;
   input [7:0]		io_cpx_req_cq;	

   
   assign               cpx_io_grant_bufio_ca    =  cpx_io_grant_ca;
   assign		io_cpx_req_bufio_cq_l    =  ~io_cpx_req_cq;


endmodule 

