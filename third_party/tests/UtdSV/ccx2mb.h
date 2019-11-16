/*
* ========== Copyright Header Begin ==========================================
* 
* OpenSPARC T1 Processor File: ccx2mb.h
* Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
* DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
* 
* The above named program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public
* License version 2 as published by the Free Software Foundation.
* 
* The above named program is distributed in the hope that it will be 
* useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* General Public License for more details.
* 
* You should have received a copy of the GNU General Public
* License along with this work; if not, write to the Free Software
* Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
* 
* ========== Copyright Header End ============================================
*/
/***************************************************************************
 * ccx2mb.h:	Defines needed by the ccx2mb interface block.
 *		Note that any of these defines could be defined elsewhere:
 *		for example, in sys.h, iop.h.
 *
 * $Id: $
 ***************************************************************************/


`ifndef FSL_D_WIDTH
`define FSL_D_WIDTH  32
`endif

`ifndef PCX_WIDTH
`define PCX_WIDTH   124
`endif

`ifndef CPX_WIDTH
`define CPX_WIDTH   145
`endif

// To pass all 5 bits of the PCX request to the FIFO, the following variable
// must be defined:
// `define PCX2MB_5_BIT_REQ
