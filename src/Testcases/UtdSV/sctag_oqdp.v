// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_oqdp.v
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
//  Module Name: sctag_oqdp.v
//  Description:      
//	 * Flops to delay the invalidation vec in C5 by 1 cycle from
//	 * Flops to delay the data returned by 2 cycles 	
//	 * Muxes to choose between directory data and data returned
//		by the data array.
//	 * Mux to select between the data from the OQ, an older req
//		or the current request.
//	 * A mux to determine the input data into the OQ array.
//	      The data return path and the input to the OQ are both critical paths.
/////////////////////////////////////////////////////
// Change 6/13/2003:
// mux1  & mux2 selects are computed here.
// The c8 logic used to be in oqctl but now has been
// moved to oqdp.
/////////////////////////////////////////////////////
*/
////////////////////////////////////////////////////////////////////////
// Global header file includes
////////////////////////////////////////////////////////////////////////
`include 	"iop.h"
`include 	"sctag.h"



module sctag_oqdp(/*AUTOARG*/
   // Outputs
   so, oq_array_data_in, sctag_cpx_data_ca, oqdp_tid_c8, 
   // Inputs
   arbdp_inst_l1way_c7, arbdp_inst_size_c7, arbdp_inst_tid_c7, 
   arbdp_inst_nc_c7, arbdp_inst_cpuid_c7, oqctl_rqtyp_rtn_c7, 
   dirdp_way_info_c7, strst_ack_c7, arbdp_oqdp_int_ret_c7, 
   rst_tri_en, fwd_req_ret_c7, oqctl_int_ack_c7, 
   arbdp_oqdp_l1_index_c7, oqctl_imiss_hit_c8, retdp_data_c8, 
   retdp_err_c8, dirdp_inval_pckt_c7, retdp_diag_data_c7, 
   tagdp_diag_data_c7, vuad_dp_diag_data_c7, oq_array_data_out, 
   oqctl_pf_ack_c7, oqctl_rmo_st_c7, atm_inst_ack_c7, str_ld_hit_c7, 
   oqctl_diag_acc_c8, oqctl_cerr_ack_c7, oqctl_uerr_ack_c7, 
   mux1_sel_data_c7, sel_array_out_l, mux_csr_sel_c7, sel_inval_c7, 
   out_mux1_sel_c7, out_mux2_sel_c7, arbdp_line_addr_c7, 
   dc_inval_vld_c7, ic_inval_vld_c7, csr_rd_data_c8, 
   oqctl_l2_miss_c7, rclk, si, se
   );




input	[1:0]	arbdp_inst_l1way_c7 ;
input   [2:1]   arbdp_inst_size_c7; // POST_4.0 change
input   [1:0]   arbdp_inst_tid_c7;
input           arbdp_inst_nc_c7;
input	[2:0]	arbdp_inst_cpuid_c7 ;
input	[3:0]   oqctl_rqtyp_rtn_c7;
input	[2:0]	dirdp_way_info_c7;
input		strst_ack_c7;
input	[17:0]	arbdp_oqdp_int_ret_c7;
input		rst_tri_en; // NEW_PIN 

input		fwd_req_ret_c7 ; 

input		oqctl_int_ack_c7;
input	[11:6]	arbdp_oqdp_l1_index_c7;
input	        oqctl_imiss_hit_c8;
input   [127:0]	retdp_data_c8;
input   [2:0]	retdp_err_c8;
input   [111:0]	dirdp_inval_pckt_c7;
input	[38:0]  retdp_diag_data_c7 ;
input	[27:0]  tagdp_diag_data_c7;
input	[33:0]	vuad_dp_diag_data_c7;
input	[`CPX_WIDTH-1:0] oq_array_data_out ;
input           oqctl_pf_ack_c7; // NEW_PIN from oqctl.
input		oqctl_rmo_st_c7; // NEW_PIN from oqctl.

input		atm_inst_ack_c7;
input		str_ld_hit_c7 ;
input		oqctl_diag_acc_c8;
input		oqctl_cerr_ack_c7; // asynchronous corr err 
input		oqctl_uerr_ack_c7; // asynchronous uncorr err 

input  [3:0]	mux1_sel_data_c7; // mux sels
input		sel_array_out_l; // Mux sel from oqctl. NEW_PIN
input  		mux_csr_sel_c7;
input		sel_inval_c7; // sel for oqarray_data_in
input	[2:0]	out_mux1_sel_c7; // sel for mux1
input	[2:0]	out_mux2_sel_c7; // sel for mux2


input	[5:4]	arbdp_line_addr_c7; // from arbaddr dp
input		dc_inval_vld_c7; // from tagctl
input		ic_inval_vld_c7; // from tagctl

input	[63:0]	csr_rd_data_c8;
input		oqctl_l2_miss_c7 ; // NEW_PIN 

input		rclk;

output	so;
input	si, se;

output	[`CPX_WIDTH-1:0] oq_array_data_in ;
output	[`CPX_WIDTH-1:0] sctag_cpx_data_ca;
output	[4:0]		oqdp_tid_c8 ;



wire	[`CPX_WIDTH-12:0]  ext_inval_data_c8;
wire	[`CPX_WIDTH-12:0]  ext_retdp_data_c8;

wire	[`CPX_WIDTH-1:0]   staged_data_out_c9;
wire	[`CPX_WIDTH-1:0]   staged_cpx_packet_c9;


wire	[1:0]	inst_tid_c8;
wire		inst_nc_c8;

wire	[1:0]	tid_c7;
wire		nc_bit_c7 ;

wire	[1:0]	tid_c8;
wire		nc_bit_c8 ;

wire  [3:0]     oqctl_rqtyp_rtn_c8;


wire	[2:0]	inval_buf_c7;
wire	[2:0]	inval_buf_c8;
wire	[`CPX_WIDTH-1:0] 	eff_oqarray_dout;
wire	[`CPX_WIDTH-1:0] 	eff_oqarray_dout_d1;

wire	[38:0]	tmp_inval_data_c7 ;
wire		int_or_diag_sel_c7;
wire	[127:0]	ext_inval_data_c7;

wire	[2:0]	mod_sz_field_st_c7 ;
wire	[1:0]	l1_way_c8;
wire		sel_c8 ;
wire	[2:0]	inst_cpuid_c8;
wire	[2:0]	cpuid_c7;
wire	[2:0]	cpuid_c8;

wire	[5:0]	inst_inval_index_c8;
wire	[5:0]	inval_index_c7;
wire	[63:0]	dir_or_csr_data;

wire	[2:0]	async_error_c7;

wire	[2:0]	mod_sz_field_ld_c7;
wire	[2:0]	ret_buf_c8;
wire	[2:0]	inval_way_c7;
wire	[2:0]	ret_way_c7;
wire	[2:0]	inval_way_c8;
wire	[2:0]	ret_way_c8;
wire	[1:0]	inst_l1way_c7;
wire	[`CPX_WIDTH-1:0]	tmp_cpx_data_ca;

wire	[2:0]	error_field_c7;
wire	[2:0]	error_field_c8;
wire	[2:0]	rtn_err_field_c8;
wire	[`CPX_WIDTH-1:0] oqdp_cpx_data_c8;


wire	[3:0]	hi_inval_c7 ;
wire	[3:0]	hi_inval_c8 ;
wire	[3:0]	cpx_hi_inval_c7;

wire	rmo_st_c8;
wire	cpx_rmo_c7;

wire    csr_or_diag_sel_c7_111to64 ;
wire    csr_or_diag_sel_c7_127to112 ;
wire	[2:0]	mux1_sel_c8 ;
wire	[2:0]	out_mux1_sel_c8 ;
wire	[2:0]	mux2_sel_c8 ;
wire	[2:0]	out_mux2_sel_c8 ;


////////////////////////////////////////////////////////////////////////////////
//____________________________________________________________________
//Pkt |bits|No |Load|I$f |I$f |Strm|Evct|Stor|Strm|Int | FP |Fwd |Err |
//    |    |   |    | 1  | 2  |Load| Inv|Ack |Stor|    |    |rep |    |
//    |    |   |    |    |    |    |    |    |Ack |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//Vld |144 | 1 | V  | V  | V  | V  | V  | V  | V  | V  | V  | V  | V  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//Rtn |143 | 4 |0000|0001|0001|0010|0011|0100|0110|0111|1000|1011|1100|
//Typ |140 |   |    |    |    |    |    |    |    |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//ERR |139 | 3 | V  | V  | V  | V  | X  | X  | X  | X  | X  | V  | V  |
//    |137 |   |    |    |    |    |    |    |    |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
// NC |136 | 1 | V  | V  | V  | V  | V  | V  | V  |flus| V  |R/!W| X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |135 | 1 | T  | T  | T  | T  | X  | T  | T  | X  | T  | X  | 0  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |134 | 1 | T  | T  | T  | T  | X  | T  | T  | X  | T  | X  | 0  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |133 | 1 | WV | WV | WV | WV | X  | X  | X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |132 | 1 | W  | W  | W  | W  | X  | X  | X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |131 | 1 | W  | W  | W  | W  | X  | P  | X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |130 | 1 | X  | X  | X  | A  | X  | P  | A  | X  | X  | X  | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |129 | 1 |atm | X  | X  | B  | X  |atm | X  | X  | X  | X  | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |128 | 1 | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//data|127 |128|    |    |    |    |6PA,|3cpu|3cpu|    |    |    |    |
//    |0   |   | V  | V  | V  | V  |112 |6PA,|6pa,|    |    | +  |    |
//    |    |   |    |    |    |    |Inv |112 |112 | V! | V* |Data|Add |
//    |    |   |    |    |    |    |    |Inv |Inv |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |    |   |    |    |    |    |    |    |    |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// In casse of Imiss or Diag instruction a bubble is inserted and
// a dummy instruction is inserted in the next cycle that looks
// like the current instruction. sel_c8 is used to select the
// bit fields for the dummy instruction, which is the delayed
// version of the original values.

assign  sel_c8 = (oqctl_imiss_hit_c8 | oqctl_diag_acc_c8) ;


////////////////////////////////////////////////////////////////////////////////
// TID (Thread ID), bit 135:134 of the CPX Packet
////////////////////////////////////////////////////////////////////////////////
dff_s   #(2)   ff_arbdp_tid_c8
              (.q   (inst_tid_c8[1:0]),
               .din (arbdp_inst_tid_c7[1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(2)  mux_tid_c7
              (.dout (tid_c7[1:0]),
               .in0  (arbdp_inst_tid_c7[1:0]),  .sel0 (~sel_c8),
               .in1  (inst_tid_c8[1:0]),        .sel1 (sel_c8)
              ) ;

dff_s   #(2)   ff_tid_c8
              (.q   (tid_c8[1:0]),
               .din (tid_c7[1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// NC (Non Cachable) bit, bit 136 of the CPX Packet
////////////////////////////////////////////////////////////////////////////////
dff_s   #(1)   ff_arbdp_nc_c8
              (.q   (inst_nc_c8),
               .din (arbdp_inst_nc_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(1)  mux_nc_c7
              (.dout (nc_bit_c7),
               .in0  (arbdp_inst_nc_c7),  .sel0 (~sel_c8),
               .in1  (inst_nc_c8),        .sel1 (sel_c8)
              ) ;

dff_s   #(1)   ff_nc_c8
              (.q   (nc_bit_c8),
               .din (nc_bit_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// RQTYP (Return request type), bit 143:140 of the CPX Packet
////////////////////////////////////////////////////////////////////////////////
dff_s   #(4)   ff_rqtyp_rtn_c8
              (.q   (oqctl_rqtyp_rtn_c8[3:0]),
               .din (oqctl_rqtyp_rtn_c7[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// SIZE, bit 130:128 of the CPX Packet
//_____________________________________________________________________
//Pkt |bits|No |Load|I$f |I$f |Strm|Evct|Stor|Strm|Int | FP |Fwd |Err |
//    |    |   |    | 1  | 2  |Load| Inv|Ack |Stor|    |    |rep |    |
//    |    |   |    |    |    |    |    |    |Ack |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |130 | 1 | X  | X  | X  | A  | X  |P[0]| A  | X  | X  | X  | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |129 | 1 |atm | X  | X  | B  | X  |atm | X  | X  | X  | X  | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |128 | 1 | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  | 0  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|

////////////////////////////////////////////////////////////////////////////////
dff_s   #(2)   ff_l1_way_c8
              (.q   (l1_way_c8[1:0]),
               .din (arbdp_inst_l1way_c7[1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(2)  mux_l1_way_c7
              (.dout (inst_l1way_c7[1:0]),
               .in0  (arbdp_inst_l1way_c7[1:0]),  .sel0 (~sel_c8),
               .in1  (l1_way_c8[1:0]),            .sel1 (sel_c8)
              ) ;

// sz_field == {P[0], atomic, 1'b0} for Store instruction
//          == {A, X, 1'b0}         for Streaming Store instruction
// inst_l1way_c7 == P[1:0] in case of Store instruction
//               == {A, X} in case of Streaming Store instruction
assign  mod_sz_field_st_c7[2] = inst_l1way_c7[0] ;
assign  mod_sz_field_st_c7[1] = atm_inst_ack_c7 ; // qualified.
assign  mod_sz_field_st_c7[0] = 1'b0;

mux2ds #(3)  mux_buf_c7
              (.dout (inval_buf_c7[2:0]),
               .in0  (mod_sz_field_st_c7[2:0]),    .sel0 (~strst_ack_c7),
               .in1  ({inst_l1way_c7[1:0],1'b0}),  .sel1 (strst_ack_c7)
              ) ;

dff_s   #(3)   ff_inval_buf_c8
              (.q   (inval_buf_c8[2:0]),
               .din (inval_buf_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


// sz_field == {X, atomic, prefetch} for Load instruction
//          == {A, B, 1'b0}      for Streaming Load instruction

assign  mod_sz_field_ld_c7[2] =  arbdp_inst_size_c7[2] & str_ld_hit_c7 ;
assign  mod_sz_field_ld_c7[1] = (arbdp_inst_size_c7[1] & str_ld_hit_c7) | 
                                 atm_inst_ack_c7 ;
assign  mod_sz_field_ld_c7[0] = oqctl_pf_ack_c7 ; // only set for a Prefetch response.

dff_s   #(3)   ff_ret_buf_c8
              (.q   (ret_buf_c8[2:0]),
               .din (mod_sz_field_ld_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// CPUID
////////////////////////////////////////////////////////////////////////////////
dff_s   #(3)   ff_inst_cpuid_c8
              (.q   (inst_cpuid_c8[2:0]),
               .din (arbdp_inst_cpuid_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(3)  mux_cpuid_c7
              (.dout (cpuid_c7[2:0]),
               .in0  (arbdp_inst_cpuid_c7[2:0]),  .sel0 (~sel_c8),
               .in1  (inst_cpuid_c8[2:0]),        .sel1 (sel_c8)
              ) ;

mux2ds #(3)  int_diag_sel120to118
              (.dout (ext_inval_data_c7[120:118]),
               .in0  (cpuid_c7[2:0]),              .sel0 (~csr_or_diag_sel_c7_127to112),
               .in1  (ext_inval_data_c7[56:54]),   .sel1 (csr_or_diag_sel_c7_127to112)
              ) ;
dff_s   #(3)   ff_inval_data120to118_c8
              (.q   (ext_inval_data_c8[120:118]),
               .din (ext_inval_data_c7[120:118]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;

assign  cpuid_c8[2:0] = ext_inval_data_c8[120:118] ;


assign  oqdp_tid_c8 = {cpuid_c8[2:0], tid_c8[1:0]} ;


////////////////////////////////////////////////////////////////////////////////
// WAY-INFO
//_____________________________________________________________________
//Pkt |bits|No |Load|I$f |I$f |Strm|Evct|Stor|Strm|Int | FP |Fwd |Err |
//    |    |   |    | 1  | 2  |Load| Inv|Ack |Stor|    |    |rep |    |
//    |    |   |    |    |    |    |    |    |Ack |    |    |    |    |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |133 | 1 | WV | WV | WV | WV | X  | X  | X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |132 | 1 | W  | W  | W  | W  | X  | X  | X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//    |131 | 1 | W  | W  | W  | W  | X  |P[1]| X  | X  | X  |tar | X  |
//____|____|___|____|____|____|____|____|____|____|____|____|____|____|
//
// In case of Forward Request instruction, CPU ID field of the PCX packet will
// contain the Source of the Forward Request, that Surce ID will be returned as
// Target ID by the L2 in the Forward Reply packet. Target ID occupy same bit
// position in the Forward Reply packet as the Way Valid & Way bits for the
// Load & I$ fill packets.
////////////////////////////////////////////////////////////////////////////////
mux2ds #(3)  mux_inval_way_c7
              (.dout (inval_way_c7[2:0]),
               .in0  ({2'b0,inst_l1way_c7[1]}),  .sel0 (~fwd_req_ret_c7),
               .in1  (cpuid_c7[2:0]),            .sel1 (fwd_req_ret_c7)
              ) ;

dff_s   #(3)   ff_inval_way_c8
              (.q   (inval_way_c8[2:0]),
               .din (inval_way_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


//?? why ret_way_c7[2:0] != dirdp_way_info_c7[2:0] ;
mux2ds #(3)  mux_ret_way_c7
              (.dout (ret_way_c7[2:0]),
               .in0  (dirdp_way_info_c7[2:0]),  .sel0 (~fwd_req_ret_c7),
               .in1  (cpuid_c7[2:0]),           .sel1 (fwd_req_ret_c7)
              ) ;

dff_s   #(3)   ff_ret_way_c8
              (.q   (ret_way_c8[2:0]),
               .din (ret_way_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// INVAL INDEX.
////////////////////////////////////////////////////////////////////////////////
// Index bits[11:6] for the L1$. Although for D$ bits<4,5,8,9,10> and for I$
// bits<5,8,9,10,11> are used as index bits in L1$, bits<11:6> are send by the
// L2. For D$ bit<11> will be ignored and four inval bits corresponding to
// bits<5:4> == 00, 01, 10 & 11 are send. For I$ two inval bits corresponding to
// the bit<5> == 0 & 1 are send.
dff_s   #(6)   ff_inst_inval_index_c8
              (.q   (inst_inval_index_c8[5:0]),
               .din (arbdp_oqdp_l1_index_c7[11:6]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(6)  mux_inval_idx_c7
              (.dout (inval_index_c7[5:0]),
               .in0  (arbdp_oqdp_l1_index_c7[11:6]),  .sel0 (~sel_c8),
               .in1  (inst_inval_index_c8[5:0]),      .sel1 (sel_c8)
              ) ;


mux2ds #(6)  int_diag_sel117to112
              (.dout (ext_inval_data_c7[117:112]),
               .in0  (inval_index_c7[5:0]),        .sel0 (~csr_or_diag_sel_c7_127to112),
               .in1  (ext_inval_data_c7[53:48]),   .sel1 (csr_or_diag_sel_c7_127to112)
              ) ;

dff_s   #(6)   ff_inval_data117to112_c8
              (.q   (ext_inval_data_c8[117:112]),
               .din (ext_inval_data_c7[117:112]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// higher order bits or dir  payload.
// added to support the invalidation packet.
////////////////////////////////////////////////////////////////////////////////
assign  hi_inval_c7 = {ic_inval_vld_c7, dc_inval_vld_c7, arbdp_line_addr_c7} ;

dff_s   #(4)   ff_hi_inval_c8
              (.q   (hi_inval_c8[3:0]),
               .din (hi_inval_c7[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(4)  mux_cpx_hi_inval_c7
              (.dout (cpx_hi_inval_c7[3:0]),
               .in0  (hi_inval_c7[3:0]),  .sel0 (~sel_c8),
               .in1  (hi_inval_c8[3:0]),  .sel1 (sel_c8)
              ) ;

mux2ds #(4)  int_diag_sel124to121
              (.dout (ext_inval_data_c7[124:121]),
               .in0  (cpx_hi_inval_c7[3:0]),       .sel0 (~csr_or_diag_sel_c7_127to112),
               .in1  (ext_inval_data_c7[60:57]),   .sel1 (csr_or_diag_sel_c7_127to112)
              ) ;
dff_s   #(4)   ff_inval_data124to121_c8
              (.q   (ext_inval_data_c8[124:121]),
               .din (ext_inval_data_c7[124:121]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;


////////////////////////////////////////////////////////////////
// bit # 125 of the payload of a inval* packet
////////////////////////////////////////////////////////////////

dff_s   #(1)   ff_rmo_c8 (.q   (rmo_st_c8),
               .din (oqctl_rmo_st_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

mux2ds #(1)  mux_cpx_rmo_c7 (.dout (cpx_rmo_c7),
               .in0  (oqctl_rmo_st_c7),  .sel0 (~sel_c8),
               .in1  (rmo_st_c8),  .sel1 (sel_c8)
              ) ;

mux2ds #(1)  int_diag_sel125
              (.dout (ext_inval_data_c7[125]),
               .in0  (cpx_rmo_c7),              .sel0 (~csr_or_diag_sel_c7_127to112),
               .in1  (ext_inval_data_c7[61]),   .sel1 (csr_or_diag_sel_c7_127to112)
              ) ;
dff_s   #(1)   ff_inval_data125_c8
              (.q   (ext_inval_data_c8[125]),
               .din (ext_inval_data_c7[125]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// ERR FIELDS
// async errors from oqctl.
// sync errors from deccdp.
// THe MSB of the error field is used by the Performance counter
// to count the number of misses for a Load/Imiss/StrmLoad instruction.
////////////////////////////////////////////////////////////////////////////////


assign  async_error_c7 = {oqctl_l2_miss_c7, 
			oqctl_uerr_ack_c7,  // comes from pst/atomic stores and Dis errs from FB
			oqctl_cerr_ack_c7} ; // comes from pst/atomic stores and Dis errs from FB

assign  error_field_c7[2] = (async_error_c7[2]) ;
assign  error_field_c7[1] = (async_error_c7[1] | 
                            (retdp_err_c8[1] & oqctl_imiss_hit_c8)) ;
assign  error_field_c7[0] = (async_error_c7[0]) ;

dff_s   #(3)   ff_error_field_c8
              (.q   (error_field_c8[2:0]),
               .din (error_field_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign  rtn_err_field_c8 = error_field_c8 | retdp_err_c8 ;


////////////////////////////////////////////////////////////////////////////////
// DATA MUXES
////////////////////////////////////////////////////////////////////////////////

assign  int_or_diag_sel_c7 = (mux1_sel_data_c7[0] | mux1_sel_data_c7[1] |
                              mux1_sel_data_c7[2] | oqctl_int_ack_c7) ;


mux4ds #(39) mux_tmp_inv_data_c7
  (.dout (tmp_inval_data_c7[38:0]),
   .in0  (retdp_diag_data_c7[38:0]),              .sel0 (mux1_sel_data_c7[0]),
   .in1  ({11'b0, tagdp_diag_data_c7[27:0]}),     .sel1 (mux1_sel_data_c7[1]),
   .in2  ({5'b0, vuad_dp_diag_data_c7[33:0]}),    .sel2 (mux1_sel_data_c7[2]),
   .in3  ({21'b0, arbdp_oqdp_int_ret_c7[17:0]}),  .sel3 (mux1_sel_data_c7[3])
  ) ;

mux2ds #(64) mux_csr_sel
              (.dout (dir_or_csr_data[63:0]),
               .in0  (dirdp_inval_pckt_c7[63:0]),  .sel0 (~mux_csr_sel_c7),
               .in1  (csr_rd_data_c8[63:0]),       .sel1 (mux_csr_sel_c7)
              ) ;

mux2ds #(64) int_diag_sel63to0
              (.dout (ext_inval_data_c7[63:0]),
               .in0  (dir_or_csr_data[63:0]),            .sel0 (~int_or_diag_sel_c7),
               .in1  ({25'b0, tmp_inval_data_c7[38:0]}), .sel1 (int_or_diag_sel_c7)
              ) ;
dff_s   #(64)  ff_inval_data63to0_c8
              (.q   (ext_inval_data_c8[63:0]),
               .din (ext_inval_data_c7[63:0]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;



assign  csr_or_diag_sel_c7_111to64  = ( int_or_diag_sel_c7 | mux_csr_sel_c7) ;
assign  csr_or_diag_sel_c7_127to112 = (~int_or_diag_sel_c7 & mux_csr_sel_c7) ;

mux2ds #(48) int_diag_sel111to64
              (.dout (ext_inval_data_c7[111:64]),
               .in0  (dirdp_inval_pckt_c7[111:64]),  .sel0 (~csr_or_diag_sel_c7_111to64),
               .in1  (ext_inval_data_c7[47:0]),      .sel1 (csr_or_diag_sel_c7_111to64)
              ) ;
dff_s   #(48)  ff_inval_data111to64_c8
              (.q   (ext_inval_data_c8[111:64]),
               .din (ext_inval_data_c7[111:64]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;


assign  ext_retdp_data_c8[`CPX_WYVLD:`CPX_WY_LO] =  ret_way_c8 ;  // 133:131
assign  ext_retdp_data_c8[`CPX_BF_HI:`CPX_BF_LO] =  ret_buf_c8 ;  // 130:128
assign  ext_retdp_data_c8[127:0]                 = retdp_data_c8 ;

assign  ext_inval_data_c8[`CPX_WYVLD:`CPX_WY_LO] = inval_way_c8 ; // 133:131
assign  ext_inval_data_c8[`CPX_BF_HI:`CPX_BF_LO] = inval_buf_c8 ; // 130:128
//assign  ext_inval_data_c8[127:126] = 2'b0 ;
//assign  ext_inval_data_c8[125]     = cpx_rmo_c8 ;
//assign  ext_inval_data_c8[124:121] = cpx_hi_inval_c8 ;
//assign  ext_inval_data_c8[120:118] = cpuid_c8 ;
//assign  ext_inval_data_c8[117:112] = inval_index_c8 ;


mux2ds #(2)  int_diag_sel127to126
              (.dout (ext_inval_data_c7[127:126]),
               .in0  (2'b0),                       .sel0 (~csr_or_diag_sel_c7_127to112),
               .in1  (ext_inval_data_c7[63:62]),   .sel1 (csr_or_diag_sel_c7_127to112)
              ) ;
dff_s   #(2)   ff_inval_data127to126_c8
              (.q   (ext_inval_data_c8[127:126]),
               .din (ext_inval_data_c7[127:126]),
               .clk (rclk),
               .se  (se), .si (), .so ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// OQ ARRAY DATA IN
// Data needs to be flopped in  OQ ARRAY 
// Array is written in phase 2 of C6 .
////////////////////////////////////////////////////////////////////////////////
dff_s   #(1)   ff_sel_inval_c8
              (.q   (sel_inval_c8),
               .din (sel_inval_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


// this data will be delayed by 4 gates after the negative edge

assign  oq_array_data_in[`CPX_VLD]                = 1'b1 ;               // 144
assign  oq_array_data_in[`CPX_RQ_HI:`CPX_RQ_LO]   = oqctl_rqtyp_rtn_c8 ; // 143:140
assign  oq_array_data_in[`CPX_ERR_HI:`CPX_ERR_LO] = rtn_err_field_c8 ;   // 139:137
assign  oq_array_data_in[`CPX_NC]                 = nc_bit_c8 ;          // 136
assign  oq_array_data_in[`CPX_TH_HI:`CPX_TH_LO]   = tid_c8 ;             // 135:134




mux2ds #(`CPX_WIDTH-11) mux_oq_in_data_c8
  (	.dout (oq_array_data_in[`CPX_WIDTH-12:0]),   // 133:0
  	.in0  (ext_inval_data_c8[`CPX_WIDTH-12:0]), .sel0 (sel_inval_c8),
  	.in1  (ext_retdp_data_c8[`CPX_WIDTH-12:0]), .sel1 (~sel_inval_c8)
  ) ;


dff_s   #(`CPX_WIDTH)  ff_data_rtn_d1
              (.q   (staged_data_out_c9[`CPX_WIDTH-1:0]),
               .din (oq_array_data_in[`CPX_WIDTH-1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


mux2ds #(`CPX_WIDTH) mux_oqarray_dout
  (	.dout (eff_oqarray_dout[`CPX_WIDTH-1:0]),   // effective array data after data
						    // forwarding
  	.in0  (oq_array_data_out[`CPX_WIDTH-1:0]), .sel0 (~sel_array_out_l),
  	.in1  (staged_data_out_c9[`CPX_WIDTH-1:0]), .sel1 (sel_array_out_l)
  ) ;


dff_s   #(`CPX_WIDTH)  ff_eff_oqarray_dout_d1
              (.q   (eff_oqarray_dout_d1[`CPX_WIDTH-1:0]),
               .din (eff_oqarray_dout[`CPX_WIDTH-1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(`CPX_WIDTH)  ff_staged_cpx_packet_c9
              (.q   (staged_cpx_packet_c9[`CPX_WIDTH-1:0]),
               .din (oqdp_cpx_data_c8[`CPX_WIDTH-1:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


/////////////////////////////////////////////////////
// Change 6/13/2003:
// mux1  & mux2 selects are computed here.
// The c8 logic used to be in oqctl but now has been
// moved to oqdp.
/////////////////////////////////////////////////////

dff_s   #(3)   ff_out_mux1_sel_c8
              (.q   (out_mux1_sel_c8[2:0]),
               .din (out_mux1_sel_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign	mux1_sel_c8[0] = out_mux1_sel_c8[0] & ~rst_tri_en ;
assign	mux1_sel_c8[1] = out_mux1_sel_c8[1] & ~rst_tri_en ;
assign	mux1_sel_c8[2] = out_mux1_sel_c8[2] | rst_tri_en ;



mux3ds #(`CPX_WIDTH)  ff_tmp_cpx_data_ca
  (.dout (tmp_cpx_data_ca[`CPX_WIDTH-1:0]),
   .in0  (staged_data_out_c9[`CPX_WIDTH-1:0]),    .sel0 (mux1_sel_c8[2]), // def sel
   .in1  (eff_oqarray_dout_d1[`CPX_WIDTH-1:0]),  .sel1 (mux1_sel_c8[1]), // oq data
   .in2  (staged_cpx_packet_c9[`CPX_WIDTH-1:0]),  .sel2 (mux1_sel_c8[0])  // staged packet sel
  ) ;

dff_s   #(3)   ff_out_mux2_sel_c8
              (.q   (out_mux2_sel_c8[2:0]),
               .din (out_mux2_sel_c7[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign	mux2_sel_c8[0] = out_mux2_sel_c8[0] & ~rst_tri_en ;
assign	mux2_sel_c8[1] = out_mux2_sel_c8[1] & ~rst_tri_en ;
assign	mux2_sel_c8[2] = out_mux2_sel_c8[2] | rst_tri_en ;


mux3ds #(`CPX_WIDTH)  ff_cpx_data_ca
  (.dout (oqdp_cpx_data_c8[`CPX_WIDTH-1:0]), 
	.in0  (tmp_cpx_data_ca[`CPX_WIDTH-1:0]),
   .sel0 (mux2_sel_c8[0]), // Old data sel
   .in1  ({oq_array_data_in[`CPX_VLD:`CPX_TH_LO], ext_inval_data_c8[`CPX_WIDTH-12:0]}),
   .sel1 (mux2_sel_c8[1]), // Inval
   .in2  ({oq_array_data_in[`CPX_VLD:`CPX_TH_LO], ext_retdp_data_c8[`CPX_WIDTH-12:0]}),
   .sel2 (mux2_sel_c8[2])  // Def Sel
  ) ;


assign  sctag_cpx_data_ca = oqdp_cpx_data_c8 ;


endmodule
