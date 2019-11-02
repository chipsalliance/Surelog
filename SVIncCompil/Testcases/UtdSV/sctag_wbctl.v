// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_wbctl.v
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
module sctag_wbctl( /*AUTOARG*/
   // Outputs
   so, wbtag_write_wl_c4, wbtag_write_en_c4, wb_read_wl, wb_read_en, 
   sctag_scbuf_wbwr_wl_c6, sctag_scbuf_wbwr_wen_c6, 
   sctag_scbuf_wbrd_wl_r0, sctag_scbuf_wbrd_en_r0, 
   sctag_scbuf_ev_dword_r0, sctag_scbuf_evict_en_r0, 
   sctag_dram_wr_req, wbctl_hit_unqual_c2, wbctl_mbctl_dep_rdy_en, 
   wbctl_mbctl_dep_mbid, wbctl_arbctl_full_px1, rdmat_read_wl, 
   rdmat_read_en, wbctl_wr_addr_sel, wb_or_rdma_wr_req_en, 
   sctag_scbuf_rdma_rdwl_r0, sctag_scbuf_rdma_rden_r0, 
   reset_rdmat_vld, set_rdmat_acked, sctag_jbi_wib_dequeue, 
   // Inputs
   si, se, rclk, arst_l, grst_l, dbginit_l, rst_tri_en, 
   dirty_evict_c3, arbdp_inst_fb_c2, mbctl_wbctl_mbid_c4, 
   mbctl_hit_c4, mbctl_fbctl_dram_pick, l2_bypass_mode_on, 
   wb_cam_match_c2, c1_addr_eq_wb_c4, arbctl_wbctl_hit_off_c1, 
   arbctl_wbctl_inst_vld_c2, dram_sctag_wr_ack, rdmat_pick_vec, 
   or_rdmat_valid
   );


input		si, se;
output		so;
input           rclk;
input           arst_l;
input           grst_l;
input           dbginit_l;
input		rst_tri_en;

input           dirty_evict_c3;
// This indicates that the Tag of the instruction evicted
// (i.e. lru_tag_c3) needs to written into the WB tag array.

input           arbdp_inst_fb_c2;


input   [3:0]   mbctl_wbctl_mbid_c4;
input           mbctl_hit_c4;
input           mbctl_fbctl_dram_pick;


// from csr
input           l2_bypass_mode_on;


// from wbtag
input   [7:0]   wb_cam_match_c2;
output  [7:0]   wbtag_write_wl_c4;      // tag wr wl. Tag is written in C4 PH1
output          wbtag_write_en_c4;      // tag wren Tag is written in C4 PH1
output  [7:0]   wb_read_wl;
output          wb_read_en; // look at read pipeline


// from arbaddr
input		c1_addr_eq_wb_c4;

// from arbctl.
input           arbctl_wbctl_hit_off_c1; // hit qualifier.
input           arbctl_wbctl_inst_vld_c2;


input           dram_sctag_wr_ack;


output  [2:0]   sctag_scbuf_wbwr_wl_c6;  // must come out of a flop
output  [3:0]   sctag_scbuf_wbwr_wen_c6; // must come out of a flop. 3:0 are the same
output  [2:0]   sctag_scbuf_wbrd_wl_r0;
output          sctag_scbuf_wbrd_en_r0;
output  [2:0]   sctag_scbuf_ev_dword_r0;
output          sctag_scbuf_evict_en_r0;


output          sctag_dram_wr_req;


// to arbaddr

// to mbctl.
output          wbctl_hit_unqual_c2; // hit not qualified with instruction valid.
output          wbctl_mbctl_dep_rdy_en;
output  [3:0]   wbctl_mbctl_dep_mbid;


// to arbctl.
output          wbctl_arbctl_full_px1;
// Can accomodate two more instructions
// This signal should come out of a flop


output	[3:0]	rdmat_read_wl;
output		rdmat_read_en;

input	[3:0]	rdmat_pick_vec ; // from rdmatctl.
input		or_rdmat_valid ;

output          wbctl_wr_addr_sel;
output		wb_or_rdma_wr_req_en; // to evict_tag_dp

output  [1:0]   sctag_scbuf_rdma_rdwl_r0;
output          sctag_scbuf_rdma_rden_r0;

// rdmatctl
output	[3:0]	reset_rdmat_vld;
output	[3:0]	set_rdmat_acked;

// to jbi
output	sctag_jbi_wib_dequeue;
////////////////////////////////////////////////////////////////////////////////
wire            dram_sctag_wr_ack_d1;

wire    [7:0]   wb_valid_in;
wire    [7:0]   wb_valid;
wire            or_wb_valid;

wire    [2:0]   enc_write_wl_c5;
wire    [2:0]   enc_write_wl_c6;

wire    [7:0]   wb_cam_hit_vec_c2;
wire    [7:0]   wb_cam_hit_vec_c3;
wire    [7:0]   wb_cam_hit_vec_c4;
wire            wbctl_hit_unqual_c2;
wire            wbctl_hit_qual_c2;
wire            wbctl_hit_qual_c3;
wire            wbctl_hit_qual_c4;

wire    [7:0]   set_wb_valid;
wire    [7:0]   reset_wb_valid;

wire    [7:0]   set_wb_acked;
wire    [7:0]   wb_acked_in;
wire    [7:0]   wb_acked;

wire            mbid_wr_en;
wire    [7:0]   sel_insert_mbid_c4;
wire    [3:0]   mbid0;
wire    [3:0]   mbid1;
wire    [3:0]   mbid2;
wire    [3:0]   mbid3;
wire    [3:0]   mbid4;
wire    [3:0]   mbid5;
wire    [3:0]   mbid6;
wire    [3:0]   mbid7;

wire    [7:0]   wb_mbid_vld_in;
wire    [7:0]   wb_mbid_vld;
wire            or_wb_mbid_vld_in;
wire            or_wb_mbid_vld;

wire    [7:0]   sel_mbid;
wire            sel_default_mux1;
wire            sel_default_mux2;
wire            sel_default_mbentry;
wire    [3:0]   sel_mbid3t0;
wire    [3:0]   sel_mbid7t4;
wire    [3:0]   sel_mbid7t0;

wire            can_req_dram;
wire            enter_state0;
wire            leave_state0;
wire            enter_state1;
wire            leave_state1;
wire            enter_state2;
wire            leave_state2;
wire    [2:0]   next_state;
wire    [2:0]   state;
wire            dram_req_pending_in;
wire            dram_req_pending;
wire            inc_cycle_count;
wire    [3:0]   cycle_count_plus1;
wire    [3:0]   next_cycle_count;
wire    [3:0]   cycle_count_in;
wire    [3:0]   cycle_count;
wire            sctag_scbuf_evict_en_r0_d1;


wire            init_pick_state;
wire            sel_lshift_quad;
wire            sel_same_quad;
wire    [2:0]   lshift_quad_state;
wire    [2:0]   quad_state_in;
wire    [2:0]   quad_state;

wire            sel_lshift_quad0;
wire            sel_same_quad0;
wire    [3:0]   lshift_quad0_state;
wire    [3:0]   quad0_state_in;
wire    [3:0]   quad0_state;

wire            sel_lshift_quad1;
wire            sel_same_quad1;
wire    [3:0]   lshift_quad1_state;
wire    [3:0]   quad1_state_in;
wire    [3:0]   quad1_state;

wire            sel_lshift_quad2;
wire            sel_same_quad2;
wire    [3:0]   lshift_quad2_state;
wire    [3:0]   quad2_state_in;
wire    [3:0]   quad2_state;

wire    [3:0]   pick_quad0_sel;
wire    [3:0]   pick_quad1_sel;
wire    [3:0]   pick_quad2_sel;

wire    [2:0]   pick_quad_sel;

wire    [3:0]   pick_quad0_in;
wire    [3:0]   pick_quad1_in;
wire    [3:0]   pick_quad2_in;

wire    [2:0]   pick_quad_in;

wire    [7:0]   pick_wb_read_wl;
wire	[3:0]	pick_rdmat_read_wl ;
wire    [7:0]   latched_wb_read_wl;
wire	[3:0]	latched_rdmad_read_wl;
wire	latched_rdma_read_en, latched_wb_read_en ;

wire    [3:0]   wb_count;
wire    [3:0]   next_wb_count;
wire    [3:0]   wb_count_plus1;
wire    [3:0]   wb_count_minus1;
wire            inc_wb_count;
wire            dec_wb_count;
wire            same_wb_count;
wire            wb_count_5;
wire            wb_count_5_plus;
wire            wbctl_arbctl_full_px1_in;
wire	sctag_jbi_wib_dequeue_prev;

wire	[7:0]	wbtag_write_wl_c5;
wire	bypass_en_c1, bypass_en_c2;
wire	bypass_hit_en_c2;
wire	[7:0]	wb_cam_hit_vec_tmp_c2;
wire	wbtag_write_en_c3;

wire            dbb_rst_l;
wire	[7:0]	sel_mbid_rst;
///////////////////////////////////////////////////////////////////
 // Reset flop
 ///////////////////////////////////////////////////////////////////

 dffrl_async    #(1)    reset_flop      (.q(dbb_rst_l),
                                        .clk(rclk),
                                        .rst_l(arst_l),
                                        .din(grst_l),
                                        .se(se), .si(), .so());


////////////////////////////////////////////////////////////////////////////////


dff_s   #(1)   ff_arbctl_wbctl_inst_vld_c3
              (.q   (arbctl_wbctl_inst_vld_c3),
               .din (arbctl_wbctl_inst_vld_c2),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)   ff_arbdp_inst_fb_c3
              (.q   (arbdp_inst_fb_c3),
               .din (arbdp_inst_fb_c2),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)   ff_arbctl_wbctl_hit_off_c2
              (.q   (arbctl_wbctl_hit_off_c2),
               .din (arbctl_wbctl_hit_off_c1),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)   ff_dram_sctag_wr_ack_d1
              (.q   (dram_sctag_wr_ack_d1),
               .din (dram_sctag_wr_ack),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// eviction pipeline.
//------------------------------------------------------------------------------
//    C2      C3            C4              C5            C6              C7
//------------------------------------------------------------------------------
//    lru     dirty         xmit            rd data       rd_data       write
//    calc.   evict         lru way         array         array.        WB array
//                                                                      in PH2
//            xmit
//            lru way
//
//            		   wen and wl    write wtag       xmit
//            		   generation    array in         wl for write
//            		   for wbtag.    PH1              and wen.
//------------------------------------------------------------------------------
////////////////////////////////////////////////////////////////////////////////

assign  wbtag_write_wl_c4[0] = ~wb_valid[0] ;
assign  wbtag_write_wl_c4[1] = ~wb_valid[1] &  wb_valid[0] ;
assign  wbtag_write_wl_c4[2] = ~wb_valid[2] & (&(wb_valid[1:0])) ;
assign  wbtag_write_wl_c4[3] = ~wb_valid[3] & (&(wb_valid[2:0])) ;
assign  wbtag_write_wl_c4[4] = ~wb_valid[4] & (&(wb_valid[3:0])) ;
assign  wbtag_write_wl_c4[5] = ~wb_valid[5] & (&(wb_valid[4:0])) ;
assign  wbtag_write_wl_c4[6] = ~wb_valid[6] & (&(wb_valid[5:0])) ;
assign  wbtag_write_wl_c4[7] = ~wb_valid[7] & (&(wb_valid[6:0])) ;


dff_s   #(8)   ff_wbtag_write_wl_c5
              (.q   (wbtag_write_wl_c5[7:0]),
               .din (wbtag_write_wl_c4[7:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign  enc_write_wl_c5[0]   = (wbtag_write_wl_c5[1] | wbtag_write_wl_c5[3] |
                                wbtag_write_wl_c5[5] | wbtag_write_wl_c5[7]) ;
assign  enc_write_wl_c5[1]   = (wbtag_write_wl_c5[2] | wbtag_write_wl_c5[3] |
                                wbtag_write_wl_c5[6] | wbtag_write_wl_c5[7]) ;
assign  enc_write_wl_c5[2]   = (wbtag_write_wl_c5[4] | wbtag_write_wl_c5[5] |
                                wbtag_write_wl_c5[6] | wbtag_write_wl_c5[7]) ;

dff_s   #(3)   ff_enc_write_wl_c6
              (.q   (enc_write_wl_c6[2:0]),
               .din (enc_write_wl_c5[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


/////////////////////////////////////////////////////////////////////////////////
// A fill causes the WBB to be written in L2 $ off mode.
// Here is the pipeline for a Fill in OFF mode.
//
// 	C5		C6		C7		C8		C8
//
//	read FB		mux		xmit		data		write
//			with		in scdata	in scbuf	WB
//			$ data.
//
//	write		xmit				setup
//	wbtag		wl and wen			wb write
//	in PH1		from sctag				en and wl
//
/////////////////////////////////////////////////////////////////////////////////

dff_s   #(1)   ff_l2_bypass_mode_on_d1
              (.q   (l2_bypass_mode_on_d1),
               .din (l2_bypass_mode_on),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign  wbtag_write_en_c3    =  dirty_evict_c3 |
                               (l2_bypass_mode_on_d1 & arbdp_inst_fb_c3 &
                                arbctl_wbctl_inst_vld_c3) ;

dff_s   #(1)   ff_wbtag_write_en_c4
              (.q   (wbtag_write_en_c4),
               .din (wbtag_write_en_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dff_s   #(1)   ff_wbtag_write_we_c5
              (.q   (wbtag_write_we_c5),
               .din (wbtag_write_en_c4),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dff_s   #(1)   ff_wbtag_write_we_c6
              (.q   (wbtag_write_we_c6),
               .din (wbtag_write_we_c5),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

/////////////////////////////////////////////////////////////////////////////////
// An eviction causes the WBB to be written in L2 $ ON mode.
//
// 	C5		C6		C7			C8		C9
//
//	read $		read $ cyc2	xmit data 		xmit		write
//					inside scdata		to scbuf	data into wbb
//			
//			
//
//	write		xmit wl					setup
//	wbtag		to wbdata 				wb write
//	in PH1							en and wl
//
//
// IN OFF mode, the wl and wen are transmitted to scbuf in the C6 cycle of 
// a Fill operation.
// A fill is indicated by arbdp_inst_fb_c3 & arbctl_wbctl_inst_vld_c3
/////////////////////////////////////////////////////////////////////////////////

assign  sctag_scbuf_wbwr_wl_c6[2:0]  = enc_write_wl_c6[2:0] ;
assign  sctag_scbuf_wbwr_wen_c6[3:0] = {4{wbtag_write_we_c6}} ;



////////////////////////////////////////////////////////////////////////////////
// VALID bit
// Set on insertion.
// Reset on an eviction to DRAM.
////////////////////////////////////////////////////////////////////////////////



assign  reset_rdmat_vld = {4{leave_state2}} & latched_rdmad_read_wl ;
assign	set_rdmat_acked = {4{leave_state1}} & latched_rdmad_read_wl ;

assign  set_wb_valid   = {8{wbtag_write_we_c5}} & wbtag_write_wl_c5 ;
assign  reset_wb_valid = {8{leave_state2}} & latched_wb_read_wl ;
assign  wb_valid_in    = (wb_valid | set_wb_valid) & ~(reset_wb_valid) ;

dffrl_s #(8)   ff_wb_valid
              (.q   (wb_valid[7:0]),
               .din (wb_valid_in[7:0]),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;

assign  or_wb_valid = |(wb_valid[7:0]) ;


////////////////////////////////////////////////////////////////////////////////
// ACKED  bit
// Set when an entry is acked by the DRAM controller.
// Reset when the valid bit is reset i.e. on an eviction to DRAM.
////////////////////////////////////////////////////////////////////////////////

assign  set_wb_acked = ({8{leave_state1}} & latched_wb_read_wl) ;
assign  wb_acked_in  = (wb_acked | set_wb_acked) & ~reset_wb_valid ;

dffrl_s #(8)   ff_wb_acked
              (.q   (wb_acked[7:0]),
               .din (wb_acked_in[7:0]),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;




///////////////////////////////////////////////
// Updated on 11/10/2002
// bypassing of wb_write_data
// required for generation
// of wb hit.
// evicted tag is written into the WBB in C5.
// The operation in C2 in that cycle will have
// to see the effect of the wb write. Hence the
// C4 address being written into the tag is compared
// with the address of the instruction in C1.
//////////////////////////////////////////////

assign	bypass_en_c1 = c1_addr_eq_wb_c4 & wbtag_write_en_c4;

dff_s   #(1)   ff_bypass_en_c2
              (.q   (bypass_en_c2),
               .din (bypass_en_c1),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign	bypass_hit_en_c2 = ( bypass_en_c2  & ~arbctl_wbctl_hit_off_c2 ) ;

assign  wb_cam_hit_vec_tmp_c2   = ( (wb_cam_match_c2[7:0] & wb_valid[7:0]) &
                    ~(wb_acked[7:0] | {8{arbctl_wbctl_hit_off_c2}}) ) ;

assign  wbctl_hit_unqual_c2 = (|(wb_cam_hit_vec_tmp_c2[7:0])) | 
				bypass_hit_en_c2 ;

assign	wb_cam_hit_vec_c2 = ( wb_cam_hit_vec_tmp_c2 ) | 
			( {8{bypass_hit_en_c2}} & wbtag_write_wl_c5 ) ;


dff_s   #(8)   ff_wb_cam_hit_vec_c3
              (.q   (wb_cam_hit_vec_c3[7:0]),
               .din (wb_cam_hit_vec_c2[7:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dff_s   #(8)   ff_wb_cam_hit_vec_c4
              (.q   (wb_cam_hit_vec_c4[7:0]),
               .din (wb_cam_hit_vec_c3[7:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


assign  wbctl_hit_qual_c2 = wbctl_hit_unqual_c2 & arbctl_wbctl_inst_vld_c2 ;

dff_s   #(1)   ff_wbctl_hit_qual_c3
              (.q   (wbctl_hit_qual_c3),
               .din (wbctl_hit_qual_c2),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dff_s   #(1)   ff_wbctl_hit_qual_c4
              (.q   (wbctl_hit_qual_c4),
               .din (wbctl_hit_qual_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// MBID and MBID_vld.
// Written in the C4 cycle of a non-dependent instruction that hits
// the Writeback buffer.
//
// When an ack is received from DRAM for the entry with mbid_vld,
// the corresponding mbid is used to wake up the miss buffer entry
// that depends on the write.The ack may be received when the instruction
// is in flight i.e in C2, C3 otr C4 and yet to set mbid vld. But that is
// okay since the "acked" bit can only be set for one entry in the WBB at
// a time.
// MBID_vld is reset when an entry has mbid_vld =1 and acked=1
//
////////////////////////////////////////////////////////////////////////////////
assign  mbid_wr_en         = wbctl_hit_qual_c4 & ~mbctl_hit_c4;
assign  sel_insert_mbid_c4 = {8{mbid_wr_en}} & wb_cam_hit_vec_c4[7:0] ;

dffe_s  #(4)   ff_mbid0
              (.q   (mbid0[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid1
              (.q   (mbid1[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[1]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid2
              (.q   (mbid2[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[2]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid3
              (.q   (mbid3[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[3]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid4
              (.q   (mbid4[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[4]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid5
              (.q   (mbid5[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[5]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid6
              (.q   (mbid6[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[6]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;
dffe_s  #(4)   ff_mbid7
              (.q   (mbid7[3:0]),
               .din (mbctl_wbctl_mbid_c4[3:0]),
               .en  (sel_insert_mbid_c4[7]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


assign  wb_mbid_vld_in[7:0] = (wb_mbid_vld[7:0] | sel_insert_mbid_c4[7:0]) &
                              ~(sel_mbid[7:0]) ;

dffrl_s #(8)   ff_wb_mbid_vld
              (.q   (wb_mbid_vld[7:0]),
               .din (wb_mbid_vld_in[7:0]),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;

assign  or_wb_mbid_vld_in = |(wb_mbid_vld_in[7:0]) ;

dffrl_s #(1)   ff_or_wb_mbid_vld
              (.q   (or_wb_mbid_vld),
               .din (or_wb_mbid_vld_in),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
assign  sel_mbid[7:0]       = wb_acked[7:0] & wb_mbid_vld[7:0] ;
assign  sel_default_mux1    = ~(sel_mbid[0] | sel_mbid[1] | sel_mbid[2]) ;
assign  sel_default_mux2    = ~(sel_mbid[4] | sel_mbid[5] | sel_mbid[6]) ;
assign  sel_default_mbentry = |(sel_mbid[3:0]) ;

assign	sel_mbid_rst[0] = sel_mbid[0] & ~rst_tri_en ;
assign	sel_mbid_rst[1] = sel_mbid[1] & ~rst_tri_en ;
assign	sel_mbid_rst[2] = sel_mbid[2] & ~rst_tri_en ;
assign	sel_mbid_rst[3] = sel_default_mux1 |  rst_tri_en ;
assign	sel_mbid_rst[4] = sel_mbid[4] & ~rst_tri_en ;
assign	sel_mbid_rst[5] = sel_mbid[5] & ~rst_tri_en ;
assign	sel_mbid_rst[6] = sel_mbid[6] & ~rst_tri_en ;
assign	sel_mbid_rst[7] = sel_default_mux2 | rst_tri_en ;


mux4ds #(4)  mux_sel_mbid3t0
              (.dout (sel_mbid3t0[3:0]),
               .in0  (mbid0[3:0]),  .sel0 (sel_mbid_rst[0]),
               .in1  (mbid1[3:0]),  .sel1 (sel_mbid_rst[1]),
               .in2  (mbid2[3:0]),  .sel2 (sel_mbid_rst[2]),
               .in3  (mbid3[3:0]),  .sel3 (sel_mbid_rst[3])
              ) ;
mux4ds #(4)  mux_sel_mbid7t4
              (.dout (sel_mbid7t4[3:0]),
               .in0  (mbid4[3:0]),  .sel0 (sel_mbid_rst[4]),
               .in1  (mbid5[3:0]),  .sel1 (sel_mbid_rst[5]),
               .in2  (mbid6[3:0]),  .sel2 (sel_mbid_rst[6]),
               .in3  (mbid7[3:0]),  .sel3 (sel_mbid_rst[7])
              ) ;
mux2ds #(4)  mux_sel_mbid7t0
              (.dout (sel_mbid7t0[3:0]),
               .in0  (sel_mbid3t0[3:0]),  .sel0 (sel_default_mbentry),
               .in1  (sel_mbid7t4[3:0]),  .sel1 (~sel_default_mbentry)
              ) ;

assign  wbctl_mbctl_dep_rdy_en = |(sel_mbid[7:0]) ;
assign  wbctl_mbctl_dep_mbid   = sel_mbid7t0[3:0] ;


////////////////////////////////////////////////////////////////////////////////
// A Write request is generated only if a READ request is not being
// sent to DRAM in the same cycle. Here is the pipeline for making
// a write request to DRAM.
//------------------------------------------------------------------------------
//      #1                      #2                 #3
//------------------------------------------------------------------------------
//   if (atleast 1          rd wbtag           xmit req,addr
//   dram_req                                  to
//   AND                                       DRAM
//   not dram_pick
//   in mbctl.
//   AND
//   not wrreq              wbctl_wr_addr_sel
//   pending to DRAM)       xmitted to
//                          arbaddr.
//   generate RD
//   pointer
//
//   set wrreq
//   pending
//
//   xmit read en
//   and rd wl to wbtag.
//------------------------------------------------------------------------------
//#n-1        #n(r0)          #n+1(r1)                #n+2(r2)        #n+2(r3)
//------------------------------------------------------------------------------
//          ack from dram   rd_en                   rd wbdata       mux data
//                          rd_wl                   in PH1          in evict
//                          to scbuf.wbdata
//------------------------------------------------------------------------------
//    r4                   r5              r6      ......          r12
//------------------------------------------------------------------------------
//   perform ecc         xmit data1      dat2                    data8
//                       to dram         to dram                 to dram
//
//                                                               reset
//                                                               wrreq
//                                                               pending
//
//                                                               reset vld
//
//                                                               dec wb counter
////////////////////////////////////////////////////////////////////////////////

assign  can_req_dram  = ( or_wb_valid | or_rdmat_valid ) 
		& ~dram_req_pending & ~mbctl_fbctl_dram_pick ;

assign  enter_state0  = ~dbb_rst_l | leave_state2 ;
assign  leave_state0  = state[0] & can_req_dram ;
assign  next_state[0] = (state[0] | enter_state0) & ~leave_state0 ;

assign  enter_state1  = leave_state0 ;
assign  leave_state1  = state[1] & dram_sctag_wr_ack_d1 ;
assign  next_state[1] = (state[1] | enter_state1) & ~leave_state1 & dbb_rst_l ;

assign  enter_state2  = leave_state1 ;
assign  leave_state2  = state[2] & (cycle_count[3:0] == 4'd12) ;
assign  next_state[2] = (state[2] | enter_state2) & ~leave_state2 & dbb_rst_l ;

dff_s   #(3)   ff_state
              (.q   (state[2:0]),
               .din (next_state[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;




assign  dram_req_pending_in = (dram_req_pending | leave_state0) & ~leave_state2 ;

dffrl_s #(1)   ff_dram_req_pending
              (.q   (dram_req_pending),
               .din (dram_req_pending_in),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;




assign  inc_cycle_count   = (enter_state2 | state[2]) ;
assign  cycle_count_plus1 = cycle_count + 4'b1 ;
assign  next_cycle_count  = cycle_count_plus1 & ~{4{leave_state2}} ;

mux2ds #(4)  mux_cycle_count_in
              (.dout (cycle_count_in[3:0]),
               .in0  (cycle_count[3:0]),        .sel0 (~inc_cycle_count),
               .in1  (next_cycle_count[3:0]),   .sel1 (inc_cycle_count)
              ) ;
dffrl_s #(4)   ff_cycle_count
              (.q   (cycle_count[3:0]),
               .din (cycle_count_in[3:0]),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;

assign  wb_read_en = leave_state0  & ~pick_quad_sel[2] ;
assign  wb_read_wl = pick_wb_read_wl ;

assign	rdmat_read_en = leave_state0 & pick_quad_sel[2] ;
assign	rdmat_read_wl = pick_rdmat_read_wl;

dffe_s  #(8)   ff_latched_wb_read_wl
              (.q   (latched_wb_read_wl[7:0]),
               .din (pick_wb_read_wl[7:0]),
               .en  (leave_state0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dffe_s  #(1)   ff_latched_wb_read_en
              (.q   (latched_wb_read_en),
               .din (wb_read_en),
               .en  (leave_state0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dffe_s  #(4)   ff_latched_rdmad_read_wl
              (.q   (latched_rdmad_read_wl[3:0]),
               .din (pick_rdmat_read_wl[3:0]),
               .en  (leave_state0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dffe_s  #(1)   ff_latched_rdma_read_en
              (.q   (latched_rdma_read_en),
               .din (rdmat_read_en),
               .en  (leave_state0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

// the following signal  indicates that the WBB buffer address
// needs to be selected over the rdmat address.
dff_s   #(1)   ff_wbctl_wr_addr_sel
              (.q   (wbctl_wr_addr_sel),
               .din (wb_read_en),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

// the following signal goes to evict_tag_dp to enable the 
// address flop that transmits the address to 
// DRAM

dff_s   #(1)   ff_wb_or_rdma_wr_req_en
              (.q   (wb_or_rdma_wr_req_en),
               .din (leave_state0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


// the following signal  indicates that a write 
// request needs to be issued either from the
// wbb or the rdmat

dff_s   #(1)   ff_sctag_dram_wr_req
              (.q   (sctag_dram_wr_req),
               .din (wb_or_rdma_wr_req_en),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;




assign  sctag_scbuf_wbrd_wl_r0[0] = (latched_wb_read_wl[1] | latched_wb_read_wl[3] |
                                     latched_wb_read_wl[5] | latched_wb_read_wl[7]) ;
assign  sctag_scbuf_wbrd_wl_r0[1] = (latched_wb_read_wl[2] | latched_wb_read_wl[3] |
                                     latched_wb_read_wl[6] | latched_wb_read_wl[7]) ;
assign  sctag_scbuf_wbrd_wl_r0[2] = (latched_wb_read_wl[4] | latched_wb_read_wl[5] |
                                     latched_wb_read_wl[6] | latched_wb_read_wl[7]) ;

assign  sctag_scbuf_wbrd_en_r0    = (sctag_scbuf_evict_en_r0 & ~sctag_scbuf_evict_en_r0_d1) &
					latched_wb_read_en  ;



assign	sctag_scbuf_rdma_rdwl_r0[0] = (latched_rdmad_read_wl[1] | latched_rdmad_read_wl[3] );
assign	sctag_scbuf_rdma_rdwl_r0[1] = (latched_rdmad_read_wl[2] | latched_rdmad_read_wl[3] );

assign	sctag_scbuf_rdma_rden_r0 =  (sctag_scbuf_evict_en_r0 & ~sctag_scbuf_evict_en_r0_d1) &
                                        latched_rdma_read_en  ;


assign  sctag_scbuf_ev_dword_r0   = cycle_count[2:0] ;
assign  sctag_scbuf_evict_en_r0   = leave_state1 | (state[2] & (cycle_count < 4'd8)) ;

dff_s   #(1)   ff_sctag_scbuf_evict_en_r0_d1
              (.q   (sctag_scbuf_evict_en_r0_d1),
               .din (sctag_scbuf_evict_en_r0),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
// Dequeue of rdmad buffer needs to be sent to jbus.
////////////////////////////////////////////////////////////////////////////////
assign	sctag_jbi_wib_dequeue_prev = leave_state2 & 
					latched_rdma_read_en ;

dff_s   #(1)   ff_sctag_jbi_wib_dequeue
              (.q   (sctag_jbi_wib_dequeue),
               .din (sctag_jbi_wib_dequeue_prev),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////

mux2ds #(4)  mux_pick_quad0_in
              (.dout (pick_quad0_in[3:0]),
               .in0  (wb_valid[3:0]),     .sel0 (~or_wb_mbid_vld),
               .in1  (wb_mbid_vld[3:0]),  .sel1 (or_wb_mbid_vld)
              ) ;
mux2ds #(4)  mux_pick_quad1_in
              (.dout (pick_quad1_in[3:0]),
               .in0  (wb_valid[7:4]),     .sel0 (~or_wb_mbid_vld),
               .in1  (wb_mbid_vld[7:4]),  .sel1 (or_wb_mbid_vld)
              ) ;



assign	pick_quad2_in[3:0] = rdmat_pick_vec[3:0] ;


assign  pick_quad_in[0] = |(pick_quad0_in[3:0]) ;
assign  pick_quad_in[1] = |(pick_quad1_in[3:0]) ;
assign  pick_quad_in[2] = |(pick_quad2_in[3:0]) ;




assign  init_pick_state   = ~dbb_rst_l | ~dbginit_l ;


assign  sel_lshift_quad   = leave_state1 & ~init_pick_state ;
assign  sel_same_quad     = ~sel_lshift_quad & ~init_pick_state ;
assign  lshift_quad_state = {quad_state[1:0], quad_state[2]} ;

mux3ds #(3)  mux_quad_state_in
              (.dout (quad_state_in[2:0]),
               .in0  (3'b01),                   .sel0 (init_pick_state),
               .in1  (quad_state[2:0]),         .sel1 (sel_same_quad),
               .in2  (lshift_quad_state[2:0]),  .sel2 (sel_lshift_quad)
              ) ;
dff_s   #(3)   ff_quad_state
              (.q   (quad_state[2:0]),
               .din (quad_state_in[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



assign  sel_lshift_quad0   = leave_state1 & |(latched_wb_read_wl[3:0]) & ~init_pick_state ;
assign  sel_same_quad0     = ~sel_lshift_quad0 & ~init_pick_state ;
assign  lshift_quad0_state = {quad0_state[2:0], quad0_state[3]} ;

mux3ds #(4)  mux_quad0_state_in
              (.dout (quad0_state_in[3:0]),
               .in0  (4'b0001),                  .sel0 (init_pick_state),
               .in1  (quad0_state[3:0]),         .sel1 (sel_same_quad0),
               .in2  (lshift_quad0_state[3:0]),  .sel2 (sel_lshift_quad0)
              ) ;

dff_s   #(4)   ff_quad0_state
              (.q   (quad0_state[3:0]),
               .din (quad0_state_in[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;



assign  sel_lshift_quad1   = leave_state1 & |(latched_wb_read_wl[7:4]) & ~init_pick_state ;
assign  sel_same_quad1     = ~sel_lshift_quad1 & ~init_pick_state ;
assign  lshift_quad1_state = {quad1_state[2:0], quad1_state[3]} ;

mux3ds #(4)  mux_quad1_state_in
              (.dout (quad1_state_in[3:0]),
               .in0  (4'b0001),                  .sel0 (init_pick_state),
               .in1  (quad1_state[3:0]),         .sel1 (sel_same_quad1),
               .in2  (lshift_quad1_state[3:0]),  .sel2 (sel_lshift_quad1)
              ) ;

dff_s   #(4)   ff_quad1_state
              (.q   (quad1_state[3:0]),
               .din (quad1_state_in[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


assign  sel_lshift_quad2   = leave_state1 & |(latched_wb_read_wl[7:4]) & ~init_pick_state ;
assign  sel_same_quad2     = ~sel_lshift_quad2 & ~init_pick_state ;
assign  lshift_quad2_state = {quad2_state[2:0], quad2_state[3]} ;

mux3ds #(4)  mux_quad2_state_in
              (.dout (quad2_state_in[3:0]),
               .in0  (4'b0001),                  .sel0 (init_pick_state),
               .in1  (quad2_state[3:0]),         .sel1 (sel_same_quad2),
               .in2  (lshift_quad2_state[3:0]),  .sel2 (sel_lshift_quad2)
              ) ;

dff_s   #(4)   ff_quad2_state
              (.q   (quad2_state[3:0]),
               .din (quad2_state_in[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;




// QUAD0 bits.
assign  pick_quad0_sel[0] =  pick_quad0_in[0] &
                            (quad0_state[0] |
                            (quad0_state[1] & ~(pick_quad0_in[1] |
                                                pick_quad0_in[2] |
                                                pick_quad0_in[3])) |
                            (quad0_state[2] & ~(pick_quad0_in[2] |
                                                pick_quad0_in[3])) |
                            (quad0_state[3] & ~(pick_quad0_in[3])) ) ;
assign  pick_quad0_sel[1] =  pick_quad0_in[1] &
                            (quad0_state[1] |
                            (quad0_state[2] & ~(pick_quad0_in[2] |
                                                pick_quad0_in[3] |
                                                pick_quad0_in[0])) |
                            (quad0_state[3] & ~(pick_quad0_in[3] |
                                                pick_quad0_in[0])) |
                            (quad0_state[0] & ~(pick_quad0_in[0])) ) ;
assign  pick_quad0_sel[2] =  pick_quad0_in[2] &
                            (quad0_state[2] |
                            (quad0_state[3] & ~(pick_quad0_in[3] |
                                                pick_quad0_in[0] |
                                                pick_quad0_in[1])) |
                            (quad0_state[0] & ~(pick_quad0_in[0] |
                                                pick_quad0_in[1])) |
                            (quad0_state[1] & ~(pick_quad0_in[1])) ) ;
assign  pick_quad0_sel[3] =  pick_quad0_in[3] &
                            (quad0_state[3] |
                            (quad0_state[0] & ~(pick_quad0_in[0] |
                                                pick_quad0_in[1] |
                                                pick_quad0_in[2])) |
                            (quad0_state[1] & ~(pick_quad0_in[1] |
                                                pick_quad0_in[2])) |
                            (quad0_state[2] & ~(pick_quad0_in[2])) ) ;


// QUAD1 bits.
assign  pick_quad1_sel[0] =  pick_quad1_in[0] &
                            (quad1_state[0] |
                            (quad1_state[1] & ~(pick_quad1_in[1] |
                                                pick_quad1_in[2] |
                                                pick_quad1_in[3])) |
                            (quad1_state[2] & ~(pick_quad1_in[2] |
                                                pick_quad1_in[3])) |
                            (quad1_state[3] & ~(pick_quad1_in[3])) ) ;
assign  pick_quad1_sel[1] =  pick_quad1_in[1] &
                            (quad1_state[1] |
                            (quad1_state[2] & ~(pick_quad1_in[2] |
                                                pick_quad1_in[3] |
                                                pick_quad1_in[0])) |
                            (quad1_state[3] & ~(pick_quad1_in[3] |
                                                pick_quad1_in[0])) |
                            (quad1_state[0] & ~(pick_quad1_in[0])) ) ;
assign  pick_quad1_sel[2] =  pick_quad1_in[2] &
                            (quad1_state[2] |
                            (quad1_state[3] & ~(pick_quad1_in[3] |
                                                pick_quad1_in[0] |
                                                pick_quad1_in[1])) |
                            (quad1_state[0] & ~(pick_quad1_in[0] |
                                                pick_quad1_in[1])) |
                            (quad1_state[1] & ~(pick_quad1_in[1])) ) ;
assign  pick_quad1_sel[3] =  pick_quad1_in[3] &
                            (quad1_state[3] |
                            (quad1_state[0] & ~(pick_quad1_in[0] |
                                                pick_quad1_in[1] |
                                                pick_quad1_in[2])) |
                            (quad1_state[1] & ~(pick_quad1_in[1] |
                                                pick_quad1_in[2])) |
                            (quad1_state[2] & ~(pick_quad1_in[2])) ) ;


// QUAD1 bits.
assign  pick_quad2_sel[0] =  pick_quad2_in[0] &
                            (quad2_state[0] |
                            (quad2_state[1] & ~(pick_quad2_in[1] |
                                                pick_quad2_in[2] |
                                                pick_quad2_in[3])) |
                            (quad2_state[2] & ~(pick_quad2_in[2] |
                                                pick_quad2_in[3])) |
                            (quad2_state[3] & ~(pick_quad2_in[3])) ) ;
assign  pick_quad2_sel[1] =  pick_quad2_in[1] &
                            (quad2_state[1] |
                            (quad2_state[2] & ~(pick_quad2_in[2] |
                                                pick_quad2_in[3] |
                                                pick_quad2_in[0])) |
                            (quad2_state[3] & ~(pick_quad2_in[3] |
                                                pick_quad2_in[0])) |
                            (quad2_state[0] & ~(pick_quad2_in[0])) ) ;
assign  pick_quad2_sel[2] =  pick_quad2_in[2] &
                            (quad2_state[2] |
                            (quad2_state[3] & ~(pick_quad2_in[3] |
                                                pick_quad2_in[0] |
                                                pick_quad2_in[1])) |
                            (quad2_state[0] & ~(pick_quad2_in[0] |
                                                pick_quad2_in[1])) |
                            (quad2_state[1] & ~(pick_quad2_in[1])) ) ;
assign  pick_quad2_sel[3] =  pick_quad2_in[3] &
                            (quad2_state[3] |
                            (quad2_state[0] & ~(pick_quad2_in[0] |
                                                pick_quad2_in[1] |
                                                pick_quad2_in[2])) |
                            (quad2_state[1] & ~(pick_quad2_in[1] |
                                                pick_quad2_in[2])) |
                            (quad2_state[2] & ~(pick_quad2_in[2])) ) ;



// QUAD bits.

assign  pick_quad_sel[0] = pick_quad_in[0] &  ( quad_state[0] |
                        ( quad_state[1] & ~( pick_quad_in[1] | pick_quad_in[2] ) ) |
                        ( quad_state[2] & ~pick_quad_in[2] ) ) ;

assign  pick_quad_sel[1] = pick_quad_in[1] &  ( quad_state[1] |
                        ( quad_state[2] & ~( pick_quad_in[2] | pick_quad_in[0] ) ) |
                        ( quad_state[0] & ~pick_quad_in[0] ) ) ;

assign  pick_quad_sel[2] = pick_quad_in[2] &  ( quad_state[2] |
                        ( quad_state[0] & ~( pick_quad_in[0] | pick_quad_in[1] ) ) |
                        ( quad_state[1] & ~pick_quad_in[1] ) ) ;



assign  pick_wb_read_wl[3:0] = (pick_quad0_sel[3:0] & {4{pick_quad_sel[0]}}) ; 
assign  pick_wb_read_wl[7:4] = (pick_quad1_sel[3:0] & {4{pick_quad_sel[1]}}) ;

assign	pick_rdmat_read_wl[3:0]= (pick_quad2_sel[3:0] & {4{pick_quad_sel[2]}}) ;







////////////////////////////////////////////////////////////////////////////////

assign  inc_wb_count  =  wbtag_write_en_c4 & ~(leave_state2  & 
				latched_wb_read_en ) ;
assign  dec_wb_count  = ~wbtag_write_en_c4 &  
			( leave_state2 & latched_wb_read_en )  ;
assign  same_wb_count = ~(inc_wb_count | dec_wb_count) ;

assign  wb_count_plus1  = wb_count + 4'b1 ;
assign  wb_count_minus1 = wb_count - 4'b1 ;

mux3ds #(4)  mux_next_wb_count
              (.dout (next_wb_count[3:0]),
               .in0  (wb_count[3:0]),         .sel0 (same_wb_count),
               .in1  (wb_count_plus1[3:0]),   .sel1 (inc_wb_count),
               .in2  (wb_count_minus1[3:0]),  .sel2 (dec_wb_count)
              ) ;
dffrl_s #(4)   ff_wb_count
              (.q   (wb_count[3:0]),
               .din (next_wb_count[3:0]),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;

// synopsys translate_off
always  @(wb_count  ) begin
        if(  wb_count > 4'd8 )  begin
             // 0in <fire -message "FATAL ERROR: wb_counter overflow."
`ifdef DEFINE_0IN
`else
	`ifdef MODELSIM
        $display("WB_COUNT", "wb_counter overflow.");
	`else
        $error("WB_COUNT", "wb_counter overflow.");
	`endif		
`endif
        end
end
// synopsys translate_on


////////////////////////////////////////////////////////////////////////////
// wb_count is a c5 flop.
// The following condition is actually evaluated in C4 and flopped to C5
//
// When an eviction is in C4, the earliest following eviction can be
// in C1 and the one following that could be in  PX2 ( happens if the
// C1 instruction has stalled ). 
// Hence the px1 instruction will not be picked if the counter is 6 or greater.

////////////////////////////////////////////////////////////////////////////
assign  wb_count_5      = (wb_count[3:0] == 4'd5) ;
assign  wb_count_5_plus = (wb_count[3:0] >  4'd5) ;


assign  wbctl_arbctl_full_px1_in = wb_count_5_plus | (wb_count_5 & inc_wb_count) ;
dffrl_s #(1)   ff_wbctl_arbctl_full_px1
              (.q   (wbctl_arbctl_full_px1),
               .din (wbctl_arbctl_full_px1_in),
               .clk (rclk),  .rst_l(dbb_rst_l),
               .se(se), .si  (), .so  ()
              ) ;


////////////////////////////////////////////////////////////////////////////////
endmodule
