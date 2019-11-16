// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vuaddp_ctl.v
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
module sctag_vuaddp_ctl
 (/*AUTOARG*/
   // Outputs
   so, vuad_sel_c2, vuad_sel_c2_d1, vuad_sel_c2orc3, vuad_sel_c4, 
   vuad_sel_rd, vuad_tagdp_sel_c2_d1, st_to_data_array_c3, 
   wr64_inst_c3, vuad_evict_c3, alloc_set_cond_c3, alloc_rst_cond_c3, 
   vuad_error_c8, hit_wayvld_c3, fill_way_c3, lru_way_c3, 
   bistordiag_wr_vd_c4, bistordiag_wr_ua_c4, sel_ua_wr_data_byp, 
   sel_vd_wr_data_byp, sel_diag0_data_wr_c3, sel_diag1_data_wr_c3, 
   vuad_array_wr_en0_c4, vuad_array_wr_en1_c4, vuad_idx_c4, 
   // Inputs
   rclk, si, se, bist_vuad_idx_c3, vuad_idx_c3, bist_wr_vd_c3, 
   tagctl_hit_way_vld_c3, lru_way_sel_c3, tagctl_st_to_data_array_c3, 
   decdp_wr64_inst_c2, evict_c3, arbctl_acc_vd_c2, arbctl_acc_ua_c2, 
   sehold, idx_c1c2comp_c1, idx_c1c3comp_c1, idx_c1c4comp_c1, 
   idx_c1c5comp_c1, decdp_inst_int_c1, l2_bypass_mode_on, 
   arbctl_inst_diag_c1, bist_vuad_wr_en, arbctl_inst_vld_c2, 
   arbctl_inst_l2vuad_vld_c3, decdp_st_inst_c3, arbdp_inst_fb_c2, 
   parity_c4, arbdp_inst_way_c2, arbdp_vuadctl_pst_no_ctrue_c2, 
   decdp_cas1_inst_c2, arbdp_pst_with_ctrue_c2, decdp_cas2_inst_c2, 
   arbdp_inst_mb_c2, vuadctl_no_bypass_px2
   ) ;



input            rclk;

input	si, se;
output so;

input	[9:0]	bist_vuad_idx_c3 ; // NEW_PIN
input	[9:0]	vuad_idx_c3; // NEW_PIN
input		bist_wr_vd_c3 ; // NEW_PIN

input	[11:0]	tagctl_hit_way_vld_c3;	// Top
input	[11:0]	lru_way_sel_c3; // Top
input		tagctl_st_to_data_array_c3;	// Top
input		decdp_wr64_inst_c2;	// Top
input		evict_c3;	// Top

input		arbctl_acc_vd_c2;	// Top // diagnostic access only
input		arbctl_acc_ua_c2;	// Top // diagnostic access only

input		sehold ; // POST_4.2

// C1 outputs
input  idx_c1c2comp_c1 ; // from arbaddr Top
input  idx_c1c3comp_c1 ; // from arbaddr Top
input  idx_c1c4comp_c1 ; // from arbaddr Top
input  idx_c1c5comp_c1 ; // from arbaddr. POST_3.0 Top

input		decdp_inst_int_c1;	// Top
input		l2_bypass_mode_on;	// Top
input		arbctl_inst_diag_c1;	// Top
input		bist_vuad_wr_en;	// Top // This is a C3 signal.
input		arbctl_inst_vld_c2;	// Top
input		arbctl_inst_l2vuad_vld_c3; // Top
input		decdp_st_inst_c3; // Top
input		arbdp_inst_fb_c2; // Top

input	[3:0]	parity_c4; // Bottom
input	[3:0]	arbdp_inst_way_c2;

input		arbdp_vuadctl_pst_no_ctrue_c2; // Top
input		decdp_cas1_inst_c2; // Top
input		arbdp_pst_with_ctrue_c2; // Top
input		decdp_cas2_inst_c2; // Top
input		arbdp_inst_mb_c2; // Top

input		vuadctl_no_bypass_px2; // Top


output		vuad_sel_c2;	// Bottom
output		vuad_sel_c2_d1;	// Bottom
output		vuad_sel_c2orc3;	// Bottom
output		vuad_sel_c4;	// Bottom
output		vuad_sel_rd;	// Bottom
output		vuad_tagdp_sel_c2_d1;	// Top

output		st_to_data_array_c3;	// Bottom
output		wr64_inst_c3	; // Bottom
output		vuad_evict_c3   ; // Bottom


output		alloc_set_cond_c3; // Bottom
output		alloc_rst_cond_c3; // Bottom

output		vuad_error_c8; // Bottom

output	[11:0]	hit_wayvld_c3; // Bottom
output	[11:0]	fill_way_c3; // Bottom
output	[11:0]	lru_way_c3; // Bottom

output		bistordiag_wr_vd_c4   ; // Bottom // bist or diag access
output		bistordiag_wr_ua_c4   ; // Bottom // bist or diag access

output		sel_ua_wr_data_byp;	// Bottom
output		sel_vd_wr_data_byp;	// Bottom

output		sel_diag0_data_wr_c3; // Bottom  sel between diagnostic and bist data
output		sel_diag1_data_wr_c3; // Bottom  sel between diagnostic and bist data

output		vuad_array_wr_en0_c4; // Bottom // Change to C4
output		vuad_array_wr_en1_c4; // Bottom // Change to C4

output	[9:0]	vuad_idx_c4; // NEW PIN

wire 	vuad_array_wr_en0_c3, vuad_array_wr_en0_c5, vuad_array_wr_en0_c6;
wire	vuad_array_wr_en1_c3, vuad_array_wr_en1_c5, vuad_array_wr_en1_c6;
wire	vuad_sel_wr, vuad_sel_c4orc5;

wire	inst_vld_c3;
wire	inst_vld_c4;
wire	inst_vld_c5;

wire	arbctl_inst_diag_c2;
wire	arbctl_inst_diag_c3;
wire	arbctl_inst_diag_c4;

wire	l2_bypass_mode_on_d1;
wire	wr_disable_c3;
wire	vuad_error_c4, vuad_error_c5;
wire	vuad_error_c6, vuad_error_c7;



wire	alloc_set_cond_c2;
wire	alloc_rst_cond_c2;
wire	fill_inst_vld_c2;
wire	[3:0]	dec_lo_fill_way_c2;
wire	[3:0]	dec_hi_fill_way_c2;
wire	[11:0]	fill_way_c2;

wire	acc_vd_c3;
wire	acc_ua_c3;
wire	bistordiag_wr_vd_c3, bistordiag_wr_ua_c3 ;
wire	[9:0]	vuad_acc_idx_c3;
 wire	vuadctl_no_bypass_c1;

wire	inst_int_c2, inst_int_c3, inst_int_c4, inst_int_c5;


assign	st_to_data_array_c3 = tagctl_st_to_data_array_c3;
assign	lru_way_c3 = lru_way_sel_c3;
assign	hit_wayvld_c3 = tagctl_hit_way_vld_c3 ;


 dff_s     #(1)    ff_vuadctl_no_bypass_c1     (.din(vuadctl_no_bypass_px2), 
		 .clk(rclk),
                 .q(vuadctl_no_bypass_c1), .se(se), .si(), .so());

////////////////////////////////////////////////////////////////////////
 // index compares to for vuad mux selects.
 ////////////////////////////////////////////////////////////////////////

 assign vuad_sel_c2 = idx_c1c2comp_c1 & arbctl_inst_vld_c2  &
			~( decdp_inst_int_c1  | inst_int_c2  ) ;

 assign vuad_sel_c4 = idx_c1c4comp_c1 & inst_vld_c4 &
			~( decdp_inst_int_c1  | inst_int_c4)  ;

 assign vuad_sel_c2orc3 =  ( (( idx_c1c3comp_c1 & inst_vld_c3) &
				~( decdp_inst_int_c1  | inst_int_c3) ) |
                         	vuad_sel_c2 
				)  ;

 assign vuad_sel_wr = ( idx_c1c5comp_c1 & inst_vld_c5) &
			~( decdp_inst_int_c1  | inst_int_c5)   ;

 assign vuad_sel_c4orc5 = vuad_sel_c4 | vuad_sel_wr ;

/////// ----\/ Fix for macrotest \/---------
// sehold will cause the vuad_sel_rd signal
// to be high during macrotest and hence
// cause the array output to be flopped in C2
/////// ----\/ Fix for macrotest \/---------


 assign vuad_sel_rd = ~( vuad_sel_c2orc3 | vuad_sel_c4orc5 ) | 
			vuadctl_no_bypass_c1 |   // BIST or DECC read of VUAD
			sehold ; 


 dff_s     #(1)    ff_vuad_sel_c2_d1     (.din(vuad_sel_c2), .clk(rclk),
                 .q(vuad_sel_c2_d1), .se(se), .si(), .so());


 dff_s     #(1)    ff_vuad_sel_wr_d1     (.din(vuad_sel_wr), .clk(rclk),
                 .q(vuad_sel_wr_d1), .se(se), .si(), .so());


 dff_s     #(1)    ff_vuad_tagdp_sel_c2_d1     (.din(vuad_sel_c2), .clk(rclk),
                 .q(vuad_tagdp_sel_c2_d1), .se(se), .si(), .so());





assign	vuad_evict_c3	= evict_c3;


dff_s     #(1)    ff_inst_int_c2     	
		(.din(decdp_inst_int_c1), .clk(rclk),
               .q(inst_int_c2), .se(se), .si(), .so()
		);

dff_s     #(1)    ff_inst_int_c3     	
		(.din(inst_int_c2), .clk(rclk),
               .q(inst_int_c3), .se(se), .si(), .so()
		);

dff_s     #(1)    ff_wr64_inst_c3     	
		(.din(decdp_wr64_inst_c2), .clk(rclk),
               .q(wr64_inst_c3), .se(se), .si(), .so()
		);


dff_s   #(1)    ff_arbctl_acc_vd_c3
              (.q   (acc_vd_c3), .din (arbctl_acc_vd_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_arbctl_acc_ua_c3
              (.q   (acc_ua_c3), .din (arbctl_acc_ua_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;


dff_s   #(1)    ff_inst_vld_c3
              (.q   (inst_vld_c3), .din (arbctl_inst_vld_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_inst_vld_c4
              (.q   (inst_vld_c4), .din (inst_vld_c3),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_inst_vld_c5
              (.q   (inst_vld_c5), .din (inst_vld_c4),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;


dff_s   #(1)    ff_arbctl_inst_diag_c2
              (.q   (arbctl_inst_diag_c2), .din (arbctl_inst_diag_c1),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;
dff_s   #(1)    ff_arbctl_inst_diag_c3
              (.q   (arbctl_inst_diag_c3), .din (arbctl_inst_diag_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;
dff_s   #(1)    ff_arbctl_inst_diag_c4
              (.q   (arbctl_inst_diag_c4), .din (arbctl_inst_diag_c3),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

//dff   #(1)   ff_fbctl_vuad_bypassed_c3
              //(.q   (fbctl_vuad_bypassed_c3), .din (fbctl_vuad_bypassed_c2),
               //.clk (rclk), .se(se), .si  (), .so  ()
              //) ;

mux2ds  #(10) mux_idx_c3      (.dout (vuad_acc_idx_c3[9:0]) ,
                                .in0(bist_vuad_idx_c3[9:0] ), 
                                .in1(vuad_idx_c3[9:0]), 
                                .sel0(bist_vuad_wr_en),        
                                .sel1(~bist_vuad_wr_en)) ;

dff_s   #(10)   ff_mux_idx_c4
              (.q   (vuad_idx_c4[9:0]), .din (vuad_acc_idx_c3[9:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;




//////////////////////////////////////////////////////////////////////////////////////////
// Disable L2 VUAD writes if
// 1. Instruction is an INT.
// 2. L2 is OFF and the instruction is a non-diag instruction.
// 3. diag instruction is not a VUAD store.
//     (in implementation disable the write whenever there is Diag Inst and
//    enable it if the inst is a Diag write to the VUAD array.)
//////////////////////////////////////////////////////////////////////////////////////////


dff_s   #(1)    ff_l2_bypass_mode_on_d1
              (.q   (l2_bypass_mode_on_d1), .din (l2_bypass_mode_on),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

assign  wr_disable_c3  = inst_int_c3 |
                         (l2_bypass_mode_on_d1 & ~arbctl_inst_diag_c3) |
                          arbctl_inst_diag_c3 ;

//////////////////////////
// access  PV, PD, V, P
//////////////////////////
assign  sel_diag0_data_wr_c3 = arbctl_inst_l2vuad_vld_c3 & 
			decdp_st_inst_c3 &  acc_vd_c3 ; // sel diag over bist data

assign	bistordiag_wr_vd_c3 =  sel_diag0_data_wr_c3 | // diagorbist over normal data
				( bist_vuad_wr_en & bist_wr_vd_c3 ); 

dff_s   #(1)    ff_bistordiag_wr_vd_c4
              (.q   (bistordiag_wr_vd_c4), .din (bistordiag_wr_vd_c3),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

assign  vuad_array_wr_en1_c3 = (inst_vld_c3 & ~wr_disable_c3) |  // normal write
				bistordiag_wr_vd_c3; // bist or diag write
				

//////////////////////////
// access  PU, PA, U, A
//////////////////////////
assign  sel_diag1_data_wr_c3 = arbctl_inst_l2vuad_vld_c3 & 
			decdp_st_inst_c3 & acc_ua_c3 ; // sel diag over bist data

assign	bistordiag_wr_ua_c3 =  sel_diag1_data_wr_c3 | // diagorbist over normal data
				( bist_vuad_wr_en & ~bist_wr_vd_c3 );

dff_s   #(1)    ff_bistordiag_wr_ua_c4
              (.q   (bistordiag_wr_ua_c4), .din (bistordiag_wr_ua_c3),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

assign  vuad_array_wr_en0_c3 = ( inst_vld_c3 & ~wr_disable_c3) | // normal write
				bistordiag_wr_ua_c3 ; // bist or diag write


dff_s     #(1)    ff_vuad_array_wr_en0_c4     
			(.din(vuad_array_wr_en0_c3), .clk(rclk),
                 	.q(vuad_array_wr_en0_c4), .se(se), .si(), .so()
			);

dff_s     #(1)    ff_vuad_array_wr_en1_c4     
			(.din(vuad_array_wr_en1_c3), .clk(rclk),
                 	.q(vuad_array_wr_en1_c4), .se(se), .si(), .so()
			);

dff_s     #(1)    ff_vuad_array_wr_en0_c5     
			(.din(vuad_array_wr_en0_c4), .clk(rclk),
                 	.q(vuad_array_wr_en0_c5), .se(se), .si(), .so()
			);

dff_s     #(1)    ff_vuad_array_wr_en1_c5     
			(.din(vuad_array_wr_en1_c4), .clk(rclk),
                 	.q(vuad_array_wr_en1_c5), .se(se), .si(), .so()
			);

dff_s     #(1)    ff_vuad_array_wr_en0_c6     
			(.din(vuad_array_wr_en0_c5), .clk(rclk),
                 	.q(vuad_array_wr_en0_c6), .se(se), .si(), .so()
			);

dff_s     #(1)    ff_vuad_array_wr_en1_c6     
			(.din(vuad_array_wr_en1_c5), .clk(rclk),
                 	.q(vuad_array_wr_en1_c6), .se(se), .si(), .so()
			);

assign	sel_ua_wr_data_byp = vuad_sel_wr_d1 
				& vuad_array_wr_en1_c6 ;
assign	sel_vd_wr_data_byp = vuad_sel_wr_d1 
				& vuad_array_wr_en0_c6 ;




//* All errors are qualififed in the block that generates them

dff_s   #(1)    ff_inst_int_c4
              (.q   (inst_int_c4), .din (inst_int_c3),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_inst_int_c5
              (.q   (inst_int_c5), .din (inst_int_c4),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;


// Used bit error will not be reported as they are harmless.
// This is accomplished by tying parity_c4[1] to 0 in the 
// top level file.

assign	vuad_error_c4 = ~(arbctl_inst_diag_c4 | inst_int_c4) & 
			((|(parity_c4[3:2])) | (|(parity_c4[1:0])) ) &
                          inst_vld_c4;

dff_s   #(1)    ff_vuad_error_c5
              (.q   (vuad_error_c5), .din (vuad_error_c4),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_vuad_error_c6
              (.q   (vuad_error_c6), .din (vuad_error_c5),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_vuad_error_c7
              (.q   (vuad_error_c7), .din (vuad_error_c6),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)    ff_vuad_error_c8
              (.q   (vuad_error_c8), .din (vuad_error_c7),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

////////////////////////////////////////////////////////////////////////////////
// 4-12 decoder for the fill way
// Conditions for altering the VUAD bits.
////////////////////////////////////////////////////////////////////////////////
assign  fill_inst_vld_c2 = arbdp_inst_fb_c2 & arbctl_inst_vld_c2 ;



assign	dec_lo_fill_way_c2[0] = ( arbdp_inst_way_c2[1:0]==2'd0 ) 
					& fill_inst_vld_c2 ;
assign	dec_lo_fill_way_c2[1] = ( arbdp_inst_way_c2[1:0]==2'd1 ) 
					& fill_inst_vld_c2 ;
assign	dec_lo_fill_way_c2[2] = ( arbdp_inst_way_c2[1:0]==2'd2 ) 
					& fill_inst_vld_c2 ;
assign	dec_lo_fill_way_c2[3] = ( arbdp_inst_way_c2[1:0]==2'd3 ) 
					& fill_inst_vld_c2 ;


assign	dec_hi_fill_way_c2[0] = ( arbdp_inst_way_c2[3:2]==2'd0 ) ;

assign	dec_hi_fill_way_c2[1] = ( arbdp_inst_way_c2[3:2]==2'd1 ) ;

assign	dec_hi_fill_way_c2[2] = ( arbdp_inst_way_c2[3:2]==2'd2 ) ;

assign	dec_hi_fill_way_c2[3] = ( arbdp_inst_way_c2[3:2]==2'd3 ) ;


assign	fill_way_c2[0] = dec_hi_fill_way_c2[0] &
				dec_lo_fill_way_c2[0] ; // 0000

assign	fill_way_c2[1] = dec_hi_fill_way_c2[0] &
				dec_lo_fill_way_c2[1] ; // 0001

assign	fill_way_c2[2] = dec_hi_fill_way_c2[0] &
				dec_lo_fill_way_c2[2] ; // 0010

assign	fill_way_c2[3] = dec_hi_fill_way_c2[0] &
				dec_lo_fill_way_c2[3] ; // 0011

assign  fill_way_c2[4] = ( dec_hi_fill_way_c2[1] |
				dec_hi_fill_way_c2[3] )  &
                                dec_lo_fill_way_c2[0] ; // 0100 or 1100

assign  fill_way_c2[5] = ( dec_hi_fill_way_c2[1] |
				dec_hi_fill_way_c2[3] )  &
                                dec_lo_fill_way_c2[1] ; // 0101 or 1101

assign  fill_way_c2[6] = ( dec_hi_fill_way_c2[1] |
				dec_hi_fill_way_c2[3] )  &
                                dec_lo_fill_way_c2[2] ; // 0110 or 1110

assign  fill_way_c2[7] = ( dec_hi_fill_way_c2[1] |
				dec_hi_fill_way_c2[3] )  &
                                dec_lo_fill_way_c2[3] ; // 0111 or 1111


assign	fill_way_c2[8] = dec_hi_fill_way_c2[2] &
				dec_lo_fill_way_c2[0] ; // 1000

assign	fill_way_c2[9] = dec_hi_fill_way_c2[2] &
				dec_lo_fill_way_c2[1] ; // 1001

assign	fill_way_c2[10] = dec_hi_fill_way_c2[2] &
				dec_lo_fill_way_c2[2] ; // 1010

assign	fill_way_c2[11] = dec_hi_fill_way_c2[2] &
				dec_lo_fill_way_c2[3] ; // 1011


dff_s   #(12)   ff_fill_way_c3
              (.q   (fill_way_c3[11:0]), .din (fill_way_c2[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;




assign  alloc_set_cond_c2 = (arbdp_vuadctl_pst_no_ctrue_c2 | decdp_cas1_inst_c2) ;



assign  alloc_rst_cond_c2 = arbdp_pst_with_ctrue_c2 |
                            (decdp_cas2_inst_c2 & arbdp_inst_mb_c2) |
                            (arbdp_inst_mb_c2 & ~alloc_set_cond_c2) ;





dff_s   #(1)   ff_alloc_set_cond_c3
              (.q   (alloc_set_cond_c3), .din (alloc_set_cond_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1)   ff_alloc_rst_cond_c3
              (.q   (alloc_rst_cond_c3), .din (alloc_rst_cond_c2),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;



endmodule



