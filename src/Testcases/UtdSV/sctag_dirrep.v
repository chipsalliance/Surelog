// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_dirrep.v
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
module sctag_dirrep(/*AUTOARG*/
   // Outputs
   dirrep_dir_wr_par_c4, dir_vld_c4_l, dc_rd_en_c4, dc_wr_en_c4, 
   inval_mask_dcd_c4, dc_rdwr_row_en_c4, dc_rdwr_panel_dec_c4, 
   dc_lkup_row_dec_c4, dc_lkup_panel_dec_c4, wr_dc_dir_entry_c4, 
   dc_dir_clear_c4, ic_rd_en_c4, ic_wr_en_c4, inval_mask_icd_c4, 
   ic_rdwr_row_en_c4, ic_rdwr_panel_dec_c4, ic_lkup_row_dec_c4, 
   ic_lkup_panel_dec_c4, wr_ic_dir_entry_c4, ic_dir_clear_c4, 
   lkup_addr8_c4, dir_error_c8, so, tagdp_lkup_addr11_c5, 
   // Inputs
   ic_parity_out, dc_parity_out, arbdp_dir_wr_par_c3, 
   arbctl_dir_vld_c3_l, arbctl_ic_rd_en_c3, arbctl_dc_rd_en_c3, 
   arbctl_ic_wr_en_c3, arbctl_dc_wr_en_c3, arbctl_dir_panel_dcd_c3, 
   arbctl_dir_panel_icd_c3, arbctl_lkup_bank_ena_dcd_c3, 
   arbctl_lkup_bank_ena_icd_c3, arbctl_inval_mask_dcd_c3, 
   arbctl_inval_mask_icd_c3, arbctl_wr_dc_dir_entry_c3, 
   arbctl_wr_ic_dir_entry_c3, lkup_row_addr_dcd_c3, 
   lkup_row_addr_icd_c3, oneshot_dir_clear_c3, tagdp_lkup_addr11_c4, 
   sehold, rclk, si, se
   );


output  	dirrep_dir_wr_par_c4;
output		dir_vld_c4_l;


// D$ directory	( Left Bottom )
output		dc_rd_en_c4, dc_wr_en_c4 ;
output [7:0]   	inval_mask_dcd_c4;
// Read and write addresses require a rd_en/wr_en qualification
output [3:0]	dc_rdwr_row_en_c4; // bits 4,3 of panel decode (i.e. address 10:9 )
output [3:0]	dc_rdwr_panel_dec_c4; // dec bits 1:0 of the panel address (i.e. address 5,4 );
// Lkup addresses do not require a qualification as the 
// _lkup_row_dec_c4 is actually a qualified vector.
output [3:0]	dc_lkup_row_dec_c4 ; 
output [3:0]   	dc_lkup_panel_dec_c4 ;// use lkup_row_addr_dcd[2:1] dec
output [5:0]   	wr_dc_dir_entry_c4 ; // lsb is arbctl_dir_panel_dcd[2] 
output	dc_dir_clear_c4; // Bottom left
					// ie bit 8 of the address.

// I$ directory	( Left TOp )
output		ic_rd_en_c4, ic_wr_en_c4 ;
output [7:0]	inval_mask_icd_c4;
// Read and write addresses require a rd_en/wr_en qualification
output [3:0]	ic_rdwr_row_en_c4; // bits 4,3 of panel decode (i.e. address 10:9 )
output [3:0]	ic_rdwr_panel_dec_c4; // dec bits 1:0 of the panel address (i.e. address 5,4 );
// Lkup addresses do not require a qualification as the 
// _lkup_row_dec_c4 is actually a qualified vector.
output [3:0]	ic_lkup_row_dec_c4 ; // use lkup_row_addr_dcd[2:1] dec
output [3:0]   	ic_lkup_panel_dec_c4 ;
output [5:0]   	wr_ic_dir_entry_c4 ; // lsb is arbctl_dir_panel_icd[2] 
					// ie bit 8 of the address.
output	ic_dir_clear_c4; // Top left

output		lkup_addr8_c4; // Left


output	dir_error_c8; // Right

output	so;

input	[3:0]	ic_parity_out; // LeftTop ( C7 signal.)
input	[3:0]	dc_parity_out; // LeftBottom ( C7 signal.)

// Use same pin positions as before.
input   	arbdp_dir_wr_par_c3;
input		arbctl_dir_vld_c3_l;
input		arbctl_ic_rd_en_c3, arbctl_dc_rd_en_c3;
input		arbctl_ic_wr_en_c3, arbctl_dc_wr_en_c3;
input [4:0]   	arbctl_dir_panel_dcd_c3, arbctl_dir_panel_icd_c3 ; 
input [3:0]   	arbctl_lkup_bank_ena_dcd_c3, arbctl_lkup_bank_ena_icd_c3 ; // translates to a row_en
input [7:0]   	arbctl_inval_mask_dcd_c3,arbctl_inval_mask_icd_c3;
input [4:0]   	arbctl_wr_dc_dir_entry_c3, arbctl_wr_ic_dir_entry_c3;
input [2:0]	lkup_row_addr_dcd_c3, lkup_row_addr_icd_c3 ; // translates to a panel enable.
							     // comes from tagdp

input		oneshot_dir_clear_c3;

input		tagdp_lkup_addr11_c4; // Added POST_4.2
input		sehold;	// Added POST_4.2
output		tagdp_lkup_addr11_c5; // Added POST_4.2

input		rclk;
input		si, se;

wire		dir_error_c7;
wire	[4:0]	dir_panel_dcd_c4, dir_panel_icd_c4 ;
wire	[2:0]	lkup_row_addr_dcd_c4, lkup_row_addr_icd_c4;

// ------\/ Addition for directory macrotest \/------------
dffe_s   #(1) ff_tagdp_lkup_addr11_c5
              (.q   (tagdp_lkup_addr11_c5),
               .din (tagdp_lkup_addr11_c4),
               .clk (rclk),
	       .en(~sehold),
               .se(se), .si  (), .so  ()
              ) ;

// ------\/ Addition for directory macrotest \/------------

assign	dir_error_c7 = (|(ic_parity_out)) | (|(dc_parity_out)) ;

dff_s   #(1) ff_dir_error_c8
              (.q   (dir_error_c8),
               .din (dir_error_c7),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1) ff_wr_par_c4
              (.q   (dirrep_dir_wr_par_c4),
               .din (arbdp_dir_wr_par_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1) ff_dir_vld_dcd_c4_l
              (.q   (dir_vld_c4_l),
               .din (arbctl_dir_vld_c3_l),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(1) ff_dc_rd_en_c4
              (.q   (dc_rd_en_c4),
               .din (arbctl_dc_rd_en_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1) ff_ic_rd_en_c4
              (.q   (ic_rd_en_c4),
               .din (arbctl_ic_rd_en_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1) ff_dc_wr_en_c4
              (.q   (dc_wr_en_c4),
               .din (arbctl_dc_wr_en_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(1) ff_ic_wr_en_c4
              (.q   (ic_wr_en_c4),
               .din (arbctl_ic_wr_en_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(8) ff_inval_mask_dcd_c4
              (.q   (inval_mask_dcd_c4[7:0]),
               .din (arbctl_inval_mask_dcd_c3[7:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

dff_s   #(8) ff_inval_mask_icd_c4
              (.q   (inval_mask_icd_c4[7:0]),
               .din (arbctl_inval_mask_icd_c3[7:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


///////////////////////////////////////////////////////////
// RD Write row and panel enables.
// Row is dtermined by the lower order bits of the 
// address.
// ie bits 5,4 for the I$
// ie bits 5,11 for the D$.
// Panel is determined by address bits 10,9
///////////////////////////////////////////////////////////

dff_s   #(4) ff_dir_panel_dcd_c4
              (.q   ({dir_panel_dcd_c4[4:3], dir_panel_dcd_c4[1:0]}),
               .din ({arbctl_dir_panel_dcd_c3[4:3],arbctl_dir_panel_dcd_c3[1:0]}),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

//assign	dc_rdwr_panel_dec_c4[0] = ( dir_panel_dcd_c4[4:3] == 2'd0 );
//assign	dc_rdwr_panel_dec_c4[1] = ( dir_panel_dcd_c4[4:3] == 2'd1 );
//assign	dc_rdwr_panel_dec_c4[2] = ( dir_panel_dcd_c4[4:3] == 2'd2 );
//assign	dc_rdwr_panel_dec_c4[3] = ( dir_panel_dcd_c4[4:3] == 2'd3 );

assign  dc_rdwr_panel_dec_c4[0] = ~dir_panel_dcd_c4[4] & ~dir_panel_dcd_c4[3] ;
assign  dc_rdwr_panel_dec_c4[1] = ~dir_panel_dcd_c4[4] & dir_panel_dcd_c4[3] ;
assign  dc_rdwr_panel_dec_c4[2] = dir_panel_dcd_c4[4] & ~dir_panel_dcd_c4[3] ;
assign  dc_rdwr_panel_dec_c4[3] = dir_panel_dcd_c4[4] & dir_panel_dcd_c4[3] ;

assign	dc_rdwr_row_en_c4[0] = (dir_panel_dcd_c4[1:0] == 2'd0 );
assign	dc_rdwr_row_en_c4[1] = (dir_panel_dcd_c4[1:0] == 2'd1 );
assign	dc_rdwr_row_en_c4[2] = (dir_panel_dcd_c4[1:0] == 2'd2 );
assign	dc_rdwr_row_en_c4[3] = (dir_panel_dcd_c4[1:0] == 2'd3 );

dff_s   #(4) ff_dir_panel_icd_c4
              (.q   ({dir_panel_icd_c4[4:3],dir_panel_icd_c4[1:0]}),
               .din ({arbctl_dir_panel_icd_c3[4:3],arbctl_dir_panel_icd_c3[1:0]}),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


assign	ic_rdwr_panel_dec_c4[0] = ( dir_panel_icd_c4[4:3] == 2'd0 );
assign	ic_rdwr_panel_dec_c4[1] = ( dir_panel_icd_c4[4:3] == 2'd1 );
assign	ic_rdwr_panel_dec_c4[2] = ( dir_panel_icd_c4[4:3] == 2'd2 );
assign	ic_rdwr_panel_dec_c4[3] = ( dir_panel_icd_c4[4:3] == 2'd3 );

assign	ic_rdwr_row_en_c4[0] = (dir_panel_icd_c4[1:0] == 2'd0 );
assign	ic_rdwr_row_en_c4[1] = (dir_panel_icd_c4[1:0] == 2'd1 );
assign	ic_rdwr_row_en_c4[2] = (dir_panel_icd_c4[1:0] == 2'd2 );
assign	ic_rdwr_row_en_c4[3] = (dir_panel_icd_c4[1:0] == 2'd3 );

///////////////////////////////////////////////////////////
// lkup  row and panel enables.
// Lkup row coming from tagdp corresponds to
// address bits <10:8> of the lkup address.
// The bits <10:9> actually go into determining
// the panel id within the directory. 
///////////////////////////////////////////////////////////

dff_s   #(3) ff_lkup_row_addr_dcd_c4
              (.q   (lkup_row_addr_dcd_c4[2:0]),
               .din (lkup_row_addr_dcd_c3[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;

assign	dc_lkup_panel_dec_c4[0] = ( lkup_row_addr_dcd_c4[2:1] == 2'd0 );
assign	dc_lkup_panel_dec_c4[1] = ( lkup_row_addr_dcd_c4[2:1] == 2'd1 );
assign	dc_lkup_panel_dec_c4[2] = ( lkup_row_addr_dcd_c4[2:1] == 2'd2 );
assign	dc_lkup_panel_dec_c4[3] = ( lkup_row_addr_dcd_c4[2:1] == 2'd3 );


dff_s   #(4) ff_lkup_bank_ena_dcd_c4
              (.q   (dc_lkup_row_dec_c4[3:0]),
               .din (arbctl_lkup_bank_ena_dcd_c3[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(3) ff_lkup_row_addr_icd_c4
              (.q   (lkup_row_addr_icd_c4[2:0]),
               .din (lkup_row_addr_icd_c3[2:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


assign	lkup_addr8_c4 = lkup_row_addr_icd_c4[0];

assign	ic_lkup_panel_dec_c4[0] = ( lkup_row_addr_icd_c4[2:1] == 2'd0 );
assign	ic_lkup_panel_dec_c4[1] = ( lkup_row_addr_icd_c4[2:1] == 2'd1 );
assign	ic_lkup_panel_dec_c4[2] = ( lkup_row_addr_icd_c4[2:1] == 2'd2 );
assign	ic_lkup_panel_dec_c4[3] = ( lkup_row_addr_icd_c4[2:1] == 2'd3 );

dff_s   #(4) ff_lkup_bank_ena_icd_c4
              (.q   (ic_lkup_row_dec_c4[3:0]),
               .din (arbctl_lkup_bank_ena_icd_c3[3:0]),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


///////////////////////////////////////////////////////////
// Wr or Rd entry.
// the LSB of the entry is address bit 2  of
// the panel id from arbctl.
// This translates to address<8> for both the I$ and D$.
///////////////////////////////////////////////////////////

dff_s   #(6) ff_wr_dc_dir_entry_c4
              (.q   (wr_dc_dir_entry_c4[5:0]),
               .din ({arbctl_wr_dc_dir_entry_c3[4:0],arbctl_dir_panel_dcd_c3[2]}),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(6) ff_wr_ic_dir_entry_c4
              (.q   (wr_ic_dir_entry_c4[5:0]),
               .din ({arbctl_wr_ic_dir_entry_c3[4:0],arbctl_dir_panel_icd_c3[2]}),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


///////////////////////////////////////////////////////////
// Dir clear bits.
///////////////////////////////////////////////////////////

dff_s   #(1) ff_ic_dir_clear_c4
              (.q   (ic_dir_clear_c4),
               .din (oneshot_dir_clear_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;


dff_s   #(1) ff_dc_dir_clear_c4
              (.q   (dc_dir_clear_c4),
               .din (oneshot_dir_clear_c3),
               .clk (rclk),
               .se(se), .si  (), .so  ()
              ) ;




endmodule
