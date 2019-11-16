// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_ua_dp.v
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
module sctag_ua_dp
 (/*AUTOARG*/
   // Outputs
   so, vuad_array_wr_data_c4, vuad_dp_used_c2, vuad_dp_alloc_c2, 
   used_rd_parity_c2, alloc_rd_parity_c2, diag_rd_ua_out, 
   // Inputs
   rclk, si, se, lru_way_sel_c3, fill_way_c3, hit_wayvld_c3, 
   bistordiag_ua_data, vuad_evict_c3, wr64_inst_c3, vuad_sel_c2, 
   vuad_sel_c2orc3, vuad_sel_c4, vuad_sel_rd, vuad_sel_c2_d1, 
   bistordiag_wr_ua_c4, sel_ua_wr_data_byp, alloc_set_cond_c3, 
   alloc_rst_cond_c3, fbctl_vuad_bypassed_c3, vuad_array_rd_data_c1
   ) ;



input   rclk;


input	si, se;
output  so;


// 100+ pins on the right.
input	[11:0]	lru_way_sel_c3; // Right
input	[11:0]	fill_way_c3; // Right
input	[11:0]	hit_wayvld_c3; // Right
input	[25:0]	bistordiag_ua_data; // Right

// Right
input		vuad_evict_c3;	
input		wr64_inst_c3;

// Right
input           vuad_sel_c2;
input           vuad_sel_c2orc3;
input           vuad_sel_c4;
input           vuad_sel_rd;
input           vuad_sel_c2_d1;

input		bistordiag_wr_ua_c4;
input		sel_ua_wr_data_byp;
input		alloc_set_cond_c3;
input		alloc_rst_cond_c3;
input		fbctl_vuad_bypassed_c3;

// Bottom
input   [51:26] vuad_array_rd_data_c1 ; 

output	[51:26]	vuad_array_wr_data_c4;  // Bottom

output	[11:0]	vuad_dp_used_c2; // Top 
output	[11:0]	vuad_dp_alloc_c2; // Top 

output		used_rd_parity_c2; // Right
output		alloc_rd_parity_c2; // Right
output	[25:0]	diag_rd_ua_out ; // Right



wire	[11:0]	used_rd_byp_c2;
wire    [11:0]  used_rd_c2;
wire    [11:0]  used_byp_c1;
wire    [11:0]  used_byp_c3_in;
wire    [11:0]  used_c1;
wire    [11:0]  used_c2;
wire    [11:0]  used_c3;
wire    [11:0]  used_c4;
wire    [11:0]  used_wr_data_c5;
wire    [11:0]  used_wr_data_c6;


wire    [11:0]  alloc_rd_byp_c2;
wire    [11:0]  alloc_rd_c2;
wire    [11:0]  alloc_byp_c1;
wire	[11:0]	alloc_byp_c2_in;
wire    [11:0]  alloc_byp_c3_in;
wire    [11:0]  alloc_c1;
wire    [11:0]  alloc_c2;
wire    [11:0]  alloc_c3;
wire    [11:0]  alloc_c4;
wire    [11:0]  alloc_wr_data_c5;
wire    [11:0]  alloc_wr_data_c6;


wire	[1:0]	parity_rd_byp_c2, parity_rd_c2;
wire	[1:0]	parity_wr_c3,parity_wr_data_c4, parity_wr_data_c5, parity_wr_data_c6;

wire    [11:0]  used_byp_c2c3;
wire    [11:0]  used_byp_c4c5;
wire    [11:0]  alloc_byp_c2c3;
wire    [11:0]  alloc_byp_c4c5;




////////////////////////////////////////////////////////////////////////////////
// USED BIT ( Use leftmost 16 dp pitches for the used bit)
////////////////////////////////////////////////////////////////////////////////

// Row 17
mux2ds #(12)  mux_used_c1 // 2-1 mux flop
              (.dout (used_c1[11:0]),
               .in0  (vuad_array_rd_data_c1[50:39]),   .sel0 (vuad_sel_rd),
               .in1  (used_byp_c1[11:0]),  .sel1 (~vuad_sel_rd)
              ) ;

dff_s    #(12)   ff_used_c2
              (.q   (used_c2[11:0]), .din (used_c1[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
		) ;

// Row16
dff_s    #(13)   ff_used_rd_c2	// vuad rd data c2 flop
              (.q   ({parity_rd_byp_c2[1],used_rd_byp_c2[11:0]}), 
	       .din ({vuad_array_rd_data_c1[51],vuad_array_rd_data_c1[50:39]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 15
assign  vuad_dp_used_c2 = used_c2 ; // Top Drive using a 40X driver.

//Row14
mux2ds #(13)  mux_used_rd_c2	// rd data mux
              (.dout ({parity_rd_c2[1],used_rd_c2[11:0]}),
               .in0  ({parity_wr_data_c6[1],used_wr_data_c6[11:0]}),   
		.sel0 (sel_ua_wr_data_byp),
               .in1  ({parity_rd_byp_c2[1],used_rd_byp_c2[11:0]}),  
		.sel1 (~sel_ua_wr_data_byp)
              ) ;

//Row 13
// Combinational row. Use a 20x Buffer
assign	diag_rd_ua_out[25] = parity_rd_c2[1];
assign	diag_rd_ua_out[23:12] = used_rd_c2[11:0];

// Row 12
mux2ds #(12)  mux_used_byp_c2c3        // Bypass mux c2/c3 to c1
              (.dout (used_byp_c2c3[11:0]),
               .in0  (used_c2[11:0]),         .sel0 (vuad_sel_c2),
               .in1  (used_byp_c3_in[11:0]),  .sel1 (~vuad_sel_c2)
              ) ;


// final bypass mux can be here.

// ROw11
mux2ds #(12)  mux_used_byp_c1  // Bypass mux without the critical component
              (.dout (used_byp_c1[11:0]),
               .in0  (used_byp_c2c3[11:0]),  .sel0 (vuad_sel_c2orc3),
               .in1  (used_byp_c4c5[11:0]),  .sel1 (~vuad_sel_c2orc3)
              ) ;


//Row 10
zzpar16  parity_used_rd   ( .z(used_rd_parity_c2),
			.d({3'b0,parity_rd_c2[1],used_rd_c2[11:0]})
		);

// Row9
dff_s    #(12)   ff_used_c3
              (.q   (used_c3[11:0]), .din (used_c2[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row8
assign  used_byp_c3_in  = 
		 (used_c3 | fill_way_c3 | hit_wayvld_c3 ) & 
		~( ({12{vuad_evict_c3}} & lru_way_sel_c3) | 
		   ({12{wr64_inst_c3}} & hit_wayvld_c3) |
		   ({12{&(used_c3|alloc_c3)}}) // all ways are used or allocated.
		 ); 

// Row 7  (empty)

//Row6
zzpar16  parity_used_wr   ( .z(parity_wr_c3[1]), 
			.d({4'b0,used_byp_c3_in[11:0]})
		);

//Row5
dff_s    #(13)   ff_used_c4	// vuad C4 flop
              (.q   ({parity_wr_data_c4[1],used_c4[11:0]}), 
	       .din ({parity_wr_c3[1],used_byp_c3_in[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

//Row4
mux2ds #(13)  mux_wr_array_used_c4
              (.dout (vuad_array_wr_data_c4[51:39]),
               .in0  ({parity_wr_data_c4[1], used_c4[11:0]}),
			.sel0 (~bistordiag_wr_ua_c4),
               .in1  (bistordiag_ua_data[25:13]), 
			.sel1 (bistordiag_wr_ua_c4)
              ) ;

//Row3
mux2ds #(12)  mux_used_byp_c4c5        // Bypass mux c4/c5 to c1
              (.dout (used_byp_c4c5[11:0]),
               .in0  (used_c4[11:0]),         .sel0 (vuad_sel_c4),
               .in1  (used_wr_data_c5[11:0]), .sel1 (~vuad_sel_c4)
              ) ;

// Row 2
dff_s    #(13)   ff_used_wr_c5	// Vuad C5 flop
              (.q   ({parity_wr_data_c5[1],used_wr_data_c5[11:0]}), 
	       .din ({parity_wr_data_c4[1],used_c4[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 1
dff_s    #(13)   ff_used_wr_c6    // Vuad C6 flop
              (.q   ({parity_wr_data_c6[1],used_wr_data_c6[11:0]}),
               .din ({parity_wr_data_c5[1],used_wr_data_c5[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;




////////////////////////////////////////////////////////////////////////////////
// ALLOC bit ( use the right 16 dp pitches )
////////////////////////////////////////////////////////////////////////////////


// Row17
// Use a 2-1 mux flop here to reduce setup
//
mux2ds #(12)  mux_alloc_c1
              (.dout (alloc_c1[11:0]),
               .in0  (vuad_array_rd_data_c1[37:26]),   .sel0 (vuad_sel_rd),
               .in1  (alloc_byp_c1[11:0]),  .sel1 (~vuad_sel_rd)
              ) ;
dff_s    #(12)   ff_alloc_c2
              (.q   (alloc_c2[11:0]), .din (alloc_c1[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
                ) ;

// Row16
dff_s    #(13)   ff_alloc_rd_c2   // vuad rd data c2 flop
              (.q   ({parity_rd_byp_c2[0],alloc_rd_byp_c2[11:0]}),
               .din ({vuad_array_rd_data_c1[38],vuad_array_rd_data_c1[37:26]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 15
assign  vuad_dp_alloc_c2 = alloc_c2 ; // Top Drive using a 40X driver.


// Row14
mux2ds #(13)  mux_alloc_rd_c2   // rd data mux
              (.dout ({parity_rd_c2[0],alloc_rd_c2[11:0]}),
               .in0  ({parity_wr_data_c6[0],alloc_wr_data_c6[11:0]}),
                .sel0 (sel_ua_wr_data_byp),
               .in1  ({parity_rd_byp_c2[0],alloc_rd_byp_c2[11:0]}),
                .sel1 (~sel_ua_wr_data_byp)
              ) ;

// Row13
// Combinational row. Use a 20x Buffer
assign	diag_rd_ua_out[24] = parity_rd_c2[0];
assign	diag_rd_ua_out[11:0] = alloc_rd_c2[11:0];

// CHAnge: POST_3.4
// IN the following mux2, alloc_byp_c2 was replaced by
// alloc_byp_c2_in

// Row 12
mux2ds #(12)  mux_alloc_byp_c2c3        // Bypass mux c2/c3 to c1
              (.dout (alloc_byp_c2c3[11:0]),
               .in0  (alloc_byp_c2_in[11:0]),         .sel0 (vuad_sel_c2),
               .in1  (alloc_byp_c3_in[11:0]),  .sel1 (~vuad_sel_c2)
              ) ;


// final bypass mux can be here.

// ROw11
mux2ds #(12)  mux_alloc_byp_c1  // Bypass mux without the critical component
              (.dout (alloc_byp_c1[11:0]),
               .in0  (alloc_byp_c2c3[11:0]),  .sel0 (vuad_sel_c2orc3),
               .in1  (alloc_byp_c4c5[11:0]),  .sel1 (~vuad_sel_c2orc3)
              ) ;

//Row 10
zzpar16  parity_dir_rd   ( .z(alloc_rd_parity_c2),
                        .d({3'b0,parity_rd_c2[0],alloc_rd_c2[11:0]})
                );


// Row 9
// Use a 2-1 mux flop here to reduce setup and area
mux2ds #(12)  mux_alloc_byp_c2_in
              (.dout (alloc_byp_c2_in[11:0]),
               .in0  (alloc_c2[11:0]),         .sel0 (~vuad_sel_c2_d1),
               .in1  (alloc_byp_c3_in[11:0]),  .sel1 (vuad_sel_c2_d1)
              ) ;
dff_s   #(12)   ff_alloc_c3
              (.q   (alloc_c3[11:0]), .din (alloc_byp_c2_in[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row8
assign  alloc_byp_c3_in = (	alloc_c3 |
                 ({12{alloc_set_cond_c3}} & hit_wayvld_c3) |
		 ({12{vuad_evict_c3}} & lru_way_sel_c3) )  &
		~( ({12{alloc_rst_cond_c3}} & hit_wayvld_c3) | 
		   ({12{fbctl_vuad_bypassed_c3}} & fill_way_c3) 
		 ); 

//Row 7 is empty.

// Row6
zzpar16  parity_dir_wr   ( .z(parity_wr_c3[0]), 
			.d({4'b0,alloc_byp_c3_in[11:0]})
		);

// Row5
dff_s    #(13)   ff_alloc_c4      // vuad C4 flop
              (.q   ({parity_wr_data_c4[0],alloc_c4[11:0]}),
               .din ({parity_wr_c3[0],alloc_byp_c3_in[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row4
mux2ds #(13)  mux_wr_array_alloc_c4
              (.dout (vuad_array_wr_data_c4[38:26]),
               .in0  ({parity_wr_data_c4[0], alloc_c4[11:0]}),
			.sel0 (~bistordiag_wr_ua_c4),
               .in1  (bistordiag_ua_data[12:0]), 
			.sel1 (bistordiag_wr_ua_c4)
              ) ;


// Row3
mux2ds #(12)  mux_alloc_byp_c4c5        // Bypass mux c4/c5 to c1
              (.dout (alloc_byp_c4c5[11:0]),
               .in0  (alloc_c4[11:0]),         .sel0 (vuad_sel_c4),
               .in1  (alloc_wr_data_c5[11:0]), .sel1 (~vuad_sel_c4)
              ) ;

// Row 2
dff_s    #(13)   ff_alloc_wr_c5   // Vuad C5 flop
              (.q   ({parity_wr_data_c5[0],alloc_wr_data_c5[11:0]}),
               .din ({parity_wr_data_c4[0],alloc_c4[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;


// Row1
dff_s    #(13)   ff_alloc_wr_c6   // Vuad C6 flop
              (.q   ({parity_wr_data_c6[0],alloc_wr_data_c6[11:0]}),
               .din ({parity_wr_data_c5[0],alloc_wr_data_c5[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;




endmodule



