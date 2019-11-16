// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: sctag_vd_dp.v
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
module sctag_vd_dp
 (/*AUTOARG*/
   // Outputs
   so, vuad_array_wr_data_c4, dirty_evict_c3, vuad_dp_valid_c2, 
   valid_rd_parity_c2, dirty_rd_parity_c2, diag_rd_vd_out, 
   // Inputs
   rclk, si, se, lru_way_c3, fill_way_c3, hit_wayvld_c3, 
   bistordiag_vd_data, vuad_evict_c3, wr64_inst_c3, 
   st_to_data_array_c3, vuad_sel_c2, vuad_sel_c2orc3, vuad_sel_c4, 
   vuad_sel_rd, vuad_sel_c2_d1, bistordiag_wr_vd_c4, 
   sel_vd_wr_data_byp, vuad_array_rd_data_c1
   ) ;



input            rclk;


input	si, se;
output so;


// 100+ pins on the right.
input	[11:0]	lru_way_c3; // Left
input	[11:0]	fill_way_c3; // Left
input	[11:0]	hit_wayvld_c3; // Left
input	[25:0]	bistordiag_vd_data; // Left // This should be C4 data.

// Left
input		vuad_evict_c3;	
input		wr64_inst_c3;
input		st_to_data_array_c3;

input		vuad_sel_c2;
input		vuad_sel_c2orc3;
input		vuad_sel_c4; 
input		vuad_sel_rd;
input		vuad_sel_c2_d1;

input		bistordiag_wr_vd_c4;
input		sel_vd_wr_data_byp; // should be a C6-c2 bypass

// Bottom
input   [25:0]  vuad_array_rd_data_c1 ; 

output	[25:0]	vuad_array_wr_data_c4;  // Bottom

output		dirty_evict_c3; // TOP
output	[11:0]	vuad_dp_valid_c2; // Top 

output		valid_rd_parity_c2; // Left
output		dirty_rd_parity_c2; // Left 
output	[25:0]	diag_rd_vd_out ; // Left



wire	[11:0]	valid_rd_byp_c2;
wire    [11:0]  valid_rd_c2;
wire    [11:0]  valid_byp_c1;
wire    [11:0]  valid_byp_c3_in;
wire    [11:0]  valid_c1;
wire    [11:0]  valid_c2;
wire    [11:0]  valid_c3;
wire    [11:0]  valid_c4;
wire    [11:0]  valid_wr_data_c5;
wire    [11:0]  valid_wr_data_c6;


wire    [11:0]  dirty_byp_c2_in;
wire    [11:0]  dirty_rd_byp_c2;
wire    [11:0]  dirty_rd_c2;
wire    [11:0]  dirty_byp_c1;
wire    [11:0]  dirty_byp_c3_in;
wire    [11:0]  dirty_c1;
wire    [11:0]  dirty_c2;
wire    [11:0]  dirty_c3;
wire    [11:0]  dirty_c4;
wire    [11:0]  dirty_wr_data_c5;
wire    [11:0]  dirty_wr_data_c6;


wire	[3:2]	parity_rd_byp_c2, parity_rd_c2;

wire	[3:2]	parity_wr_c3,parity_wr_data_c4, parity_wr_data_c5, parity_wr_data_c6;

wire	[11:0]	valid_byp_c2c3;
wire	[11:0]	valid_byp_c4c5;
wire	[11:0]	dirty_byp_c2c3;
wire	[11:0]	dirty_byp_c4c5;



////////////////////////////////////////////////////////////////////////////////
// VALID BIT ( Use leftmost 16 dp pitches for the valid bit)
////////////////////////////////////////////////////////////////////////////////
// Row 17
mux2ds #(12)  mux_valid_c1 // 2-1 mux flop
              (.dout (valid_c1[11:0]),
               .in0  (vuad_array_rd_data_c1[24:13]),   .sel0 (vuad_sel_rd),
               .in1  (valid_byp_c1[11:0]),  .sel1 (~vuad_sel_rd)
              ) ;

dff_s    #(12)   ff_valid_c2
              (.q   (valid_c2[11:0]), .din (valid_c1[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
		) ;

// Row16
dff_s    #(13)   ff_valid_rd_c2	// vuad rd data c2 flop
              (.q   ({parity_rd_byp_c2[3],valid_rd_byp_c2[11:0]}), 
	       .din ({vuad_array_rd_data_c1[25],vuad_array_rd_data_c1[24:13]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 15
assign  vuad_dp_valid_c2 = valid_c2 ; // Top Drive using a 40X driver.

//Row14
mux2ds #(13)  mux_valid_rd_c2	// rd data mux
              (.dout ({parity_rd_c2[3],valid_rd_c2[11:0]}),
               .in0  ({parity_wr_data_c6[3],valid_wr_data_c6[11:0]}),   
		.sel0 (sel_vd_wr_data_byp),
               .in1  ({parity_rd_byp_c2[3],valid_rd_byp_c2[11:0]}),  
		.sel1 (~sel_vd_wr_data_byp)
              ) ;

//Row 13
// Combinational row. Use a 20x Buffer
assign	diag_rd_vd_out[25] = parity_rd_c2[3];
assign	diag_rd_vd_out[23:12] = valid_rd_c2[11:0];

// Row 12
mux2ds #(12)  mux_valid_byp_c2c3	// Bypass mux c2/c3 to c1
              (.dout (valid_byp_c2c3[11:0]),
               .in0  (valid_c2[11:0]),         .sel0 (vuad_sel_c2),
               .in1  (valid_byp_c3_in[11:0]),  .sel1 (~vuad_sel_c2)
              ) ;


// final bypass mux can be here.

// ROw11
mux2ds #(12)  mux_valid_byp_c1	// Bypass mux without the critical component
              (.dout (valid_byp_c1[11:0]),
               .in0  (valid_byp_c2c3[11:0]),  .sel0 (vuad_sel_c2orc3),
               .in1  (valid_byp_c4c5[11:0]),  .sel1 (~vuad_sel_c2orc3)
              ) ;

//Row 10
zzpar16  parity_vld_rd   ( .z(valid_rd_parity_c2),
			.d({3'b0,parity_rd_c2[3],valid_rd_c2[11:0]})
		);


// Row9
dff_s    #(12)   ff_valid_c3
              (.q   (valid_c3[11:0]), .din (valid_c2[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 8.5 is an empty row.
// Row8
assign  valid_byp_c3_in  = 
		 (valid_c3 | 
		fill_way_c3) & 
		~( ({12{vuad_evict_c3}} & lru_way_c3) | 
		   ({12{wr64_inst_c3}} & hit_wayvld_c3) 
		 ); 
//Row7 is empty
// assign  invalid_evict_c3 = vuad_evict_c3 & |(lru_way_c3 & ~valid_c3) ;

//Row6
zzpar16  parity_vld_wr   ( .z(parity_wr_c3[3]), 
			.d({4'b0,valid_byp_c3_in[11:0]})
		);


//Row5
dff_s    #(13)   ff_valid_c4	// vuad C4 flop
              (.q   ({parity_wr_data_c4[3],valid_c4[11:0]}), 
	       .din ({parity_wr_c3[3],valid_byp_c3_in[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

//Row4
mux2ds #(13)  mux_wr_array_valid_c4
              (.dout (vuad_array_wr_data_c4[25:13]),
               .in0  ({parity_wr_data_c4[3], valid_c4[11:0]}),
			.sel0 (~bistordiag_wr_vd_c4),
               .in1  (bistordiag_vd_data[25:13]), 
			.sel1 (bistordiag_wr_vd_c4)
              ) ;


// Row 3
mux2ds #(12)  mux_valid_byp_c4c5	// Bypass mux c4/c5 to c1
              (.dout (valid_byp_c4c5[11:0]),
               .in0  (valid_c4[11:0]),         .sel0 (vuad_sel_c4),
               .in1  (valid_wr_data_c5[11:0]), .sel1 (~vuad_sel_c4)
              ) ;


//Row2
dff_s    #(13)   ff_valid_wr_c5	// Vuad C5 flop
              (.q   ({parity_wr_data_c5[3],valid_wr_data_c5[11:0]}), 
	       .din ({parity_wr_data_c4[3],valid_c4[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;
//Row1
dff_s    #(13)   ff_valid_wr_c6	// Vuad C6 flop
              (.q   ({parity_wr_data_c6[3],valid_wr_data_c6[11:0]}), 
	       .din ({parity_wr_data_c5[3],valid_wr_data_c5[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;









////////////////////////////////////////////////////////////////////////////////
// DIRTY bit ( use the right 16 dp pitches )
////////////////////////////////////////////////////////////////////////////////


// Row 17
// Use a 2-1 mux flop here to reduce setup
mux2ds #(12)  mux_dirty_c1
              (.dout (dirty_c1[11:0]),
               .in0  (vuad_array_rd_data_c1[11:0]),   .sel0 (vuad_sel_rd),
               .in1  (dirty_byp_c1[11:0]),  .sel1 (~vuad_sel_rd)
              ) ;
dff_s    #(12)   ff_dirty_c2
              (.q   (dirty_c2[11:0]), .din (dirty_c1[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
                ) ;

// Row 16
dff_s    #(13)   ff_dirty_rd_c2   // vuad rd data c2 flop
              (.q   ({parity_rd_byp_c2[2],dirty_rd_byp_c2[11:0]}),
               .din ({vuad_array_rd_data_c1[12],vuad_array_rd_data_c1[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row 15 empty

// Row 14
mux2ds #(13)  mux_dirty_rd_c2   // rd data mux
              (.dout ({parity_rd_c2[2],dirty_rd_c2[11:0]}),
               .in0  ({parity_wr_data_c6[2],dirty_wr_data_c6[11:0]}),
                .sel0 (sel_vd_wr_data_byp),
               .in1  ({parity_rd_byp_c2[2],dirty_rd_byp_c2[11:0]}),
                .sel1 (~sel_vd_wr_data_byp)
              ) ;

// Row 13
// Combinational row. Use a 20x Buffer
assign	diag_rd_vd_out[24] = parity_rd_c2[2];
assign	diag_rd_vd_out[11:0] = dirty_rd_c2[11:0];


// Row 12
mux2ds #(12)  mux_dirty_byp_c2c3        // Bypass mux c2/c3 to c1
              (.dout (dirty_byp_c2c3[11:0]),
               .in0  (dirty_c2[11:0]),         .sel0 (vuad_sel_c2),
               .in1  (dirty_byp_c3_in[11:0]),  .sel1 (~vuad_sel_c2)
              ) ;


// final bypass mux can be here.

// ROw11
mux2ds #(12)  mux_dirty_byp_c1  // Bypass mux without the critical component
              (.dout (dirty_byp_c1[11:0]),
               .in0  (dirty_byp_c2c3[11:0]),  .sel0 (vuad_sel_c2orc3),
               .in1  (dirty_byp_c4c5[11:0]),  .sel1 (~vuad_sel_c2orc3)
              ) ;

// Row 10
zzpar16  parity_dir_rd   ( .z(dirty_rd_parity_c2),
                        .d({3'b0,parity_rd_c2[2],dirty_rd_c2[11:0]})
                );


// Row 9

// Use a 2-1 mux flop here to reduce setup and area
mux2ds #(12)  mux_dirty_byp_c2_in
              (.dout (dirty_byp_c2_in[11:0]),
               .in0  (dirty_c2[11:0]),         .sel0 (~vuad_sel_c2_d1),
               .in1  (dirty_byp_c3_in[11:0]),  .sel1 (vuad_sel_c2_d1)
              ) ;

dff_s   #(12)   ff_dirty_c3
              (.q   (dirty_c3[11:0]), .din (dirty_byp_c2_in[11:0]),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

// Row8
assign  dirty_byp_c3_in = (	dirty_c3 |
                 ({12{st_to_data_array_c3}} & hit_wayvld_c3) )  &
		~( ({12{vuad_evict_c3}} & lru_way_c3) | 
		   ({12{wr64_inst_c3}} & hit_wayvld_c3) 
		 ); 


// Row 7
assign  dirty_evict_c3  = vuad_evict_c3 & |(lru_way_c3 & dirty_c3) ;// Top


// Row 6
zzpar16  parity_dir_wr   ( .z(parity_wr_c3[2]), 
			.d({4'b0,dirty_byp_c3_in[11:0]})
		);


// Row 5
dff_s    #(13)   ff_dirty_c4      // vuad C4 flop
              (.q   ({parity_wr_data_c4[2],dirty_c4[11:0]}),
               .din ({parity_wr_c3[2],dirty_byp_c3_in[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;





// Row 4
mux2ds #(13)  mux_wr_array_dirty_c4
              (.dout (vuad_array_wr_data_c4[12:0]),
               .in0  ({parity_wr_data_c4[2], dirty_c4[11:0]}),
			.sel0 (~bistordiag_wr_vd_c4),
               .in1  (bistordiag_vd_data[12:0]), 
			.sel1 (bistordiag_wr_vd_c4)
              ) ;

// Row 3
mux2ds #(12)  mux_dirty_byp_c4c5        // Bypass mux c4/c5 to c1
              (.dout (dirty_byp_c4c5[11:0]),
               .in0  (dirty_c4[11:0]),         .sel0 (vuad_sel_c4),
               .in1  (dirty_wr_data_c5[11:0]), .sel1 (~vuad_sel_c4)
              ) ;

// Row 2
dff_s    #(13)   ff_dirty_wr_c5   // Vuad C5 flop
              (.q   ({parity_wr_data_c5[2],dirty_wr_data_c5[11:0]}),
               .din ({parity_wr_data_c4[2],dirty_c4[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;

//Row 1
dff_s    #(13)   ff_dirty_wr_c6   // Vuad C6 flop
              (.q   ({parity_wr_data_c6[2],dirty_wr_data_c6[11:0]}), 
               .din ({parity_wr_data_c5[2],dirty_wr_data_c5[11:0]}),
               .clk (rclk), .se(se), .si  (), .so  ()
              ) ;








endmodule



