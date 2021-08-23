/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

module wav_clock_inv  (
  input  wire clk_in,
  output wire clk_out
);

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//    assign clk_out = ~clk_in;
// `endif
//

wav_inv u_wav_inv (
  .i_a     ( clk_in      ),
  .o_z     ( clk_out     ));

endmodule

module wav_clock_mux (
	input  wire				clk0,
  input  wire				clk1,
  input  wire				sel,
  output wire				clk_out
);

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//    assign clk_out = sel ? clk1 : clk0;
// `endif

wav_mux u_wav_mux (
  .i_sel     ( sel      ),
  .i_a       ( clk0     ),
  .i_b       ( clk1     ),
  .o_z       ( clk_out  ));

endmodule

module wav_clock_buf (
  input  wire clk_in,
  output wire clk_out
);
`ifdef WAV_STDCELL_GF12LP
//    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
//       .I  (i_a),
//       .ZN (o_z)
//    );
   //cadence script_begin
   //set_db [get_db insts */u_inv[*]] .preserve true
   //cadence script_end
`else
   assign clk_out = clk_in;
`endif

endmodule

module wav_clock_gate (
  input  wire clk_in,
  input  wire en,
  input  wire test_en,
  output wire clk_out
);

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//    assign clk_out = test_en | en ? clk_in : 1'b0;
// `endif

wav_cgc_rl u_wav_cgc_rl (
  .i_cgc_en    ( test_en      ),
  .i_clk_en    ( en           ),
  .i_clk       ( clk_in       ),
  .o_clk       ( clk_out      ));
endmodule

module wav_clock_xor(
  input  wire  A1,
  input  wire  A2,
  output wire  Z
);
// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//    assign Z = A1 ^ A2;
// `endif

wav_xor #(
  //parameters
  .DWIDTH             ( 1         )
) u_wav_xor (
  .i_a     ( A1      ),  //input -   [DWIDTH-1:0]
  .i_b     ( A2      ),  //input -   [DWIDTH-1:0]
  .o_z     ( Z       )); //output -  [DWIDTH-1:0]

endmodule

//There was no CKOR I could find so made it with some NANDs
module wav_clock_or (
 input  wire  a1,
 input  wire  a2,
 output wire  z
);

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//    assign z = a1 | a2;
// `endif
//
// //   wire nand1_out;
// //   wire nand2_out;
// //
// //   generate
// //    if (STDCELL==1) begin : gen_7tbwp40phvt
// //      CKND2D8BWP7T40P140HVT clk_nand1 (.A1(a1), .A2(a1), .ZN(nand1_out));
// //      CKND2D8BWP7T40P140HVT clk_nand2 (.A1(a2), .A2(a2), .ZN(nand2_out));
// //      CKND2D8BWP7T40P140HVT clk_nand3 (.A1(nand1_out), .A2(nand2_out), .ZN(z));
// //
// //    end else if (STDCELL==2) begin : gen_9tbwp40psvt
// //      CKND2D8BWP40P140 clk_nand1 (.A1(a1), .A2(a1), .ZN(nand1_out));
// //      CKND2D8BWP40P140 clk_nand2 (.A1(a2), .A2(a2), .ZN(nand2_out));
// //      CKND2D8BWP40P140 clk_nand3 (.A1(nand1_out), .A2(nand2_out), .ZN(z));
// //    end
// //   endgenerate

wav_or u_wav_or (
  .i_a     ( a1      ),
  .i_b     ( a2      ),
  .o_z     ( z       ));

endmodule

module wav_clock_mux_sync (
  input  wire           reset0,
  input  wire           reset1,
  input  wire           sel,
  input  wire           clk0,
  input  wire           clk1,
  input  wire           core_scan_mode,
  input  wire           core_scan_clk,
  output wire           clk_out
);


wav_clk_mux_gf u_wav_clk_mux_gf (
  .i_clk_0     ( clk0           ),  //input -  1              
  .i_clk_1     ( clk1           ),  //input -  1              
  .i_clk_rst_0 ( reset0         ),  //input -  1              
  .i_clk_rst_1 ( reset1         ),  //input -  1              
  .i_sel       ( sel            ),  //input -  1              
  .i_test_en   ( core_scan_mode ),  //input -  1        
  .i_cgc_en    ( core_scan_mode ),      
  .o_sel_0     (                ),  //output - 1              
  .o_sel_1     (                ),  //output - 1              
  .o_clk       ( clk_out        )); //output - 1    

// // `ifdef WAV_STDCELL_GF12LP
// // //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// // //       .I  (i_a),
// // //       .ZN (o_z)
// // //    );
// //    //cadence script_begin
// //    //set_db [get_db insts */u_inv[*]] .preserve true
// //    //cadence script_end
// // `else
// //    assign clk_out = sel ? clk1 : clk0;  //real temp
// // `endif
// 
// wire clk0_inv;
// wire clk1_inv;
// wire sel_inv;
// wire sel0_in;
// wire sel1_in;
// wire clk0_out;
// wire clk1_out;
// wire clk_out_pre;
// 
// wire reset0_inv;
// wire reset1_inv;
// 
// wire clk0_dff1_qn;
// wire clk1_dff1_qn;
// wire sel_and_clk0_dff1_qn;
// wire sel_inv_and_clk1_dff1_qn;
// wire clk1_dff0_q;
// wire clk1_dff1_q;
// wire clk0_dff0_q;
// wire clk0_dff1_q;
// wire sel_and_clk1_dff1_qn;
// wire clk1_AND_clk1_dff1_q;
// wire clk0_and_clk0_dff1_q;
// wire sel_buf;
// 
// //Google glichless clock mux and look for EETimes article
// wav_clock_inv  u_clk0_inv (.clk_in(clk0), .clk_out(clk0_inv));
// wav_clock_mux  u_clk0_inv_mux(.clk0(clk0_inv), .clk1(core_scan_clk), .sel(core_scan_mode), .clk_out(clk0_inv_mux));
// 
// wav_clock_inv  u_clk1_inv (.clk_in(clk1), .clk_out(clk1_inv));
// wav_clock_mux  u_clk1_inv_mux(.clk0(clk1_inv), .clk1(core_scan_clk), .sel(core_scan_mode), .clk_out(clk1_inv_mux));
// 
// wav_clock_inv  u_reset0_inv(.clk_in(reset0), .clk_out(reset0_inv));
// wav_clock_inv  u_reset1_inv(.clk_in(reset1), .clk_out(reset1_inv));
// 
// //for case_analysis settings
// wav_clock_buf  u_sel_buf(.clk_in(sel), .clk_out(sel_buf));
// 
// wav_clock_inv  u_sel_inv(.clk_in(sel_buf), .clk_out(sel_inv));
// 
// wav_and u_sel_AND_clk0_dff1_qn     (.i_a(sel_buf),  .i_b(clk0_dff1_qn), .o_z(sel_and_clk0_dff1_qn));
// wav_and u_sel_inv_AND_clk1_dff1_qn (.i_a(sel_inv),  .i_b(clk1_dff1_qn), .o_z(sel_and_clk1_dff1_qn));
// 
// //CLK1
// wav_dff_r u_clk1_dff0 (.i_d(sel_and_clk0_dff1_qn), .i_clk(clk1),         .i_rst(reset1), .o_q(clk1_dff0_q));
// wav_dff_r u_clk1_dff1 (.i_d(clk1_dff0_q),          .i_clk(clk1_inv_mux), .i_rst(reset1), .o_q(clk1_dff1_q));
// wav_clock_inv  u_clk1_dff1_qn(.clk_in(clk1_dff1_q), .clk_out(clk1_dff1_qn));
// 
// //CLK0
// wav_dff_r u_clk0_dff0 (.i_d(sel_and_clk1_dff1_qn), .i_clk(clk0),         .i_rst(reset0), .o_q(clk0_dff0_q));
// wav_dff_r u_clk0_dff1 (.i_d(clk0_dff0_q),          .i_clk(clk0_inv_mux), .i_rst(reset0), .o_q(clk0_dff1_q));
// wav_clock_inv  u_clk0_dff1_qn(.clk_in(clk0_dff1_q), .clk_out(clk0_dff1_qn));
// 
// //clk1 AND
// //wav_and u_clk1_AND_clk1_dff1_q (.i_a(clk1),      .i_b(clk1_dff1_q), .o_z(clk1_and_clk1_dff1_q));
// wav_clock_gate u_wav_clock_gate1 (
//   .clk_in    ( clk1                 ),        
//   .en        ( clk1_dff1_q          ),        
//   .test_en   ( core_scan_mode       ),        
//   .clk_out   ( clk1_and_clk1_dff1_q )); 
// 
// //clk0 AND
// //wav_and u_clk0_AND_clk0_dff1_q (.i_a(clk0),      .i_b(clk0_dff1_q), .o_z(clk0_and_clk0_dff1_q));
// wav_clock_gate u_wav_clock_gate0 (
//   .clk_in    ( clk0                 ),        
//   .en        ( clk0_dff1_q          ),        
//   .test_en   ( core_scan_mode       ),        
//   .clk_out   ( clk0_and_clk0_dff1_q )); 
// 
// 
// //CLK_OUT XOR
// wav_clock_xor u_clk_out_pre_XOR(.A1(clk0_and_clk0_dff1_q), .A2(clk1_and_clk1_dff1_q), .Z(clk_out_pre));
// 
// //Final MUX (declare clock here)
// wav_clock_mux  u_wav_clock_mux(.clk0(clk_out_pre), .clk1(core_scan_clk), .sel(core_scan_mode), .clk_out(clk_out));

endmodule

// in stdcell_lib
// module wav_dff (
//   input  wire   clk,
//   input  wire   sig_in,
//   output wire   sig_out
// );
//
// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//     reg sig_reg;
//     always @(posedge clk) begin
//       sig_reg <= sig_in;
//     end
//     assign sig_out = sig_reg;
// `endif
//
// endmodule

module demet_reset (
   input  wire   clk,
   input  wire   reset,
   input  wire   sig_in,
   output wire   sig_out
);

wav_demet_reset u_wav_demet_reset (.clk(clk), .nreset(~reset), .sig_in(sig_in), .se(1'b0), .si(1'b0), .sig_out(sig_out));

endmodule

module wav_demet_reset (
   input  wire   clk,
   input  wire   nreset,
   input  wire   sig_in,
   input  wire   se,
   input  wire   si,
   output wire   sig_out
);

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//     reg ff1, ff2;
//     always @(posedge clk or negedge nreset) begin
//       if(~nreset) begin
//         ff1 <= 1'b0;
//         ff2 <= 1'b0;
//       end else begin
//         ff1 <= sig_in;
//         ff2 <= ff1;
//       end
//     end
//     assign sig_out = ff2;
// `endif

wav_demet_r u_wav_demet_r (
  .i_clk     ( clk      ),
  .i_rst     ( ~nreset  ),
  .i_d       ( sig_in   ),
  .o_q       ( sig_out  ));

endmodule

module demet_set (
   input  wire   clk,
   input  wire   set,
   input  wire   sig_in,
   output wire   sig_out
);

wav_demet_set u_wav_demet_set (.clk(clk), .nset(~set), .sig_in(sig_in), .se(1'b0), .si(1'b0), .sig_out(sig_out));

endmodule

module wav_demet_set (
   input  wire   clk,
   input  wire   nset,
   input  wire   sig_in,
   input  wire   se,
   input  wire   si,
   output wire   sig_out
  );

// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//     reg ff1, ff2;
//     always @(posedge clk or negedge nset) begin
//       if(~nset) begin
//         ff1 <= 1'b1;
//         ff2 <= 1'b1;
//       end else begin
//         ff1 <= sig_in;
//         ff2 <= ff1;
//       end
//     end
//     assign sig_out = ff2;
// `endif

wav_demet_s #(
  //parameters
  .DWIDTH             ( 1         )
) u_wav_demet_s (
  .i_clk     ( clk        ),
  .i_set     ( ~nset      ),
  .i_d       ( sig_in     ),
  .o_q       ( sig_out    ));

endmodule

module demet (
   input  wire   clk,
   input  wire   sig_in,
   output wire   sig_out
);

//wav_demet u_wav_demet (.clk(clk), .sig_in(sig_in), .se(1'b0), .si(1'b0), .sig_out(sig_out));
wav_demet u_wav_demet (.i_clk(clk), .i_d(sig_in), .o_q(sig_out));

endmodule

// module wav_demet (
//    input  wire   clk,
//    input  wire   sig_in,
//    input  wire   se,
//    input  wire   si,
//    output wire   sig_out
//   );
//
// `ifdef WAV_STDCELL_GF12LP
// //    CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
// //       .I  (i_a),
// //       .ZN (o_z)
// //    );
//    //cadence script_begin
//    //set_db [get_db insts */u_inv[*]] .preserve true
//    //cadence script_end
// `else
//     reg ff1, ff2;
//     always @(posedge clk) begin
//       ff1 <= sig_in;
//       ff2 <= ff1;
//     end
//     assign sig_out = ff2;
// `endif
//
// endmodule

module wav_cen
  #(
    parameter                   EN_WIDTH              = 1
   )
   (
    input  wire                 clk_in,
    input  wire                 reset,
    input  wire [EN_WIDTH-1:0]  enable,
    input  wire                 test_en,
    input  wire                 disable_clkgate,
    output wire                 clk_out
   );

  wire [EN_WIDTH-1:0]         enable_ff2;
  wire                        clk_en;

  demet_reset u_demet_enable[EN_WIDTH-1:0]
    (
     .clk      ( clk_in               ),
     .reset    ( reset                ),
     .sig_in   ( enable               ),
     .sig_out  ( enable_ff2           )
    );

  generate
    if (EN_WIDTH == 1) begin : gen_single_enable

      assign clk_en = disable_clkgate ? 1'b1 : enable_ff2;

      wav_clock_gate u_wav_clock_gate
        (
         .clk_in   ( clk_in           ),
         .en       ( clk_en           ),
         .test_en  ( test_en          ),
         .clk_out  ( clk_out          )
        );

    end else begin : gen_multiple_enables

      reg       enable_ff;

      always @(posedge clk_in or posedge reset) begin
        if (reset) begin
          enable_ff       <= 1'b0;
        end else begin
          enable_ff       <= |enable_ff2;
        end
      end

      assign clk_en = disable_clkgate ? 1'b1 : enable_ff;

      wav_clock_gate u_wav_clock_gate
        (
         .clk_in   ( clk_in           ),
         .en       ( clk_en           ),
         .test_en  ( test_en          ),
         .clk_out  ( clk_out          )
        );

    end
  endgenerate

endmodule

// Handles reset_sync and extra DFT muxing
module wav_cen_reset_sync #(
  parameter     STDCELL   = 2,
  parameter     EN_WIDTH  = 1
)(
  input  wire                   clk_in,
  input  wire                   reset_async,
  input  wire  [EN_WIDTH-1:0]   enable,
  input  wire                   disable_clkgate,

  input  wire                   core_scan_mode,
  input  wire                   core_scan_clk,
  input  wire                   core_scan_asyncrst_ctrl,

  output wire                   reset_sync,
  output wire                   clk_gated_out
);

wire clk_pre_gate_scan;
wire disable_clkgate_sync;
wire clk_out_cen;

wav_clock_mux u_wav_clock_mux_pregate (
  .clk0    ( clk_in               ),
  .clk1    ( core_scan_clk        ),
  .sel     ( core_scan_mode       ),
  .clk_out ( clk_pre_gate_scan    ));

wav_reset_sync u_wav_reset_sync (
  .clk           ( clk_pre_gate_scan            ),
  .scan_ctrl     ( core_scan_asyncrst_ctrl      ),
  .reset_in      ( reset_async                  ),
  .reset_out     ( reset_sync                   ));

// Removed as you want to be able to bypass the gate without the need to run the clock
// demet_reset u_demet_reset_disable_clkgate (
//   .clk     ( clk_pre_gate_scan      ),
//   .reset   ( reset_sync             ),
//   .sig_in  ( disable_clkgate        ),
//   .sig_out ( disable_clkgate_sync   ));

wav_cen #(
  //parameters
  .EN_WIDTH           ( EN_WIDTH  )
) u_wav_cen (
  .clk_in              ( clk_pre_gate_scan    ),
  .reset               ( reset_sync           ),
  .enable              ( enable               ),
  .test_en             ( core_scan_mode       ),
  .disable_clkgate     ( disable_clkgate      ),
  .clk_out             ( clk_out_cen          ));

wav_clock_mux u_wav_clock_mux_postgate (
  .clk0    ( clk_out_cen          ),
  .clk1    ( core_scan_clk        ),
  .sel     ( core_scan_mode       ),
  .clk_out ( clk_gated_out        ));

endmodule

module wav_reset_sync
(
  input  wire     clk,
  input  wire     scan_ctrl,
  input  wire     reset_in,
  output wire     reset_out
);

  wire reset_in_ff2;
  wire reset_in_int;

  assign reset_in_int = ~scan_ctrl & reset_in;

  demet_set u_demet_set
    (
     .clk          ( clk               ),
     .set          ( reset_in_int      ),
     .sig_in       ( 1'b0              ),
     .sig_out      ( reset_in_ff2      )
    );

  assign  reset_out = ~scan_ctrl & reset_in_ff2;

endmodule

module wav_reset_si_sync
(
  input  wire     clk,
  input  wire     scan_ctrl,
  input  wire     reset,
  input  wire     in,
  output wire     out
);

  wire in_ff2;

  wire reset_int = ~scan_ctrl & reset;

  demet_reset u_demet_reset(
    .clk          ( clk               ),
    .reset        ( reset_int         ),
    .sig_in       ( in                ),
    .sig_out      ( in_ff2            )
  );

  assign  out = ~scan_ctrl & (in | in_ff2);

endmodule

module wav_reset_sync_n
(
  input  wire     clk,
  input  wire     scan_ctrl,
  input  wire     reset_in,
  output wire     reset_out
);

  wire reset_in_ff2;
  wire reset_in_int;

  assign reset_in_int = scan_ctrl | reset_in;

//demet_reset u_demet_reset
//  (
//   .clk      ( clk                  ),
//   .reset    ( 1'b0                 ),
//   .sig_in   ( reset_in             ),
//   .sig_out  ( reset_in_ff2         )
//  );

  demet_reset u_demet_reset
    (
     .clk      ( clk                  ),
     .reset    ( ~reset_in_int        ),
     .sig_in   ( 1'b1                 ),
     .sig_out  ( reset_in_ff2         )
    );

  assign  reset_out = scan_ctrl | (reset_in & reset_in_ff2);

endmodule

module wav_set_sync
(
  input  wire     clk,
  input  wire     scan_ctrl,
  input  wire     set,
  input  wire     in,
  output wire     out
);

  wire in_ff2;

  assign set_int = ~scan_ctrl & set;

  demet_set u_demet_set(
    .clk          ( clk               ),
    .set          ( set_int           ),
    .sig_in       ( in                ),
    .sig_out      ( in_ff2            )
  );

  assign  out = ~scan_ctrl & (in | in_ff2);

endmodule
