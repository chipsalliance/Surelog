
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

module wav_jtag_bsr #(
  parameter RESET_VAL = 1'b0
) (
   input  logic i_tck,
   input  logic i_trst_n,
   input  logic i_bsr_mode,
   input  logic i_capture,
   input  logic i_shift,
   input  logic i_update,
   input  logic i_pi,
   output logic o_po,
   input  logic i_tdi,
   output logic o_tdo
);

`ifdef WAV_JTAG_BEHAV
   reg capture_q;
   reg update_q;

   always @(posedge i_tck or negedge i_trst_n)
      if (!i_trst_n)
         capture_q <= RESET_VAL;
      else
         if (i_capture || i_shift)
            capture_q <= i_shift ? i_tdi : i_pi;

   always @(negedge i_tck or negedge i_trst_n)
      if (!i_trst_n)
         update_q <= RESET_VAL;
      else
         if (i_update)
            update_q <= capture_q;

   assign o_po = i_bsr_mode ? update_q : i_pi;
`else
   logic capture_q;
   logic update_q;
   logic capture_d;
   logic capture_en;
   logic trst;

   wav_or  u_or (.i_a(i_capture), .i_b(i_shift), .o_z(capture_en));
   wav_mux u_capture_mux (.i_a(i_pi), .i_b(i_tdi), .i_sel(i_shift), .o_z(capture_d));

   wav_inv u_inv (.i_a(i_trst_n), .o_z(trst));
   generate
    if(RESET_VAL == 0) begin : gen_reset_dff
      wav_dff_r_e u_capture_ff (.i_clk (i_tck), .i_rst(trst), .i_en(capture_en), .i_d(capture_d), .o_q(capture_q));
      wav_dff_r_e u_update_ff  (.i_clk (i_tck), .i_rst(trst), .i_en(i_update  ), .i_d(capture_q), .o_q(update_q ));
    end else begin : gen_set_dff
      wav_dff_s_e u_capture_ff (.i_clk (i_tck), .i_set(trst), .i_en(capture_en), .i_d(capture_d), .o_q(capture_q));
      wav_dff_s_e u_update_ff  (.i_clk (i_tck), .i_set(trst), .i_en(i_update  ), .i_d(capture_q), .o_q(update_q ));
    end
   endgenerate

   wav_mux u_po_mux (.i_a(i_pi), .i_b(update_q), .i_sel(i_bsr_mode), .o_z(o_po));
`endif

   assign o_tdo = capture_q;

endmodule

module wav_jtag_reg #(
   parameter              NO_BYP   = 0,                 //1 - Don't include the bypass register
   parameter              DWIDTH   = 8,
   parameter [DWIDTH-1:0] BSR_MASK = {DWIDTH{1'b0}},
   parameter [DWIDTH-1:0] RESET_VAL= {DWIDTH{1'b0}}
) (
   input  logic              i_tck,
   input  logic              i_trst_n,
   input  logic              i_bsr_mode,
   input  logic              i_capture,
   input  logic              i_shift,
   input  logic              i_update,
   input  logic [DWIDTH-1:0] i_pi,
   output logic [DWIDTH-1:0] o_po,
   input  logic              i_tdi,
   output logic              o_tdo
);

`ifdef WAV_BSR_EMPTY

  assign o_tdo = i_tdi;
  assign o_po  = i_pi;

`else // WAV_BSR_EMPTY

   wire [DWIDTH:0] tdo;
   wire bypass_tdo;
   wire bypass_n;

   generate
    if(NO_BYP == 1) begin : gen_no_bypass_register
      //No reg
      assign bypass_tdo = i_tdi;
      assign bypass_n   = 1'b1;
    end else begin : gen_bypass_register
      // Bypass register is first element in the chain
      wav_jtag_bsr u_bypass_reg (
         .i_tck        (i_tck),
         .i_trst_n     (i_trst_n),
         .i_bsr_mode   (i_bsr_mode),
         .i_capture    (1'b0),
         .i_shift      (i_shift),
         .i_update     (i_update),
         .i_pi         (1'b0),
         .o_po         (bypass_n),
         .i_tdi        (i_tdi),
         .o_tdo        (bypass_tdo)
      );
    end
   endgenerate

   //assign tdo[0] = bypass_tdo;
   assign tdo[DWIDTH] = bypass_tdo;
   wire [DWIDTH-1:0] po;

   genvar i;
   generate
      //for (i=0; i<DWIDTH; i=i+1) begin : bsr_register
      for (i=DWIDTH-1; i>=0; i=i-1) begin : bsr_register
         wav_jtag_bsr #(.RESET_VAL(RESET_VAL[i])) u_reg (
            .i_tck        (i_tck),
            .i_trst_n     (i_trst_n),
            .i_bsr_mode   (i_bsr_mode),
            .i_capture    (i_capture),
            .i_shift      (i_shift),
            .i_update     (i_update),
            .i_pi         (i_pi[i]),
            .o_po         (po[i]),
            //.i_tdi        (tdo[i]),
            //.o_tdo        (tdo[i+1])
            .i_tdi        (tdo[i+1]),
            .o_tdo        (tdo[i])
         );
         // If BSR is masked then bypass
         assign o_po[i] = BSR_MASK[i] ? i_pi[i] : po[i];
      end
   endgenerate

   // If active low bypass is asserted, then bypass the chain
   //assign o_tdo = !bypass_n ? i_tdi : tdo[DWIDTH];
   assign o_tdo = !bypass_n ? i_tdi : tdo[0];

`endif // WAV_BSR_EMPTY
endmodule

module wav_jtag_tap (

   input  logic  i_tck,
   input  logic  i_trst_n,
   input  logic  i_tms,

   output logic  o_test_logic_reset,

   output logic  o_shift_dr,
   output logic  o_update_dr,
   output logic  o_capture_dr,

   output logic  o_shift_ir,
   output logic  o_update_ir,
   output logic  o_capture_ir

);


   localparam STATE_TEST_LOGIC_RESET = 4'hF;
   localparam STATE_RUN_TEST_IDLE    = 4'hC;
   localparam STATE_SELECT_DR_SCAN   = 4'h7;
   localparam STATE_CAPTURE_DR       = 4'h6;
   localparam STATE_SHIFT_DR         = 4'h2;
   localparam STATE_EXIT1_DR         = 4'h1;
   localparam STATE_PAUSE_DR         = 4'h3;
   localparam STATE_EXIT2_DR         = 4'h0;
   localparam STATE_UPDATE_DR        = 4'h5;
   localparam STATE_SELECT_IR_SCAN   = 4'h4;
   localparam STATE_CAPTURE_IR       = 4'hE;
   localparam STATE_SHIFT_IR         = 4'hA;
   localparam STATE_EXIT1_IR         = 4'h9;
   localparam STATE_PAUSE_IR         = 4'hB;
   localparam STATE_EXIT2_IR         = 4'h8;
   localparam STATE_UPDATE_IR        = 4'hD;

   reg [3:0] tap_state;
   reg [3:0] next_tap_state;

   always_ff @ (posedge i_tck, negedge i_trst_n) begin
      if(!i_trst_n) begin
         tap_state          <= STATE_TEST_LOGIC_RESET;
      end else begin
         tap_state          <= next_tap_state;
      end
   end

   // Determination of next state; purely combinatorial
   always_comb begin
      case(tap_state)
         STATE_TEST_LOGIC_RESET:
            if(i_tms) next_tap_state    = STATE_TEST_LOGIC_RESET;
            else next_tap_state = STATE_RUN_TEST_IDLE;
         STATE_RUN_TEST_IDLE:
            if(i_tms) next_tap_state = STATE_SELECT_DR_SCAN;
            else next_tap_state = STATE_RUN_TEST_IDLE;
         STATE_SELECT_DR_SCAN:
            if(i_tms) next_tap_state = STATE_SELECT_IR_SCAN;
            else next_tap_state = STATE_CAPTURE_DR;
         STATE_CAPTURE_DR:
            if(i_tms) next_tap_state = STATE_EXIT1_DR;
            else next_tap_state = STATE_SHIFT_DR;
         STATE_SHIFT_DR:
            if(i_tms) next_tap_state = STATE_EXIT1_DR;
            else next_tap_state = STATE_SHIFT_DR;
         STATE_EXIT1_DR:
            if(i_tms) next_tap_state = STATE_UPDATE_DR;
            else next_tap_state = STATE_PAUSE_DR;
         STATE_PAUSE_DR:
            if(i_tms) next_tap_state = STATE_EXIT2_DR;
            else next_tap_state = STATE_PAUSE_DR;
         STATE_EXIT2_DR:
            if(i_tms) next_tap_state = STATE_UPDATE_DR;
            else next_tap_state = STATE_SHIFT_DR;
         STATE_UPDATE_DR:
            if(i_tms) next_tap_state = STATE_SELECT_DR_SCAN;
            else next_tap_state = STATE_RUN_TEST_IDLE;
         STATE_SELECT_IR_SCAN:
            if(i_tms) next_tap_state = STATE_TEST_LOGIC_RESET;
            else next_tap_state = STATE_CAPTURE_IR;
         STATE_CAPTURE_IR:
            if(i_tms) next_tap_state = STATE_EXIT1_IR;
            else next_tap_state = STATE_SHIFT_IR;
         STATE_SHIFT_IR:
            if(i_tms) next_tap_state = STATE_EXIT1_IR;
            else next_tap_state = STATE_SHIFT_IR;
         STATE_EXIT1_IR:
            if(i_tms) next_tap_state = STATE_UPDATE_IR;
            else next_tap_state = STATE_PAUSE_IR;
         STATE_PAUSE_IR:
            if(i_tms) next_tap_state = STATE_EXIT2_IR;
            else next_tap_state = STATE_PAUSE_IR;
         STATE_EXIT2_IR:
            if(i_tms) next_tap_state = STATE_UPDATE_IR;
            else next_tap_state = STATE_SHIFT_IR;
         STATE_UPDATE_IR:
            if(i_tms) next_tap_state = STATE_SELECT_DR_SCAN;
            else next_tap_state = STATE_RUN_TEST_IDLE;
         default: next_tap_state = STATE_TEST_LOGIC_RESET;
      endcase
   end

   always_comb begin

      o_test_logic_reset = 1'b0;
      o_capture_dr       = 1'b0;
      o_shift_dr         = 1'b0;
      o_update_dr        = 1'b0;
      o_capture_ir       = 1'b0;
      o_shift_ir         = 1'b0;
      o_update_ir        = 1'b0;

      case(tap_state)
         STATE_TEST_LOGIC_RESET: o_test_logic_reset = 1'b1;
         STATE_CAPTURE_DR:       o_capture_dr       = 1'b1;
         STATE_SHIFT_DR:         o_shift_dr         = 1'b1;
         STATE_UPDATE_DR:        o_update_dr        = 1'b1;
         STATE_CAPTURE_IR:       o_capture_ir       = 1'b1;
         STATE_SHIFT_IR:         o_shift_ir         = 1'b1;
         STATE_UPDATE_IR:        o_update_ir        = 1'b1;
      endcase
   end

endmodule

module wav_jtag_top #(
  parameter [31:0] IDCODE_RESET   = 32'h7761_7601,     //[0] must be 1
  parameter        INCLUDE_APB    = 0,
  parameter        APB_ADDR_WIDTH = 64,
  parameter        NUM_STAPS      = 1
)(
  input  wire                       i_tck,
  input  wire                       i_trst_n,
  input  wire                       i_tms,
  input  wire                       i_tdi,
  output reg                        o_tdo,

  output wire                       o_dsr_mode,
  output wire                       o_dsr_tdo,
  input  wire                       i_dsr_tdo,
  output wire                       o_dsr_shift,
  output wire                       o_dsr_capture,
  output wire                       o_dsr_update,

  output wire                       o_bsr_mode,
  output wire                       o_bsr_tdo,
  input  wire                       i_bsr_tdo,
  output wire                       o_bsr_shift,
  output wire                       o_bsr_capture,
  output wire                       o_bsr_update,

  output wire                       o_stap_enable,
  output wire [NUM_STAPS-1:0]       o_stap_sel,
  output wire [NUM_STAPS-1:0]       o_stap_rti_or_tlr,
  output wire                       o_stap_tdi_sk,
  input  wire                       i_stap_tdo_s1,

  input  wire                       i_freeze_n,
  input  wire                       i_highz_n,
  input  wire                       i_iddq_mode,

  output wire                       o_freeze_n,
  output wire                       o_highz_n,
  output wire                       o_iddq_mode,

  output wire [7:0]                 o_scan_freq_en,
  output wire                       o_scan_cgc_ctrl,
  output wire                       o_scan_rst_ctrl,
  output wire                       o_scan_set_ctrl,

  input  wire                       i_apb_clk,
  input  wire                       i_apb_reset,
  output wire                       o_apb_psel,
  output wire                       o_apb_penable,
  output wire                       o_apb_pwrite,
  output wire [31:0]                o_apb_pwdata,
  output wire [APB_ADDR_WIDTH-1:0]  o_apb_paddr,
  input  wire                       i_apb_pslverr,
  input  wire                       i_apb_pready,
  input  wire [31:0]                i_apb_prdata

);

  localparam  JTAG_BYASS    = 8'hff,          //Spec requirement
              JTAG_SAMPLE   = 8'h05,
              JTAG_PRELOAD  = 8'h09,
              JTAG_EXTEST   = 8'h0d,
              JTAG_IDCODE   = 8'h15,
              JTAG_SCAN_CTRL= 8'h39,
              JTAG_INT_DSR  = 8'h40,
              JTAG_EXT_DSR  = 8'h41,
              JTAG_APB      = 8'hab,
              JTAG_3DCR     = 8'h3d;

  wire tap_shift_dr;
  wire tap_update_dr;
  wire tap_capture_dr;
  wire tap_shift_ir;
  wire tap_update_ir;
  wire tap_capture_ir;

  wav_jtag_tap u_wav_jtag_tap (
    .i_tck                 ( i_tck                  ),
    .i_trst_n              ( i_trst_n               ),
    .i_tms                 ( i_tms                  ),
    .o_test_logic_reset    ( /*noconn*/             ),
    .o_shift_dr            ( tap_shift_dr           ),
    .o_update_dr           ( tap_update_dr          ),
    .o_capture_dr          ( tap_capture_dr         ),
    .o_shift_ir            ( tap_shift_ir           ),
    .o_update_ir           ( tap_update_ir          ),
    .o_capture_ir          ( tap_capture_ir         ));

  //----------------------------
  // Instruction Register
  //----------------------------
  wire [7:0]  jtag_ir;
  wire        jtag_ir_tdo;

  wav_jtag_reg #(
    .NO_BYP             ( 1           ),
    .DWIDTH             ( 8           ),
    .RESET_VAL          ( JTAG_IDCODE )
  ) u_jtag_reg_instruction (
    .i_tck              ( i_tck          ),
    .i_trst_n           ( i_trst_n       ),
    .i_bsr_mode         ( 1'b1           ),
    .i_capture          ( tap_capture_ir ),
    .i_shift            ( tap_shift_ir   ),
    .i_update           ( tap_update_ir  ),
    .i_pi               ( 8'd0           ),
    .o_po               ( jtag_ir        ),
    .i_tdi              ( i_tdi          ),
    .o_tdo              ( jtag_ir_tdo    ));

  //----------------------------
  // IDCODE Register
  //----------------------------
  wire idcode_tdo;
  wire idcode_capture_dr  = tap_capture_dr && (jtag_ir == JTAG_IDCODE);
  wire idcode_shift_dr    = tap_shift_dr   && (jtag_ir == JTAG_IDCODE);
  wire idcode_update_dr   = tap_update_dr  && (jtag_ir == JTAG_IDCODE);

  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1            ),
    .DWIDTH             ( 32           ),
    .RESET_VAL          ( IDCODE_RESET )
  ) u_jtag_reg_idcode (
    .i_tck         ( i_tck              ),
    .i_trst_n      ( i_trst_n           ),
    .i_bsr_mode    ( 1'b1               ),
    .i_capture     ( idcode_capture_dr  ),
    .i_shift       ( idcode_shift_dr    ),
    .i_update      ( idcode_update_dr   ),
    .i_pi          ( IDCODE_RESET       ),
    .o_po          ( /*noconn*/         ),
    .i_tdi         ( i_tdi              ),
    .o_tdo         ( idcode_tdo         ));

  //----------------------------
  // SCAN_CTRL Register
  //----------------------------

  wire scan_ctrl_tdo;
  wire scan_ctrl_capture_dr  = tap_capture_dr && (jtag_ir == JTAG_SCAN_CTRL);
  wire scan_ctrl_shift_dr    = tap_shift_dr   && (jtag_ir == JTAG_SCAN_CTRL);
  wire scan_ctrl_update_dr   = tap_update_dr  && (jtag_ir == JTAG_SCAN_CTRL);
  wire [11:0] scan_ctrl_reg;

  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1            ),
    .DWIDTH             ( 12           ),
    .RESET_VAL          ( {12{1'b0}}   )
  ) u_jtag_reg_scan_ctrl (
    .i_tck         ( i_tck                ),
    .i_trst_n      ( i_trst_n             ),
    .i_bsr_mode    ( 1'b1                 ),
    .i_capture     ( scan_ctrl_capture_dr ),
    .i_shift       ( scan_ctrl_shift_dr   ),
    .i_update      ( scan_ctrl_update_dr  ),
    .i_pi          ( 12'd0                ),
    .o_po          ( scan_ctrl_reg        ),
    .i_tdi         ( i_tdi                ),
    .o_tdo         ( scan_ctrl_tdo        ));

  assign o_scan_freq_en   = scan_ctrl_reg[7:0];
  assign o_scan_cgc_ctrl  = scan_ctrl_reg[8];
  assign o_scan_rst_ctrl  = scan_ctrl_reg[9];
  assign o_scan_set_ctrl  = scan_ctrl_reg[10];

  //----------------------------
  // Internal Data Register
  //----------------------------

  wire int_dsr_tdo;
  wire int_dsr_capture_dr  = tap_capture_dr && (jtag_ir == JTAG_INT_DSR);
  wire int_dsr_shift_dr    = tap_shift_dr   && (jtag_ir == JTAG_INT_DSR);
  wire int_dsr_update_dr   = tap_update_dr  && (jtag_ir == JTAG_INT_DSR);
  wire [3:0] int_dsr_reg;

  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1            ),
    .DWIDTH             ( 4            ),
    .RESET_VAL          ( {4{1'b0}}    )
  ) u_jtag_reg_dsr (
    .i_tck         ( i_tck              ),
    .i_trst_n      ( i_trst_n           ),
    .i_bsr_mode    ( 1'b1               ),
    .i_capture     ( int_dsr_capture_dr ),
    .i_shift       ( int_dsr_shift_dr   ),
    .i_update      ( int_dsr_update_dr  ),
    .i_pi          ( 4'd0               ),
    .o_po          ( int_dsr_reg        ),
    .i_tdi         ( i_tdi              ),
    .o_tdo         ( int_dsr_tdo        ));

  wire test_mode     = int_dsr_reg[0];
  assign o_freeze_n  = test_mode ? ~int_dsr_reg[1] : i_freeze_n;
  assign o_highz_n   = test_mode ? ~int_dsr_reg[2] : i_highz_n;
  assign o_iddq_mode = test_mode ?  int_dsr_reg[3] : i_iddq_mode;

  //----------------------------
  // Bypass Register
  //----------------------------
  wire bypass_tdo;
  wire bypass_capture_dr  = tap_capture_dr && (jtag_ir == JTAG_BYASS);
  wire bypass_shift_dr    = tap_shift_dr   && (jtag_ir == JTAG_BYASS);
  wire bypass_update_dr   = tap_update_dr  && (jtag_ir == JTAG_BYASS);

  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1           ),
    .DWIDTH             ( 1           ),
    .RESET_VAL          ( 1'b0        )
  ) u_jtag_reg_bypass (
    .i_tck         ( i_tck             ),
    .i_trst_n      ( i_trst_n          ),
    .i_bsr_mode    ( 1'b1              ),
    .i_capture     ( bypass_capture_dr ),
    .i_shift       ( bypass_shift_dr   ),
    .i_update      ( bypass_update_dr  ),
    .i_pi          ( 1'b0              ),
    .o_po          ( /*noconn*/        ),
    .i_tdi         ( i_tdi             ),
    .o_tdo         ( bypass_tdo        ));

  //----------------------------
  // External Data Reg Control
  //----------------------------

  wire ext_dsr_sel  = (jtag_ir == JTAG_EXT_DSR);
  assign o_dsr_shift   = tap_shift_dr   && ext_dsr_sel;
  assign o_dsr_capture = tap_capture_dr && ext_dsr_sel;
  assign o_dsr_update  = tap_update_dr  && ext_dsr_sel;
  assign o_dsr_mode = jtag_ir == JTAG_EXT_DSR;
  assign o_dsr_tdo = i_tdi;

  //----------------------------
  // External BSCAN Control
  //----------------------------

  wire ext_bsr_sel  = (jtag_ir == JTAG_SAMPLE || jtag_ir == JTAG_PRELOAD || jtag_ir == JTAG_EXTEST);
  assign o_bsr_shift   = tap_shift_dr   && ext_bsr_sel;
  assign o_bsr_capture = tap_capture_dr && ext_bsr_sel;
  assign o_bsr_update  = tap_update_dr  && ext_bsr_sel;
  assign o_bsr_mode = jtag_ir == JTAG_EXTEST;
  assign o_bsr_tdo = i_tdi;

  //----------------------------
  // STAP Support
  //----------------------------
  wire threeDCR_tdo;
  wire threeDCR_sel_tdo;
  wire threeDCR_capture_dr  = tap_capture_dr && (jtag_ir == JTAG_3DCR);
  wire threeDCR_shift_dr    = tap_shift_dr   && (jtag_ir == JTAG_3DCR);
  wire threeDCR_update_dr   = tap_update_dr  && (jtag_ir == JTAG_3DCR);
  
  wire threeDCR_config_hold;
  
  assign o_stap_enable      = (|o_stap_sel);
  
  
  // MSb - Config-Hold Signal (reset to 0)    
  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1                     ),
    .DWIDTH             ( (NUM_STAPS*2)         ),
    .RESET_VAL          ( {{(NUM_STAPS){1'b1}}, {(NUM_STAPS){1'b0}}}  )
  ) u_jtag_reg_3dcr (
    .i_tck         ( i_tck                            ),
    .i_trst_n      ( i_trst_n | threeDCR_config_hold  ),  //only reset of cfgHold is not blocking
    .i_bsr_mode    ( 1'b1                             ),
    .i_capture     ( threeDCR_capture_dr              ),
    .i_shift       ( threeDCR_shift_dr                ),
    .i_update      ( threeDCR_update_dr               ),
    .i_pi          ( {(NUM_STAPS*2){1'b0}}            ),
    .o_po          ( {o_stap_rti_or_tlr,
                      o_stap_sel}                     ),
    .i_tdi         ( i_tdi                            ),
    .o_tdo         ( threeDCR_sel_tdo                 ));
  
  wav_jtag_reg #(
    //parameters
    .NO_BYP             ( 1     ),
    .DWIDTH             ( 1     ),
    .RESET_VAL          ( 1'b0  )
  ) u_jtag_reg_3dcr_cfghold (
    .i_tck         ( i_tck                            ),
    .i_trst_n      ( i_trst_n                         ),
    .i_bsr_mode    ( 1'b1                             ),
    .i_capture     ( threeDCR_capture_dr              ),
    .i_shift       ( threeDCR_shift_dr                ),
    .i_update      ( threeDCR_update_dr               ),
    .i_pi          ( 1'b0                             ),
    .o_po          ( threeDCR_config_hold             ),
    .i_tdi         ( threeDCR_sel_tdo                 ),
    .o_tdo         ( threeDCR_tdo                     ));
  

  //----------------------------
  // APB
  //----------------------------
  wire  apb_tdo;

  generate
    if(INCLUDE_APB) begin : gen_apb_logic

      // [0]    - Start
      // [1]    - 1 - Write, 0 - Read (only valid when start is set). On shift out this is the error
      // [2]    - IDLE (status on shift out)
      // [34:3] - PWDATA/PRDATA - Write data when write transaction, captured PRDATA
      // [APB_ADDR_WIDTH+34:35] - PADDR
      localparam  APB_REG_WIDTH = APB_ADDR_WIDTH + 32 + 1 + 1 + 1;

      wire [APB_REG_WIDTH-1:0]  apb_reg_po, apb_reg_pi;

      wire apb_capture_dr         = tap_capture_dr && (jtag_ir == JTAG_APB);
      wire apb_shift_dr           = tap_shift_dr   && (jtag_ir == JTAG_APB);
      wire apb_update_dr          = tap_update_dr  && (jtag_ir == JTAG_APB);

      wire                      apb_reg_start   = apb_reg_po[0];
      wire                      apb_reg_write   = apb_reg_po[1];
      wire [31:0]               apb_reg_pwdata  = apb_reg_po[34:3];
      wire [APB_ADDR_WIDTH-1:0] apb_reg_paddr   = apb_reg_po[APB_ADDR_WIDTH+34:35];

      wav_jtag_reg #(
        //parameters
        .NO_BYP             ( 1                     ),
        .DWIDTH             ( APB_REG_WIDTH         ),
        .RESET_VAL          ( {APB_REG_WIDTH{1'b0}} )
      ) u_jtag_reg_apb_control (
        .i_tck         ( i_tck             ),
        .i_trst_n      ( i_trst_n          ),
        .i_bsr_mode    ( 1'b1              ),
        .i_capture     ( apb_capture_dr    ),
        .i_shift       ( apb_shift_dr      ),
        .i_update      ( apb_update_dr     ),
        .i_pi          ( apb_reg_pi        ),
        .o_po          ( apb_reg_po        ),
        .i_tdi         ( i_tdi             ),
        .o_tdo         ( apb_tdo           ));

      wire [31:0] apb_prdata;
      wire        apb_plsverr;
      wire        apb_idle;

      assign apb_reg_pi[0]                    = 1'b0;
      assign apb_reg_pi[1]                    = apb_plsverr;
      assign apb_reg_pi[2]                    = apb_idle;
      assign apb_reg_pi[34:3]                 = apb_prdata;
      assign apb_reg_pi[APB_ADDR_WIDTH+34:35] = {APB_ADDR_WIDTH{1'b0}};

      wav_jtag2apb #(
        //parameters
        .ADDR_WIDTH         ( APB_ADDR_WIDTH )
      ) u_wav_jtag2apb (
        .i_jtag_tck    ( i_tck            ),
        .i_jtag_trst_n ( i_trst_n         ),
        .i_jtag_write  ( apb_reg_write    ),
        .i_jtag_addr   ( apb_reg_paddr    ),
        .i_jtag_wdata  ( apb_reg_pwdata   ),
        .o_jtag_rdata  ( apb_prdata       ),
        .o_jtag_slverr ( apb_plsverr      ),
        .i_jtag_start  ( apb_reg_start    ),
        .o_jtag_idle   ( apb_idle         ),
        .i_apb_clk     ( i_apb_clk        ),
        .i_apb_reset   ( i_apb_reset      ),
        .o_apb_psel    ( o_apb_psel       ),
        .o_apb_penable ( o_apb_penable    ),
        .o_apb_pwrite  ( o_apb_pwrite     ),
        .o_apb_pwdata  ( o_apb_pwdata     ),
        .o_apb_paddr   ( o_apb_paddr      ),
        .i_apb_pslverr ( i_apb_pslverr    ),
        .i_apb_pready  ( i_apb_pready     ),
        .i_apb_prdata  ( i_apb_prdata     ));

    end else begin : tieoff_apb_logic

      assign apb_tdo        = bypass_tdo;

      assign o_apb_psel     = 1'b0;
      assign o_apb_penable  = 1'b0;
      assign o_apb_pwrite   = 1'b0;
      assign o_apb_pwdata   = 32'd0;
      assign o_apb_paddr    = {APB_ADDR_WIDTH{1'b0}};

    end
  endgenerate

  //----------------------------
  // TDO Output
  //----------------------------  
  // If any STAPs are selected then we need to include those in the chain
  // If no STAPs are selected then we can bypass those
  // The output STAP_TDI_Sk goes to the STAP chain
  assign o_stap_tdi_sk = tap_shift_ir ? jtag_ir_tdo :
                                        ext_dsr_sel                 ? i_dsr_tdo       :
                                        ext_bsr_sel                 ? i_bsr_tdo       :
                                        (jtag_ir == JTAG_INT_DSR)   ? int_dsr_tdo     :
                                        (jtag_ir == JTAG_BYASS)     ? bypass_tdo      :
                                        (jtag_ir == JTAG_IDCODE)    ? idcode_tdo      :
                                        (jtag_ir == JTAG_SCAN_CTRL) ? scan_ctrl_tdo   :
                                        (jtag_ir == JTAG_3DCR)      ? threeDCR_tdo    :
                                        (jtag_ir == JTAG_APB)       ? apb_tdo         : bypass_tdo;

  always @(negedge i_tck or negedge i_trst_n) begin
    if(~i_trst_n) begin
      o_tdo <= 1'b0;
    end else begin
      o_tdo <= o_stap_enable ? i_stap_tdo_s1 : o_stap_tdi_sk;
    end
  end

endmodule

module wav_jtag2apb #(
  parameter ADDR_WIDTH  = 32
)(
  //To/From JTAG BSRs
  input  wire                               i_jtag_tck,
  input  wire                               i_jtag_trst_n,
  input  wire                               i_jtag_write,
  input  wire [ADDR_WIDTH-1:0]              i_jtag_addr,
  input  wire [31:0]                        i_jtag_wdata,
  output wire [31:0]                        o_jtag_rdata,
  output wire                               o_jtag_slverr,
  input  wire                               i_jtag_start,
  output reg                                o_jtag_idle,

  input  wire                               i_apb_clk,           //
  input  wire                               i_apb_reset,         //
  output reg                                o_apb_psel,
  output reg                                o_apb_penable,
  output reg                                o_apb_pwrite,
  output reg   [31:0]                       o_apb_pwdata,
  output reg   [ADDR_WIDTH-1:0]             o_apb_paddr,
  input  wire                               i_apb_pslverr,
  input  wire                               i_apb_pready,
  input  wire  [31:0]                       i_apb_prdata
);

localparam  IDLE      = 'd0,
            APB_TRANS = 'd1;

reg                     state, nstate;
reg                     is_write, is_write_in;
wire                    jtag_start_ff2;
reg                     jtag_start_ff3;
wire                    jtag_start_re;
wire                    jtag_idle_in;
reg   [ADDR_WIDTH-1:0]  apb_paddr_reg, apb_paddr_reg_in;
reg   [31:0]            apb_pwdata_reg, apb_pwdata_reg_in;
reg   [31:0]            apb_prdata_reg, apb_prdata_reg_in;
reg   [31:0]            apb_pslverr_reg, apb_pslverr_reg_in;

`ifndef WAV_JTAG_BEHAV
demet_reset u_demet_reset (
  .clk     ( i_apb_clk      ),
  .reset   ( i_apb_reset    ),
  .sig_in  ( i_jtag_start   ),
  .sig_out ( jtag_start_ff2 ));
`else
reg ff1, ff2;
always @(posedge i_apb_clk or posedge i_apb_reset) begin
  if(i_apb_reset) begin
    ff1 <= 1'b0;
    ff2 <= 1'b0;
  end else begin
    ff1 <= i_jtag_start;
    ff2 <= ff1;
  end
end
assign jtag_start_ff2 = ff2;
`endif

assign jtag_start_re = jtag_start_ff2  & ~jtag_start_ff3;

// Let's see if we can get rid of the paddr/pwdata registers
always @(posedge i_apb_clk or posedge i_apb_reset) begin
  if(i_apb_reset) begin
    state             <= IDLE;
    jtag_start_ff3    <= 1'b0;
    is_write          <= 1'b0;
    apb_paddr_reg     <= {ADDR_WIDTH{1'b0}};
    apb_pwdata_reg    <= 32'd0;
    apb_prdata_reg    <= 32'd0;
    apb_pslverr_reg   <= 1'b0;
    o_jtag_idle       <= 1'b0;
  end else begin
    state             <= nstate;
    jtag_start_ff3    <= jtag_start_ff2;
    is_write          <= is_write_in;
    apb_paddr_reg     <= apb_paddr_reg_in;
    apb_pwdata_reg    <= apb_pwdata_reg_in;
    apb_prdata_reg    <= apb_prdata_reg_in;
    apb_pslverr_reg   <= apb_pslverr_reg_in;
    o_jtag_idle       <= jtag_idle_in;
  end
end

assign jtag_idle_in   = jtag_start_re ? 1'b0 : (state == IDLE ? 1'b1 : o_jtag_idle);

assign o_jtag_rdata   = apb_prdata_reg;
assign o_jtag_slverr  = apb_pslverr_reg;

always @(*) begin
  nstate                      = state;
  is_write_in                 = is_write;
  o_apb_psel                  = 1'b0;
  o_apb_penable               = 1'b0;
  o_apb_pwrite                = 1'b0;
  o_apb_pwdata                = 32'd0;
  o_apb_paddr                 = {ADDR_WIDTH{1'b0}};
  apb_paddr_reg_in            = apb_paddr_reg;
  apb_pwdata_reg_in           = apb_pwdata_reg;
  apb_prdata_reg_in           = apb_prdata_reg;
  apb_pslverr_reg_in          = apb_pslverr_reg;

  case(state)
    IDLE : begin
      if(jtag_start_re) begin
        is_write_in           = i_jtag_write;
        apb_paddr_reg_in      = i_jtag_addr;
        apb_pwdata_reg_in     = o_apb_pwdata;
        o_apb_psel            = 1'b1;
        o_apb_pwrite          = i_jtag_write;
        o_apb_pwdata          = i_jtag_wdata;
        o_apb_paddr           = i_jtag_addr;
        nstate                = APB_TRANS;
      end
    end

    APB_TRANS : begin
      o_apb_psel              = 1'b1;
      o_apb_pwrite            = is_write;
      o_apb_penable           = 1'b1;
      o_apb_pwdata            = apb_pwdata_reg;
      o_apb_paddr             = apb_paddr_reg;
      if(i_apb_pready) begin
        apb_prdata_reg_in     = i_apb_prdata;
        apb_pslverr_reg_in    = i_apb_pslverr;
        nstate                = IDLE;
      end
    end
  endcase
end

endmodule


//See IEEE 1838-2019 for details
module wav_jtag_stap(
  //From PTAP
  input  wire         i_tck,
  input  wire         i_tms,
  input  wire         i_trst_n,
  input  wire         i_tdi,
  output wire         o_tdo,
  input  wire         i_enable,
  input  wire         i_select,
  input  wire         i_rti_or_tlr,
  
  //To/From external die
  output wire         o_exdie_tck,
  output wire         o_exdie_tms,
  output wire         o_exdie_trst_n,
  output wire         o_exdie_tdi,
  input  wire         i_exdie_tdo  
);

reg     exdie_tdi;
reg     ptap_tdo;

assign o_exdie_tck      = i_tck;
assign o_exdie_tms      = i_select ? i_tms : i_rti_or_tlr;
assign o_exdie_trst_n   = i_trst_n;

assign o_exdie_tdi      = exdie_tdi;
assign o_tdo            = ptap_tdo;

always @(negedge i_tck or negedge i_trst_n) begin
  if(~i_trst_n) begin
    exdie_tdi   <= 1'b0;
  end else begin
    exdie_tdi   <= i_tdi;
  end
end

always @(posedge i_tck or negedge i_trst_n) begin
  if(~i_trst_n) begin
    ptap_tdo    <= 1'b0;
  end else begin
    ptap_tdo    <= i_enable ? (i_select ? i_exdie_tdo : i_tdi) : ptap_tdo;
  end
end



endmodule
