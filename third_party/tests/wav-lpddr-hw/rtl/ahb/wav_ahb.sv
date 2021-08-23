
import wav_ahb_pkg::*;

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

module wav_ahb_master_arbiter_mux #(
   parameter AWIDTH   = 32,
   parameter DWIDTH   = 32,
   parameter NUM_MSTR = 2,
   parameter MDEPTH   = $clog2(NUM_MSTR)
) (
   input  logic                         i_hclk,
   input  logic                         i_hreset,

   input  logic [AWIDTH*NUM_MSTR-1:0]   i_ahbm_haddr,
   input  logic [NUM_MSTR-1:0]          i_ahbm_hwrite,
   input  logic [DWIDTH*NUM_MSTR-1:0]   i_ahbm_hwdata,
   input  logic [2*NUM_MSTR-1:0]        i_ahbm_htrans,
   input  logic [3*NUM_MSTR-1:0]        i_ahbm_hsize,
   input  logic [3*NUM_MSTR-1:0]        i_ahbm_hburst,
   input  logic [NUM_MSTR-1:0]          i_ahbm_hbusreq,
   input  logic                         i_ahbm_hready,
   input  logic [DWIDTH-1:0]            i_ahbm_hrdata,
   input  logic [1:0]                   i_ahbm_hresp,

   output logic [AWIDTH-1:0]            o_ahbm_haddr,
   output logic                         o_ahbm_hwrite,
   output logic [DWIDTH-1:0]            o_ahbm_hwdata,
   output logic [1:0]                   o_ahbm_htrans,
   output logic [2:0]                   o_ahbm_hsize,
   output logic [2:0]                   o_ahbm_hburst,
   output logic                         o_ahbm_hbusreq,
   output logic [NUM_MSTR-1:0]          o_ahbm_hgrant,
   output logic [NUM_MSTR-1:0]          o_ahbm_hready,
   output logic [DWIDTH*NUM_MSTR-1:0]   o_ahbm_hrdata,
   output logic [2*NUM_MSTR-1:0]        o_ahbm_hresp,

   output logic [MDEPTH-1:0]            o_ahbm_hmaster,
   output logic                         o_ahbm_hmastlock

);

   wav_ahb_master_arbiter #(
      .NUM_MSTR(NUM_MSTR)
   ) u_ahb_arbiter (
      .i_hclk      (i_hclk),
      .i_hreset    (i_hreset),
      .i_hwrite    (i_ahbm_hwrite),
      .i_htrans    (i_ahbm_htrans),
      .i_hready    (i_ahbm_hready),
      .i_hbusreq   (i_ahbm_hbusreq),
      .i_hlock     ('0),
      .o_hgrant    (o_ahbm_hgrant),
      .o_hmaster   (o_ahbm_hmaster),
      .o_hmastlock (o_ahbm_hmastlock)
   );

   wav_ahb_master_mux #(
      .AWIDTH(AWIDTH),
      .DWIDTH(DWIDTH),
      .NUM_MSTR(NUM_MSTR)
   ) u_ahbm_mux (
      .i_hclk      (i_hclk),
      .i_hreset    (i_hreset),
      .i_hwrite    (i_ahbm_hwrite),
      .i_htrans    (i_ahbm_htrans),
      .i_hwdata    (i_ahbm_hwdata),
      .i_haddr     (i_ahbm_haddr),
      .i_hsize     (i_ahbm_hsize),
      .i_hburst    (i_ahbm_hburst),
      .i_hbusreq   (i_ahbm_hbusreq),
      .i_hmaster   (o_ahbm_hmaster),
      .o_hrdata    (o_ahbm_hrdata),
      .o_hresp     (o_ahbm_hresp ),
      .o_hready    (o_ahbm_hready),

      .i_hrdata    (i_ahbm_hrdata),
      .i_hresp     (i_ahbm_hresp ),
      .i_hready    (i_ahbm_hready),
      .o_hwrite    (o_ahbm_hwrite),
      .o_htrans    (o_ahbm_htrans),
      .o_hsize     (o_ahbm_hsize),
      .o_hburst    (o_ahbm_hburst),
      .o_hwdata    (o_ahbm_hwdata),
      .o_haddr     (o_ahbm_haddr),
      .o_hbusreq   (o_ahbm_hbusreq)
   );

endmodule

module wav_ahb_master_arbiter #(
   parameter NUM_MSTR = 8,
   parameter MDEPTH   = $clog2(NUM_MSTR)
) (
   input   logic                         i_hclk,
   input   logic                         i_hreset,

   input   logic [NUM_MSTR-1:0]          i_hwrite,
   input   logic [2*NUM_MSTR-1:0]        i_htrans,
   input   logic                         i_hready,
   input   logic [NUM_MSTR-1:0]          i_hbusreq,
   input   logic [NUM_MSTR-1:0]          i_hlock,

   output  logic [NUM_MSTR-1:0]          o_hgrant,
   output  logic [MDEPTH-1:0]            o_hmaster,
   output  logic                         o_hmastlock
);

   logic [NUM_MSTR-1:0]  vldtrans ;
   logic [NUM_MSTR-1:0]  req_d ;
   logic [NUM_MSTR-1:0]  req_dly ;
   logic [NUM_MSTR-1:0]  req_q ;
   logic [MDEPTH-1:0]    hmaster;
   logic [NUM_MSTR-1:0]  mstr_mask ;

  typedef enum logic [1:0] {
     IDLE       = 2'h0,
     TRANS_ADDR = 2'h1,
     TRANS_DATA = 2'h2,
     WAIT       = 2'h3
  } state_t;

   state_t state_q, state_d, state_dly ;

   genvar i;
   generate
     for (i=0; i<NUM_MSTR; i++) begin : TRANS
        assign vldtrans[i] =  ((i_htrans[((i+1)*2)-1:i*2] == AHB_TRANS_SEQ) | (i_htrans[((i+1)*2)-1:i*2] == AHB_TRANS_NONSEQ)) & i_hbusreq[i];
     end
   endgenerate

   always_ff @(posedge i_hclk, posedge i_hreset) begin
     if (i_hreset) begin
       state_q   <= IDLE ;
     end else begin
       state_q   <= state_dly ;
     end
   end

  `ifdef WAV_AHB_SIMDLY_EN
   assign #1ps state_dly = state_d ;
   assign #1ps req_dly   = req_d ;
  `else
   assign state_dly = state_d ;
   assign req_dly   = req_d ;
  `endif

   always_ff @(posedge i_hclk, posedge i_hreset) begin
     if (i_hreset) begin
       req_q  <= '0 ;
     end else begin
       req_q  <= req_dly ;
     end
   end

   always_comb begin
     state_d = state_q ;
     req_d   = req_q ;
     case(state_q)
        IDLE : begin
           req_d = vldtrans ;
           if(|(vldtrans & i_hwrite & mstr_mask) & i_hready) begin
              state_d = TRANS_DATA ;
           end else if ((|vldtrans & ~i_hready) | (|(vldtrans & ~i_hwrite & mstr_mask)))begin
              state_d = TRANS_ADDR ;
           end
        end
        TRANS_ADDR : begin
           if (i_hready) begin
              state_d = TRANS_DATA;
           end
        end
        TRANS_DATA : begin
           if (~i_hready) begin
              state_d = WAIT ;
           end else begin //if (i_hready)
              req_d = vldtrans ;
              if(~|vldtrans)
                  state_d = IDLE ;
              else if(~|(mstr_mask & vldtrans & i_hwrite))
                  state_d = TRANS_ADDR ;
              else
                  state_d = TRANS_DATA;
           end
        end
        WAIT : begin
           if(i_hready)
              req_d = vldtrans ;

           if(|(vldtrans & i_hwrite & mstr_mask) & i_hready) begin
              state_d = TRANS_DATA ;
           end else if (|(vldtrans & ~i_hwrite & mstr_mask))begin
              state_d = TRANS_ADDR ;
           end else if (i_hready) begin
              state_d = IDLE ;
           end

        end
     endcase
   end

   assign mstr_mask = {NUM_MSTR{1'b0}} | (1'b1 << hmaster) ;

   wav_priority_enc #(
      .DWIDTH(NUM_MSTR),
      .PIPELINE(1'b0)
   ) u_priority_enc (
      .i_clk    (i_hclk),
      .i_rst    (i_hreset),
      .i_dec    (req_d),
      .o_enc    (hmaster)
   );

   assign o_hmaster   = hmaster;
   assign o_hgrant    = 'b1 << o_hmaster;
   assign o_hmastlock = 'b0;

endmodule

module wav_ahb_master_mux #(
   parameter DWIDTH   = 32,
   parameter AWIDTH   = 32,
   parameter NUM_MSTR = 8,
   parameter MDEPTH   = $clog2(NUM_MSTR)
) (
   input   logic                         i_hclk,
   input   logic                         i_hreset,
   input   logic [DWIDTH*NUM_MSTR-1:0]   i_hwdata,
   input   logic [AWIDTH*NUM_MSTR-1:0]   i_haddr,
   input   logic [2*NUM_MSTR-1:0]        i_htrans,
   input   logic [3*NUM_MSTR-1:0]        i_hsize,
   input   logic [3*NUM_MSTR-1:0]        i_hburst,
   input   logic [NUM_MSTR-1:0]          i_hwrite,
   input   logic [NUM_MSTR-1:0]          i_hbusreq,
   input   logic [MDEPTH-1:0]            i_hmaster,
   output  logic [NUM_MSTR-1:0]          o_hready,
   output  logic [DWIDTH*NUM_MSTR-1:0]   o_hrdata,
   output  logic [2*NUM_MSTR-1:0]        o_hresp,

   input   logic                         i_hready,
   input   logic [DWIDTH-1:0]            i_hrdata,
   input   logic [1:0]                   i_hresp,
   output  logic                         o_hbusreq,
   output  logic                         o_hwrite,
   output  logic [1:0]                   o_htrans,
   output  logic [2:0]                   o_hsize,
   output  logic [2:0]                   o_hburst,
   output  logic [DWIDTH-1:0]            o_hwdata,
   output  logic [AWIDTH-1:0]            o_haddr
);

  logic [MDEPTH-1:0]   hmaster_q;
  logic [NUM_MSTR-1:0] mstr_mask ;
  logic [NUM_MSTR-1:0] hready;
  logic [NUM_MSTR-1:0] hready_int;
  logic [NUM_MSTR-1:0] hready_hold;
  logic [NUM_MSTR-1:0] vldtrans ;
  logic [NUM_MSTR-1:0] vldtrans_dly ;
  logic [NUM_MSTR-1:0] vldtrans_q ;

  logic                hready_d ;
  logic                hready_d_dly ;
  logic                hready_q ;
  logic                vld_htrans;
  logic                hbusreq;
  logic                hwrite;
  logic [1:0]          htrans;
  logic [2:0]          hsize;
  logic [2:0]          hburst;
  logic [DWIDTH-1:0]   hwdata;
  logic [AWIDTH-1:0]   haddr;

  genvar i;
  generate
    for (i=0; i<NUM_MSTR; i++) begin : TRANS
       assign vldtrans[i] =  ((i_htrans[((i+1)*2)-1:i*2] == AHB_TRANS_SEQ) | (i_htrans[((i+1)*2)-1:i*2] == AHB_TRANS_NONSEQ)) & i_hbusreq[i] & mstr_mask[i];
    end
  endgenerate

  assign mstr_mask = {NUM_MSTR{1'b0}} | (1'b1 << i_hmaster) ;

  `ifdef WAV_AHB_SIMDLY_EN
  assign #1ps vldtrans_dly = vldtrans ;
  `else
  assign vldtrans_dly = vldtrans ;
  `endif
  always_ff @(posedge i_hclk, posedge i_hreset) begin
     if (i_hreset) begin
        hmaster_q  <= '0;
        vldtrans_q <= '0;
     end else if(hready[0]) begin
        hmaster_q  <= i_hmaster;
        vldtrans_q <= vldtrans_dly ;
     end
  end

  typedef enum logic [1:0] {
     IDLE         = 2'h0,
     TRANS_RDADDR = 2'h1,
     TRANS_DATA   = 2'h2
  } state_t;

   state_t state_q, state_d, state_dly ;

  `ifdef WAV_AHB_SIMDLY_EN
  assign #1ps state_dly    = state_d ;
  assign #1ps hready_d_dly = hready_d ;
  `else
  assign state_dly = state_d ;
  assign hready_d_dly = hready_d ;
  `endif

   assign vld_htrans = ((htrans == AHB_TRANS_SEQ) | (htrans == AHB_TRANS_NONSEQ)) & hbusreq ;

   always_ff @(posedge i_hclk, posedge i_hreset) begin
     if (i_hreset) begin
       state_q   <= IDLE ;
       hready_q  <= '0 ;
     end else begin
       state_q   <= state_dly ;
       hready_q  <= hready_d_dly ;
     end
   end

   always_comb begin
     state_d  = state_q ;
     hready_d = hready_q ;
     case(state_q)
        IDLE : begin
           hready_d = 1'b1 ;
           if(vld_htrans & hwrite ) begin
              state_d  = TRANS_DATA ;
              hready_d = vld_htrans ;
           end else if(vld_htrans & !hwrite ) begin
              state_d  = TRANS_RDADDR ;
              hready_d = vld_htrans ;
           end
        end
        TRANS_RDADDR : begin
           hready_d = 0 ;
           if (i_hready) begin
              state_d  = TRANS_DATA;
           end
        end
        TRANS_DATA : begin
           hready_d = i_hready ;
           if (i_hready & ~vld_htrans) begin
              state_d = IDLE ;
           end else if (i_hready & vld_htrans & ~hwrite) begin
              state_d = TRANS_RDADDR ;
           end else begin //i_hready & vld_htrans & hwrite
              state_d = TRANS_DATA ;
           end
        end
     endcase
   end

  always_ff @(posedge i_hclk, posedge i_hreset) begin
     if(i_hreset) begin
        o_hwdata  <= '0;
        o_haddr   <= '0;
        o_htrans  <= '0;
        o_hsize   <= '0;
        o_hburst  <= '0;
        o_hwrite  <= '0;
        o_hbusreq <= '0;
     end else if ((vld_htrans & hready_d_dly) | i_hready)begin
        o_hwdata  <= hwdata ;
        o_haddr   <= haddr  ;
        o_htrans  <= htrans ;
        o_hsize   <= hsize  ;
        o_hburst  <= hburst ;
        o_hwrite  <= hwrite ;
        o_hbusreq <= hbusreq;
     end
  end

  assign hwdata  = i_hwdata  >> DWIDTH * hmaster_q;
  assign haddr   = i_haddr   >> AWIDTH * i_hmaster;
  assign htrans  = i_htrans  >> 2 * i_hmaster;
  assign hsize   = i_hsize   >> 3 * i_hmaster;
  assign hburst  = i_hburst  >> 3 * i_hmaster;
  assign hwrite  = i_hwrite  >> i_hmaster;
  assign hbusreq = i_hbusreq >> i_hmaster;

  //assign o_hwdata  = i_hwdata  >> DWIDTH * hmaster_q;
  //assign o_haddr   = i_haddr   >> AWIDTH * i_hmaster;
  //assign o_htrans  = i_htrans  >> 2 * i_hmaster;
  //assign o_hsize   = i_hsize   >> 3 * i_hmaster;
  //assign o_hburst  = i_hburst  >> 3 * i_hmaster;
  //assign o_hwrite  = i_hwrite  >> i_hmaster;
  //assign o_hbusreq = i_hbusreq >> i_hmaster;

  assign o_hrdata  = i_hrdata  << DWIDTH * hmaster_q;
  assign o_hresp   = i_hresp   << 2 * hmaster_q;
  assign hready    = {{(NUM_MSTR-1){1'b0}},hready_d } ;
  assign hready_hold = {NUM_MSTR{hready_d}} & mstr_mask ;

  wav_mux u_hready0 [NUM_MSTR-1:0] (.i_a(hready_int),  .i_b((hready  << i_hmaster)), .i_sel(vldtrans),   .o_z(o_hready));
  wav_mux u_hready1 [NUM_MSTR-1:0] (.i_a(hready_hold), .i_b((hready  << hmaster_q)), .i_sel(vldtrans_q), .o_z(hready_int));

endmodule

module wav_ahb_slave2master #(
   parameter AWIDTH = 32
) (
   input   logic                i_hclk,
   input   logic                i_hreset,
   // AHB slave
   input   logic [AWIDTH-1:0]   i_ahbs_haddr,
   input   logic                i_ahbs_hwrite,
   input   logic                i_ahbs_hsel,
   input   logic [31:0]         i_ahbs_hwdata,
   input   logic [1:0]          i_ahbs_htrans,
   input   logic [2:0]          i_ahbs_hsize,
   input   logic [2:0]          i_ahbs_hburst,
   input   logic                i_ahbs_hreadyin,
   output  logic                o_ahbs_hready,
   output  logic [31:0]         o_ahbs_hrdata,
   output  logic [1:0]          o_ahbs_hresp,

   // AHB Master
   output  logic [AWIDTH-1:0]   o_ahbm_haddr,
   output  logic                o_ahbm_hbusreq,
   input   logic                i_ahbm_hgrant,
   output  logic                o_ahbm_hwrite,
   output  logic [31:0]         o_ahbm_hwdata,
   output  logic [1:0]          o_ahbm_htrans,
   output  logic [2:0]          o_ahbm_hsize,
   output  logic [2:0]          o_ahbm_hburst,
   input   logic                i_ahbm_hready,
   input   logic [31:0]         i_ahbm_hrdata,
   input   logic [1:0]          i_ahbm_hresp
);

  logic vldtrans ;
  logic vldtrans_q ;
  logic wait_grant_q;

   assign vldtrans =  ((o_ahbm_htrans == AHB_TRANS_SEQ) | (o_ahbm_htrans == AHB_TRANS_NONSEQ)) & (o_ahbm_hbusreq == 1'b1);

   always_ff @ (posedge i_hclk, posedge i_hreset) begin
     if(i_hreset) begin
        vldtrans_q   <= '0 ;
        wait_grant_q <= '0 ;
     end
     else begin
        if (vldtrans & i_ahbm_hgrant) begin
           wait_grant_q <= 1'b0 ;
           vldtrans_q   <= 1'b1 ;
        end
        else if (vldtrans & !i_ahbm_hgrant) begin
           wait_grant_q <= 1'b1 ;
           vldtrans_q   <= 1'b1 ;
        end
        else if (vldtrans_q & i_ahbm_hready) begin
           wait_grant_q <= 1'b0 ;
           vldtrans_q   <= 1'b0 ;
        end
     end
   end

   // Master
   assign o_ahbm_haddr   = i_ahbs_haddr;
   assign o_ahbm_hbusreq = i_ahbs_hsel ; //& i_ahbs_hreadyin ;
   assign o_ahbm_hwrite  = i_ahbs_hwrite;
   assign o_ahbm_hwdata  = i_ahbs_hwdata;
   assign o_ahbm_htrans  = i_ahbs_htrans;
   assign o_ahbm_hsize   = i_ahbs_hsize;
   assign o_ahbm_hburst  = i_ahbs_hburst;
   // Slave
   assign o_ahbs_hready  = (vldtrans & !i_ahbm_hgrant) ? 1'b0 : (i_ahbm_hgrant | vldtrans_q) ? i_ahbm_hready  : 1'b1 ;
   assign o_ahbs_hrdata  = i_ahbm_hrdata;
   assign o_ahbs_hresp   = i_ahbm_hresp;

endmodule

module wav_ahb_slave_mux #(
   parameter DWIDTH           = 32,
   parameter AWIDTH           = 32,
   parameter NUM_SLV          = 8,
   parameter SWIDTH           = $clog2(NUM_SLV) + 1
) (
   input   logic                         i_hclk,
   input   logic                         i_hreset,

   input   logic [SWIDTH-1:0]            i_slv_sel,

   input   logic                         i_hbusreq,
   input   logic                         i_hreadyin,
   input   logic [DWIDTH-1:0]            i_hwdata,
   input   logic [AWIDTH-1:0]            i_haddr,
   input   logic [1:0]                   i_htrans,
   input   logic [2:0]                   i_hsize,
   input   logic [2:0]                   i_hburst,
   input   logic                         i_hwrite,
   output  logic                         o_hready,
   output  logic [DWIDTH-1:0]            o_hrdata,
   output  logic [1:0]                   o_hresp,

   output  logic [AWIDTH*NUM_SLV-1:0]    o_haddr ,
   output  logic [NUM_SLV-1:0]           o_hreadyin,
   output  logic [NUM_SLV-1:0]           o_hwrite,
   output  logic [NUM_SLV-1:0]           o_hsel  ,
   output  logic [DWIDTH*NUM_SLV-1:0]    o_hwdata,
   output  logic [2*NUM_SLV-1:0]         o_htrans,
   output  logic [3*NUM_SLV-1:0]         o_hsize ,
   output  logic [3*NUM_SLV-1:0]         o_hburst,
   input   logic [NUM_SLV-1:0]           i_hready,
   input   logic [DWIDTH*NUM_SLV-1:0]    i_hrdata,
   input   logic [2*NUM_SLV-1:0]         i_hresp
);

   logic               vld_trans ;
   logic [SWIDTH-1:0]  slv_sel;
   logic [SWIDTH-1:0]  slv_sel_int;
   logic [SWIDTH-1:0]  slv_sel_q;
   logic [NUM_SLV-1:0] hready ;

   logic               hbusreq_q;
   logic [AWIDTH-1:0]  haddr_q;
   logic [1:0]         htrans_q;
   logic [2:0]         hsize_q;
   logic [2:0]         hburst_q;
   logic               hwrite_q;

   typedef enum logic [1:0] {
      ADDR_PHASE    = 2'h0,
      ADDR_WAIT_RDY = 2'h1,
      DATA_PHASE    = 2'h2,
      WAIT_RDY      = 2'h3
   } state_t;

   state_t state_q, state_d ;

   assign slv_sel_int  = {SWIDTH{i_hbusreq}} & i_slv_sel ;
   assign hready       = i_hready >> 1*(i_slv_sel-'b1);
   assign vld_trans    = i_hbusreq & i_hreadyin & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
        state_q   <= ADDR_PHASE;
      end
      else begin
        state_q   <= state_d ;
      end
   end

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
        hbusreq_q <= '0 ;
        haddr_q   <= '0 ;
        htrans_q  <= '0 ;
        hsize_q   <= '0 ;
        hburst_q  <= '0 ;
        hwrite_q  <= '0 ;
        slv_sel_q <= '0;
      end
      else begin
        slv_sel_q <= slv_sel ;
        if((state_q != ADDR_WAIT_RDY) & (state_d == ADDR_WAIT_RDY)) begin
           hbusreq_q <= i_hbusreq ;
           haddr_q   <= i_haddr   ;
           htrans_q  <= i_htrans  ;
           hsize_q   <= i_hsize   ;
           hburst_q  <= i_hburst  ;
           hwrite_q  <= i_hwrite  ;
        end
      end
   end

   always_comb begin
      state_d = state_q ;
      slv_sel = slv_sel_q;
      case(state_q)
         ADDR_PHASE : begin
            if(vld_trans & hready[0]) begin
               state_d = DATA_PHASE ;
               slv_sel = slv_sel_int;
            end
         end
         DATA_PHASE : begin
            if (o_hready && vld_trans && hready[0]) begin
               state_d = DATA_PHASE;
               slv_sel = slv_sel_int ;
            end
            else if(o_hready && vld_trans && ~hready[0]) begin
               state_d = ADDR_WAIT_RDY;
               slv_sel = slv_sel_int ;
            end
            else if(o_hready) begin
               state_d = ADDR_PHASE;
               slv_sel = slv_sel_int ;
            end
            else begin
               state_d = WAIT_RDY;
            end
         end
         ADDR_WAIT_RDY: begin
            if(hready[0] == 1) begin
               state_d = DATA_PHASE ;
            end
         end
         WAIT_RDY : begin
            if (o_hready && vld_trans) begin
               state_d = DATA_PHASE;
               slv_sel = slv_sel_int ;
            end
            else if (o_hready ) begin
               state_d = ADDR_PHASE;
               slv_sel = slv_sel_int;
            end
         end
      endcase
   end

   assign o_hsel       = (state_q == ADDR_WAIT_RDY) ?  i_hbusreq << 1*(slv_sel_q - 'b1) : i_hbusreq << 1*(slv_sel_int - 'b1) ;
   assign o_hreadyin   = {NUM_SLV{(&i_hready)}} ;
   assign o_haddr      = (state_q == ADDR_WAIT_RDY) ?  {NUM_SLV{haddr_q  }} : {NUM_SLV{i_haddr  }} ;
   assign o_hwrite     = (state_q == ADDR_WAIT_RDY) ?  {NUM_SLV{hwrite_q }} : {NUM_SLV{i_hwrite }} ;
   assign o_htrans     = (state_q == ADDR_WAIT_RDY) ?  {NUM_SLV{htrans_q }} : {NUM_SLV{i_htrans }} ;
   assign o_hsize      = (state_q == ADDR_WAIT_RDY) ?  {NUM_SLV{hsize_q  }} : {NUM_SLV{i_hsize  }} ;
   assign o_hburst     = (state_q == ADDR_WAIT_RDY) ?  {NUM_SLV{hburst_q }} : {NUM_SLV{i_hburst }} ;
   assign o_hwdata     = {NUM_SLV{i_hwdata }} ;

   assign o_hready     = (state_q == ADDR_WAIT_RDY) ? '0 : (state_q != ADDR_PHASE) & (|slv_sel_q) ? i_hready >> 1*(slv_sel_q-'b1) : hready[0] ; // 1'b1;
   assign o_hrdata     = (|slv_sel_q) ? i_hrdata >> DWIDTH*(slv_sel_q-'b1) : '0;
   assign o_hresp      = (|slv_sel_q) ? i_hresp  >> 2*(slv_sel_q-'b1)      : '0;

endmodule

module wav_ahb_slave #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(
   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic                i_hsel,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   input   logic                i_hreadyin,
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp,

   output  logic                o_write,
   output  logic                o_read,
   output  logic [AWIDTH-1:0]   o_addr,
   output  logic [DWIDTH-1:0]   o_wdata,
   input   logic [DWIDTH-1:0]   i_rdata,
   input   logic                i_error,
   input   logic                i_ready
);

   logic [AWIDTH-1:0] addr_d;
   logic [AWIDTH-1:0] addr_q;
   logic write_d;
   logic write_q;
   logic read_d;
   logic read_q;
   logic [DWIDTH-1:0] wdata_q;
   //logic [DWIDTH-1:0] rdata_q;
   logic [DWIDTH-1:0] wdata_d;
   logic wr_q;

   assign write_d  =  i_hwrite & i_hsel & i_hreadyin & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));
   assign read_d   = ~i_hwrite & i_hsel & i_hreadyin & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));
   assign addr_d   =             i_hsel & i_hreadyin & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ)) ? i_haddr : addr_q;

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset) begin
         addr_q  <= '0;
         write_q <= '0;
         read_q  <= '0;
         wr_q    <= '0;
         wdata_q <= '0;
         //rdata_q <= '0;
      end
      else begin
         // Write or Read to start the transaction, ready to keep the command
         // on the output. A slave must only sample the address and control
         // signals and hsel when HREADY is asserted.
         if (i_ready || write_d || read_d) begin
            addr_q  <= addr_d;
            write_q <= write_d;
            read_q  <= read_d;
         end

         // Write signal delayed one cycle to align with data
         wr_q <= write_d;

         // Capture data if not ready and previous cycle was a write
         if (wr_q && !i_ready) begin
            wdata_q <= i_hwdata;
         end
         //if (read_d) begin
         //   rdata_q <= i_rdata;
         //end
      end
   end

   // Previous cycle was not command cycle, but slave may not be ready so
   // select the captured data
   assign wdata_d = !wr_q ? wdata_q : i_hwdata;

   // Delay the write address by one cycle to align to data
   assign o_addr   = addr_q;
   assign o_write  = write_q;
   assign o_read   = read_q;
   assign o_wdata  = wdata_d;
   assign o_hrdata = i_rdata;
   assign o_hready = i_ready;
   assign o_hresp  = (i_error==1'b0) ? AHB_RESP_OK : AHB_RESP_ERROR ;

endmodule

module wav_default_ahb_slave #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(
   input   logic                i_hclk,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic                i_hsel,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   input   logic                i_hreadyin,
   output  logic                o_hready,
   output  logic [DWIDTH-1:0]   o_hrdata,
   output  logic [1:0]          o_hresp
);

   logic vld_trans;
   logic [1:0]          hresp_q;

   assign vld_trans  = i_hreadyin & i_hsel & ((i_htrans == AHB_TRANS_SEQ) | (i_htrans == AHB_TRANS_NONSEQ));

   always_ff @(posedge i_hclk, posedge i_hreset) begin
      if (i_hreset)
         hresp_q <= AHB_RESP_OK ;
      else
         if(vld_trans)
            hresp_q <= AHB_RESP_ERROR ;
         else
            hresp_q <= AHB_RESP_OK ;
   end

   assign o_hrdata = '0 ;
   assign o_hready = '1; //ready_q;
   assign o_hresp  = hresp_q ;

endmodule

/*
module wav_apb2ahb #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(

   // APB Slave
   input   logic [AWIDTH-1:0]   i_apbs_paddr,
   input   logic                i_apbs_pwrite,
   input   logic                i_apbs_psel,
   input   logic                i_apbs_penable,
   input   logic [DWIDTH-1:0]   i_apbs_pwdata,
   output  logic                o_apbs_pready,
   output  logic [DWIDTH-1:0]   o_apbs_prdata,
   output  logic                o_apbs_pslverr,

   // AHB Master
   output  logic [AWIDTH-1:0]   o_ahbm_haddr,
   output  logic                o_ahbm_hwrite,
   output  logic                o_ahbm_hsel,
   output  logic [DWIDTH-1:0]   o_ahbm_hwdata,
   output  logic [1:0]          o_ahbm_htrans,
   output  logic [2:0]          o_ahbm_hsize,
   output  logic [2:0]          o_ahbm_hburst,
   output  logic [3:0]          o_ahbm_hprot,
   input   logic                i_ahbm_grant,
   input   logic                i_ahbm_hready,
   input   logic [DWIDTH-1:0]   i_ahbm_hrdata,
   input   logic [1:0]          i_ahbm_hresp

);

   assign o_apbs_pready  = i_ahbm_hready & i_ahbm_grant;
   assign o_apbs_prdata  = i_ahbm_hrdata;
   assign o_apbs_pslverr = i_ahbm_hresp[0];

   assign o_ahbm_hwdata  = i_apbs_pwdata;
   assign o_ahbm_haddr   = i_apbs_paddr;
   assign o_ahbm_hwrite  = i_apbs_pwrite;
   assign o_ahbm_hsel    = i_apbs_psel;
   assign o_ahbm_htrans  = i_apbs_psel? AHB_TRANS_NONSEQ : AHB_TRANS_IDLE;
   assign o_ahbm_hsize   = AHB_SIZE_WORD;
   assign o_ahbm_hburst  = AHB_BURST_INCR;
   assign o_ahbm_hprot   = 4'b0001;     // Data access, No Buffer, No Cache

endmodule
*/

module wav_apb2ahb # (
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(
   input  logic                 i_pclk,
   input  logic                 i_preset,
   input  logic                 i_psel,
   input  logic                 i_penable,
   input  logic                 i_pwrite,
   input  logic [DWIDTH-1:0]    i_pwdata,
   input  logic [AWIDTH-1:0]    i_paddr,
   output logic [DWIDTH-1:0]    o_prdata,
   output logic                 o_pready,
   output logic                 o_pslverr,

   output logic                 o_hsel,
   output logic [AWIDTH-1:0]    o_haddr,
   output logic                 o_hwrite,
   output logic [2:0]           o_hsize,
   output logic [2:0]           o_hburst,
   output logic [3:0]           o_hprot,
   output logic [1:0]           o_htrans,
   output logic                 o_hmstlock,
   output logic [DWIDTH-1:0]    o_hwdata,
   output logic                 o_hreadyin,
   input  logic                 i_hgrant,
   input  logic                 i_hreadyout,
   input  logic [DWIDTH-1:0]    i_hrdata,
   input  logic [1:0]           i_hresp

);

   logic [1:0] data_naddr_phase;
   logic [1:0] data_naddr_phase_in;

   logic       pready_in;
   logic       pslverr_in;

   always @(posedge i_pclk or posedge i_preset) begin
     if (i_preset) begin
       data_naddr_phase      <= 2'b00;
     end else begin
       data_naddr_phase      <= i_psel ? data_naddr_phase_in : 1'b0;
     end
   end

   always_comb begin
     data_naddr_phase_in         = data_naddr_phase;
     pready_in                   = 1'b0;
     pslverr_in                  = 1'b0;
     case (data_naddr_phase)
       2'b00 : begin  // IDLE -> SETUP / ADDRESS PHASE
         if (i_psel & i_hreadyout & i_hgrant) begin
           data_naddr_phase_in   = 2'b01;
         end else begin
           data_naddr_phase_in   = 2'b00;
         end
       end
       2'b01 : begin  // ACCESS / DATA PHASE
         if (i_penable & (i_hreadyout | (i_hresp == AHB_RESP_ERROR))) begin
           data_naddr_phase_in   = 2'b11;
           pready_in             = 1'b1;
           pslverr_in            = i_hresp[0];
         end else begin
           data_naddr_phase_in   = 2'b01;
         end
       end
       2'b11 : begin  // APB TERMINATE PHASE
         if (~i_penable) begin
           data_naddr_phase_in   = 2'b00;
         end else begin
           data_naddr_phase_in   = 2'b11;
         end
       end
       default : begin
         data_naddr_phase_in     = 2'b00;
       end
     endcase
   end

   generate
     if (DWIDTH < 9) begin : gen_byte
       assign o_hsize = 3'b000; // 32 bits always
     end else if (DWIDTH < 17) begin : gen_half_word
       assign o_hsize = 3'b001; // 32 bits always
     end else begin : gen_word
       assign o_hsize = 3'b010; // 32 bits always
     end
   endgenerate

   assign o_hsel      = i_psel  & ~data_naddr_phase[0] ; //& i_hreadyout;
   assign o_haddr     = i_paddr;
   assign o_hwrite    = i_psel & i_pwrite & ~data_naddr_phase[0];
   assign o_hburst    = 3'b000;  // APB does not burst
   assign o_hprot     = 4'b0011; //  uncacheable, unbufferable, privileged, data access
   assign o_htrans    = 2'b10;   //  nonsequential
   assign o_hmastlock = 1'b0;
   assign o_hwdata    = i_pwdata;
   assign o_hreadyin  = 1'b1; /*i_hreadyout;*/
   assign o_prdata    = i_hrdata;
   assign o_pready    = pready_in;
   assign o_pslverr   = pslverr_in;

endmodule

module wav_axi2apb (

   input  wire                 i_clk,      //same clock for both sides
   input  wire                 i_reset,

   //Write
   input  wire [3:0]           i_awid,
   input  wire [39:0]          i_awaddr,
   input  wire [7:0]           i_awlen,      //must be 1 or err
   input  wire [2:0]           i_awsize,     //must be 'b010 or err
   input  wire [2:0]           i_awprot,
   input  wire                 i_awvalid,
   input  wire [3:0]           i_awqos,
   input  wire [3:0]           i_awregion,
   input  wire [3:0]           i_awcache,
   input  wire                 i_awlock,
   input  wire [1:0]           i_awburst,
   output wire                 o_awready,

   input  wire [63:0]          i_wdata,
   input  wire [7:0]           i_wstrb,      //If not all 1's, will err
   input  wire                 i_wvalid,
   input  wire                 i_wlast,
   output wire                 o_wready,

   output wire [3:0]           o_bid,        //reflects awid
   output wire [1:0]           o_bresp,
   output wire                 o_bvalid,
   input  wire                 i_bready,

   //Read
   input  wire [3:0]           i_arid,
   input  wire [39:0]          i_araddr,
   input  wire [7:0]           i_arlen,      //must be 1 or err
   input  wire [2:0]           i_arsize,     //must be 'b010 or err
   input  wire [2:0]           i_arprot,
   input  wire                 i_arvalid,
   input  wire [3:0]           i_arqos,
   input  wire [3:0]           i_arregion,
   input  wire [3:0]           i_arcache,
   input  wire                 i_arlock,
   input  wire [1:0]           i_arburst,
   output wire                 o_arready,
   output wire [3:0]           o_rid,        //reflects arid
   output wire [63:0]          o_rdata,
   output wire [1:0]           o_rresp,
   output wire                 o_rvalid,
   output wire                 o_rlast,
   input  wire                 i_rready,

   //APB
   output reg  [39:0]          o_paddr,
   output reg  [31:0]          o_pwdata,
   output reg                  o_pwrite,
   output reg                  o_psel,
   output reg                  o_penable,
   input  wire [31:0]          i_prdata,
   input  wire                 i_pready,
   input  wire                 i_pslverr,

   input  wire                 i_clr_err,
   output wire [7:0]           o_err_cond

);

   localparam        RESET         = 3'd0,
                     WRITE_ADDR    = 3'd1,
                     WRITE_DATA    = 3'd2,
                     WRITE_RESP    = 3'd3,
                     READ_ADDR     = 3'd4,
                     READ_DATA     = 3'd5,
                     READ_RESP     = 3'd6;

   reg  [2:0]        state, nstate;
   reg psel_in;

   reg  [39:0]       awaddr_reg;
   reg  [3:0]        awid_reg;
   reg               awready_reg;
   reg               aw_captured;
   reg  [2:0]        prot_in;
   reg  [2:0]        prot_reg;

   reg  [31:0]       wdata_reg;
   reg               wready_reg;
   reg               w_captured;

   reg  [39:0]       araddr_reg;
   reg  [3:0]        arid_reg;
   reg               arready_reg;
   reg               ar_captured;

   reg  [63:0]       rdata_reg;
   reg               rready_reg;
   reg               r_captured;
   reg  [63:0]       rdata_reg_in;

   wire              clear_w;
   wire              clear_r;

   wire              aw_update;
   wire              w_update;
   wire              ar_update;
   wire              r_update;

   reg  [39:0]       paddr_in;
   reg  [31:0]       pwdata_in;
   reg               pwrite_in;
   reg               hsel_in;
   reg  [1:0]        htrans_in;

   reg  [7:0]        err_cond_reg;
   wire [7:0]        err_cond_reg_in;
   wire              clr_err_ff2;
   wire [3:0]        wstrb_sel;

   wav_demet_r u_demet (.i_clk(i_clk), .i_rst(i_reset), .i_d(i_clr_err), .o_q(clr_err_ff2));

   always_ff @(posedge i_clk or posedge i_reset) begin
     if (i_reset) begin
       awaddr_reg      <= 40'd0;
       awready_reg     <= 1'b0;
       aw_captured     <= 1'b0;
       awid_reg        <= 4'd0;

       wdata_reg       <= 32'd0;
       wready_reg      <= 1'b0;
       w_captured      <= 1'b0;

       araddr_reg      <= 40'd0;
       arready_reg     <= 1'b0;
       ar_captured     <= 1'b0;
       arid_reg        <= 4'd0;

       rdata_reg       <= 64'd0;

       err_cond_reg    <= 8'd0;
     end else begin
       awaddr_reg      <= aw_update ? i_awaddr : awaddr_reg;
       awready_reg     <= aw_captured || aw_update ? 1'b0 : 1'b1;
       aw_captured     <= clear_w ? 1'b0 : aw_update ? 1'b1 : aw_captured;
       awid_reg        <= aw_update ? i_awid : awid_reg;

       wdata_reg       <= w_update ? (awaddr_reg[2] ? i_wdata[63:32] : i_wdata[31:0]) : wdata_reg;
       wready_reg      <= w_captured || w_update ? 1'b0 : 1'b1;
       w_captured      <= clear_w ? 1'b0 : w_update ? 1'b1 : w_captured;

       araddr_reg      <= ar_update ? i_araddr : araddr_reg;
       arready_reg     <= ar_captured || ar_update ? 1'b0 : 1'b1;
       ar_captured     <= clear_r ? 1'b0 : ar_update ? 1'b1 : ar_captured;
       arid_reg        <= ar_update ? i_arid : arid_reg;

       rdata_reg       <= rdata_reg_in;

       err_cond_reg    <= clr_err_ff2 ? 8'h00 : err_cond_reg_in;
     end
   end

   //clr_err will override, can also just set it high to disable the errors
   //0 - ahb hresp
   //1 - awlen not 0
   //2 - awsize not word
   //3 - wstrb not all 1s
   //4 - arlen not 0
   //5 - arsize not word
   assign wstrb_sel = awaddr_reg[2] ? i_wstrb[7:4] : i_wstrb[3:0];
   assign err_cond_reg_in[0] = ((state == READ_ADDR) || (state == WRITE_ADDR)) && i_pready ? i_pslverr : err_cond_reg[0];
   assign err_cond_reg_in[1] = aw_update ? (i_awlen != 8'd0)     : err_cond_reg[1];
   assign err_cond_reg_in[2] = aw_update ? (i_awsize != 3'b010)  : err_cond_reg[2];
   assign err_cond_reg_in[3] = w_update  ? (wstrb_sel != 4'b1111)  : err_cond_reg[3];
   assign err_cond_reg_in[4] = w_update  ? ~i_wlast : err_cond_reg[4];
   assign err_cond_reg_in[5] = ar_update ? (i_arlen != 8'd0)     : err_cond_reg[5];
   assign err_cond_reg_in[6] = ar_update ? (i_arsize != 3'b010)  : err_cond_reg[6];
   assign err_cond_reg_in[7] = r_update ? ~o_rlast : err_cond_reg[7];

   assign err_cond = err_cond_reg;

   assign aw_update  = o_awready & i_awvalid;
   assign w_update   = o_wready  & i_wvalid;

   assign ar_update  = o_arready & i_arvalid;
   assign r_update  = i_rready & o_rvalid;

   assign o_awready = awready_reg;
   assign o_wready  = wready_reg;

   assign o_arready = arready_reg;

   assign o_bid      = awid_reg;
   assign o_bresp    = (|err_cond_reg[4:0]) ? 2'b10 : 2'b00;
   assign o_bvalid   = state == WRITE_RESP;

   assign o_rid      = arid_reg;
   assign o_rresp    = (|err_cond_reg[7:5]) || err_cond_reg[0] ? 2'b10 : 2'b00;
   assign o_rvalid   = state == READ_RESP;
   assign o_rdata    = {rdata_reg};
   assign o_rlast    = 1'b1;

   always_ff @(posedge i_clk or posedge i_reset) begin
     if(i_reset) begin
       state       <= RESET;
       o_paddr     <= 40'd0;
       o_pwdata    <= 32'd0;
       o_pwrite    <= 1'b0;
       o_psel      <= 1'b0;
     end else begin
       state       <= nstate;
       o_paddr     <= paddr_in;
       o_pwdata    <= pwdata_in;
       o_pwrite    <= pwrite_in;
       o_psel      <= psel_in;
     end
   end

   assign clear_w = (state == WRITE_ADDR) && (nstate == WRITE_RESP);
   assign clear_r = (state == READ_ADDR)  && (nstate == READ_RESP);

   always @(*) begin
     nstate            = state;

     paddr_in          = o_paddr;
     o_penable         = 1'b0;

     pwdata_in         = o_pwdata;
     pwrite_in         = o_pwrite;
     psel_in           = o_psel;

     rdata_reg_in      = rdata_reg;

     case(state)
       RESET : begin
         if(aw_captured && w_captured) begin
           paddr_in    = awaddr_reg;
           pwdata_in   = wdata_reg;
           pwrite_in   = 1'b1;
           psel_in     = 1'b1;
           nstate      = WRITE_ADDR;
         end else if (ar_captured) begin
           paddr_in    = araddr_reg;
           pwdata_in   = 32'd0;
           pwrite_in   = 1'b0;
           psel_in     = 1'b1;
           nstate      = READ_ADDR;
         end
       end

       //
       WRITE_ADDR : begin
         o_penable  = 1'b1;
         psel_in  = ~i_pready;
         pwrite_in  = ~i_pready;
         if(i_pready) begin
           nstate      = WRITE_RESP;
         end
       end

       WRITE_RESP : begin
         if(i_bready) begin
           nstate      = RESET;
         end
       end

       READ_ADDR : begin
         o_penable  = 1'b1;
         psel_in  = ~i_pready;
         rdata_reg_in  = araddr_reg[2] ? {i_prdata, 32'h00000000} : {32'h00000000, i_prdata};
         if(i_pready) begin
           nstate      = READ_RESP;
         end
       end

       default : begin
         if(i_rready) begin
           nstate        = RESET;
         end
       end

     endcase
   end

endmodule

module wav_ahb_monitor #(
   parameter AWIDTH = 32,
   parameter DWIDTH = 32
)(
   input   logic                i_hclk,
   input   logic                i_hbusreq,
   input   logic                i_hreset,
   input   logic [AWIDTH-1:0]   i_haddr,
   input   logic                i_hwrite,
   input   logic [DWIDTH-1:0]   i_hwdata,
   input   logic [1:0]          i_htrans,
   input   logic [2:0]          i_hsize,
   input   logic [2:0]          i_hburst,
   input   logic                i_hready,
   input   logic [DWIDTH-1:0]   i_hrdata,
   input   logic [1:0]          i_hresp
);
   logic hclk_g, hclk_dly;
   assign #2ps hclk_dly = i_hclk;

   assign hclk_g = hclk_dly & i_hbusreq;

`ifdef WAV_AHB_SVA
   //Error Response followed by Idle Trans
   property err_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_hresp == 1) ##1 (i_hresp == 1) |=> (i_htrans == 0);
   endproperty

   //Split Response followed by Idle Trans
   property split_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_hresp == 3) ##1 (i_hresp == 3) |=> (i_htrans == 0);
   endproperty

   //Retry Response followed by Idle Trans
   property retry_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_hresp == 2) ##1 (i_hresp == 2) |=> (i_htrans == 0);
   endproperty

   //NONSEQ (BURST = 0) should not follow BUSY
   property no_busy_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_hburst == 0) |=> (i_htrans != 1);
   endproperty

   //Busy followed by Idle
   property busy_idle_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_htrans == 1) ##1 (i_htrans == 0) |-> ($past(i_hburst, 1) == 1);
   endproperty

   //Okay Resp for Idle Trans
   property idle_okay_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_htrans == 0) |=> (i_hresp == 0);
   endproperty

   //Busy on Address and Write Data
   property busy_write_p;
      @(posedge i_hclk) disable iff(i_hreset)
         ((i_htrans == 1) && (i_hwrite)) ##1 (i_htrans != 0) |=> (($past(i_hwdata, 1) == $past(i_hwdata, 2)) &&
                ($past(i_haddr, 1) == $past(i_haddr, 2)));
   endproperty

   //Busy on Address and Read Data
   property busy_read_p;
      @(posedge i_hclk) disable iff(i_hreset)
         ((i_htrans == 1) && (!i_hwrite)) ##1 (i_htrans != 0) |=> (($past(i_hrdata, 1) == $past(i_hrdata, 2)) &&
                ($past(i_haddr, 1) == $past(i_haddr, 2)));
   endproperty

   // 1KB Boundry Check
   property kb_boundry_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_htrans == 3) |-> (i_haddr[10:0] != 11'b1_00000_00000);
   endproperty

   //Address Check for INCR/INCRx
   property incr_addr_p;
      @(posedge i_hclk) disable iff(i_hreset)
         (i_htrans == 3) && ((i_hburst == 1)||(i_hburst == 3)||(i_hburst == 5)||(i_hburst == 7)) &&
                ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |-> (i_haddr == ($past(i_haddr, 1) + 2**i_hsize));
   endproperty

   //Address Check for WRAP4 Byte
   property wrap4_size0_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 2) && (i_hsize == 0) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[1:0] == ($past(i_haddr[1:0], 1) + 1)) && (i_haddr[31:2] == $past(i_haddr[31:2], 1)));
   endproperty

   //Address Check for WRAP4 Halfword
   property wrap4_size1_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 2) && (i_hsize == 1) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[2:1] == ($past(i_haddr[2:1], 1) + 1)) && (i_haddr[31:3] == $past(i_haddr[31:3], 1)));
   endproperty

   //Address Check for WRAP4 Word
   property wrap4_size2_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 2) && (i_hsize == 2) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[3:2] == ($past(i_haddr[3:2], 1) + 1)) && (i_haddr[31:4] == $past(i_haddr[31:4], 1)));
   endproperty

   //Address Check for WRAP8 Byte
   property wrap8_size0_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 4) && (i_hsize == 0) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[2:0] == ($past(i_haddr[2:0], 1) + 1)) && (i_haddr[31:3] == $past(i_haddr[31:3], 1)));
   endproperty

   //Address Check for WRAP8 Halfword
   property wrap8_size1_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 4) && (i_hsize == 1) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[3:1] == ($past(i_haddr[3:1], 1) + 1)) && (i_haddr[31:4] == $past(i_haddr[31:4], 1)));
   endproperty

   //Address Check for WRAP8 Word
   property wrap8_size2_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 4) && (i_hsize == 2) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[4:2] == ($past(i_haddr[4:2], 1) + 1)) && (i_haddr[31:5] == $past(i_haddr[31:5], 1)));
   endproperty

   //Address Check for WRAP16 Byte
   property wrap16_size0_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 6) && (i_hsize == 0) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[3:0] == ($past(i_haddr[3:0], 1) + 1)) && (i_haddr[31:4] == $past(i_haddr[31:4], 1)));
   endproperty

   //Address Check for WRAP16 Halfword
   property wrap16_size1_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 6) && (i_hsize == 1) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[4:1] == ($past(i_haddr[4:1], 1) + 1)) && (i_haddr[31:5] == $past(i_haddr[31:5], 1)));
   endproperty

   //Address Check for WRAP16 Word
   property wrap16_size2_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         (i_htrans == 3) && (i_hburst == 6) && (i_hsize == 2) && ($past(i_htrans, 1) != 1) && ($past(i_hready, 1)) |->
           ((i_haddr[5:2] == ($past(i_haddr[5:2], 1) + 1)) && (i_haddr[31:6] == $past(i_haddr[31:6], 1)));
   endproperty

   // Address Boundry Aligned for Halfword
   property size1_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 1 |-> i_haddr[0] == 0;
   endproperty

   // Address Boundry Aligned for Word
   property size2_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 2 |-> i_haddr[1:0] == 0;
   endproperty

   // Address Boundry Aligned for Wordx2
   property size3_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 3 |-> i_haddr[2:0] == 0;
   endproperty

   // Address Boundry Aligned for Wordx4
   property size4_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 4 |-> i_haddr[3:0] == 0;
   endproperty

   // Address Boundry Aligned for Wordx8
   property size5_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 5 |-> i_haddr[4:0] == 0;
   endproperty

   // Address Boundry Aligned for Wordx16
   property size6_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 6 |-> i_haddr[5:0] == 0;
   endproperty

   // Address Boundry Aligned for Wordx32
   property size7_addr_p;
      @(posedge hclk_g) disable iff(i_hreset)
         i_hsize == 7 |-> i_haddr[6:0] == 0;
   endproperty

   ERROR          : assert property(err_p);
   RETRY          : assert property(retry_p);
   SPLIT          : assert property(split_p);
   NO_BUSY        : assert property(no_busy_p);
   BUSY_IDLE      : assert property(busy_idle_p);
   IDLE_OK        : assert property(idle_okay_p);
   BUSY_WRITE     : assert property(busy_write_p);
   BUSY_READ      : assert property(busy_read_p);
   ONE_KB         : assert property(kb_boundry_p);
   INCR_ADDR      : assert property(incr_addr_p);
   WRAP4_SIZE0    : assert property(wrap4_size0_addr_p);
   WRAP4_SIZE1    : assert property(wrap4_size1_addr_p);
   WRAP4_SIZE2    : assert property(wrap4_size2_addr_p);
   WRAP8_SIZE0    : assert property(wrap8_size0_addr_p);
   WRAP8_SIZE1    : assert property(wrap8_size1_addr_p);
   WRAP8_SIZE2    : assert property(wrap8_size2_addr_p);
   WRAP16_SIZE0   : assert property(wrap16_size0_addr_p);
   WRAP16_SIZE1   : assert property(wrap16_size1_addr_p);
   WRAP16_SIZE2   : assert property(wrap16_size2_addr_p);

   SIZE1_ADDR_BOUD: assert property(size1_addr_p);
   SIZE2_ADDR_BOUD: assert property(size2_addr_p);
   SIZE3_ADDR_BOUD: assert property(size3_addr_p);
   SIZE4_ADDR_BOUD: assert property(size4_addr_p);
   SIZE5_ADDR_BOUD: assert property(size5_addr_p);
   SIZE6_ADDR_BOUD: assert property(size6_addr_p);
   SIZE7_ADDR_BOUD: assert property(size7_addr_p);

`endif

endmodule
