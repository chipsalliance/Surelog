//----------------------------------------------------------------------
// Srdy/drdy round-robin arbiter
// but without the one cycle decision delay.
//
// This component supports multiple round-robin modes:
//
// Mode 0 : Each input gets a single cycle, regardless of data
//          availability.  This mode functions like a TDM
//          demultiplexer.  Output flow control will cause the
//          component to stall, so that inputs do not miss their
//          turn due to flow control.
// Mode 0 fast arb : Each input gets a single grant. If the
//          output is not ready (p_drdy deasserted), then the
//          machine will hold on that particular input until it
//          receives a grant.  Once a single token has been
//          accepted the machine will round-robin arbitrate.
//          When there are no requests the machine returns to
//          its default state.
// Mode 1 : Each input can transmit for as long as it has data.
//          When input deasserts, device will begin to hunt for a
//          new input with data.
// Mode 2 : Continue to accept input until the incoming data
//          matches a particular "end pattern".  The end pattern
//          is provided on the c_rearb (re-arbitrate) input.  When
//          c_rearb is high, will hunt for new inputs on next clock.
//
// This component also supports two arbitration modes: slow and fast.
// slow rotates the grant from requestor to requestor cycle by cycle,
// so each requestor gets serviced at most once every #inputs cycles.
// This can be useful for producing a TDM-type interface, however
// requestors may be delayed waiting for the grant to come around even
// if there are no other requestors.
//
// Fast mode immediately grants the highest-priority requestor, however
// it is drdy-noncompliant (drdy will not be asserted until srdy is
// asserted).
//
// Naming convention: c = consumer, p = producer, i = internal interface
//----------------------------------------------------------------------
//  Author: Frank Wang
//
// This block is uncopyrighted and released into the public domain.
//----------------------------------------------------------------------
`ifndef _SD_RRMUX_V_
`define _SD_RRMUX_V_
// Clocking statement for synchronous blocks.  Default is for
// posedge clocking and positive async reset
`ifndef SDLIB_CLOCKING 
 `define SDLIB_CLOCKING posedge clk or posedge reset
`endif

// delay unit for nonblocking assigns, default is to #1 
`ifndef SDLIB_DELAY 
 `define SDLIB_DELAY #1  
`endif

module sd_rrmux
  #(parameter width=8,
    parameter inputs=2,
    parameter mode=0,
    parameter fast_arb=1)
  (
   input               clk,
   input               reset,
  
   input [(width*inputs)-1:0] c_data,
   input [inputs-1:0]      c_srdy,
   output  [inputs-1:0]    c_drdy,
   input                   c_rearb,  // for use with mode 2 only

   output reg [width-1:0]  p_data,
   output [inputs-1:0]     p_grant,
   output reg              p_srdy,
   input                   p_drdy
   );
  // bmp for the c_srdy that has just been granted and accepted by p_drdy
  reg [inputs-1:0]    just_granted;
  //control path, transit only after p_drdy ("accepted" part).
  reg [inputs-1:0]    to_be_granted; 
  //for data path, regardless of p_drdy, help to remove combo loops
  //rational being, when p_drdy==1'b0, it doesn't matter what p_data is.
  reg [inputs-1:0]    to_tx_data; 

  wire [width-1:0]     rr_mux_grid [0:inputs-1];
  reg 		       rr_locked;
  reg nxt_rr_locked;   // ri lint_check_waive NOT_DRIVEN
  genvar               i;
  integer              j;

  assign c_drdy = to_be_granted & {inputs{p_drdy}};
  assign p_grant = to_be_granted;

  function [inputs-1:0] nxt_grant;
    input [inputs-1:0] cur_grant;
    input [inputs-1:0] cur_req;
    input              cur_accept;
    reg [inputs-1:0]   msk_req;
    reg [inputs-1:0]   tmp_grant;
    reg [inputs-1:0]   tmp_grant2;

    begin
// scenario: 
// in cycle 0, src 1 is granted and accepted by p_drdy,
// in cycle 1, src 3 is requesting, but p_drdy is 0, so c_data3 is presented at p_data with p_srdy
// in cycle 2, if src 2 comes in requesting, should hold src 3 at p_data till p_drdy, 
//             src 2 will only participate in next round arb.
// the way is in this scenario, pretend src2 is the just_granted in cycle 1.
// so arbitration is excercies in two cases: (1): p_drdy, 
// or (2) p_not_drdy, the immediate next c_not_srdy, but at least one remote c_srdy
      
      msk_req = cur_req & ~((cur_grant - 1) | cur_grant);
      tmp_grant = msk_req & (~msk_req + 1);
      tmp_grant2 = cur_req & (~cur_req + 1);

      if(cur_accept)begin
          if (msk_req != 0) nxt_grant = tmp_grant;
          else nxt_grant = tmp_grant2;
      //end else if (rem_neighbor_rearb) begin
      end else if (| cur_req) begin
          if (msk_req != 0) nxt_grant = {tmp_grant[0],tmp_grant[inputs-1:1]};
          else nxt_grant = {tmp_grant2[0],tmp_grant2[inputs-1:1]};
      end else begin
          nxt_grant = cur_grant;
      end
    end
  endfunction
  
  generate
    for (i=0; i<inputs; i=i+1)
      begin : grid_assign
        //assign rr_mux_grid[i] = c_data >> (i*width);
        assign rr_mux_grid[i] = c_data[i*width+width-1 : i*width]; 
      end

    if (mode == 2)
      begin : tp_gen
        always @*
          begin
            nxt_rr_locked = rr_locked;

            if ((c_srdy & just_granted) & (!rr_locked))
              nxt_rr_locked = 1;
            else if ((c_srdy & just_granted & c_rearb))
              nxt_rr_locked = 0;
          end

        always @(`SDLIB_CLOCKING)
          begin
            if (reset)
              rr_locked <= 0;
            else
              rr_locked <= nxt_rr_locked;
          end
      end // block: tp_gen
  endgenerate

//  always @*
//    begin
//      p_data = 0;
//      p_srdy = 0;
//      for (j=0; j<inputs; j=j+1)
//        if (just_granted[j])
//          begin
//            p_data = rr_mux_grid[j];
//            p_srdy = c_srdy[j];
//          end
//    end
always @(*) begin
    p_srdy = | c_srdy;

    p_data = {width{1'b0}};
    for (j=0; j<inputs; j=j+1) begin
        if (to_tx_data[j]) begin
            p_data = rr_mux_grid[j];
            p_srdy = c_srdy[j];
        end
    end
end
  
  always @*
    begin
      to_tx_data = just_granted;
      to_be_granted = just_granted;
      if ((mode ==  1) & (|(c_srdy & just_granted)))
        to_be_granted = just_granted;
      else if ((mode == 0) && !fast_arb)begin
        to_be_granted=p_drdy?{just_granted[0],just_granted[inputs-1:1]}:just_granted;
        to_tx_data={just_granted[0],just_granted[inputs-1:1]};
      end
      //else if ((mode == 0) && |(just_granted & c_srdy) && !p_drdy && fast_arb)
      //  to_be_granted = just_granted;
      else if ((mode == 2) & (nxt_rr_locked | (|(c_srdy & just_granted))))
        to_be_granted = just_granted;
      else if (fast_arb) begin
        to_be_granted=nxt_grant (just_granted, c_srdy, p_drdy);
        to_tx_data = nxt_grant(just_granted, c_srdy, 1'b1);
      end
      else begin
        to_be_granted=p_drdy?{just_granted[0],just_granted[inputs-1:1]}:just_granted;
        to_tx_data={just_granted[0],just_granted[inputs-1:1]};
      end
    end

  always @(`SDLIB_CLOCKING)
    begin
      if (reset)
        just_granted <= {1'b1,{inputs-1{1'b0}}};
      else
        if (to_be_granted==0)
            just_granted <= just_granted;
        else
            just_granted <= to_be_granted;
    end

endmodule 
`endif //  _SD_RRMUX_V_
