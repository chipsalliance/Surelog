 module fsm (
 clock,
 reset,
 req,
 gnt
 );
 input   clock,reset;
 inout [1:0] req ;
 output [1:0]  gnt ;
 wire    clock,reset;
 wire [1:0] req ;
 reg  [1:0]   gnt ;

  parameter SIZE = 3           ;
 parameter IDLE  = 3'b001,GNT0 = 3'b010,GNT1 = 3'b100,GNT2 = 3'b101,GNT3 = 3'b111;

 reg [SIZE-1:0] state;
 reg [SIZE-1:0] next_state;

  always @ (posedge clock)
 begin : FSM
 if (reset == 1'b1) begin
   state <=  #1  IDLE;
   gnt[0] <= 0;
   gnt[1] <= 0;
 end else
  case(state)
    IDLE : if (req[0] == 1'b1) begin
                 state <=  #1  GNT0;
`ifndef BUG
                 gnt[0] <= 1;
`else
                 gnt[0] <= 1'bZ;
`endif
               end else if (req[1] == 1'b1) begin
                 gnt[1] <= 1;
                 state <=  #1  GNT0;
               end else begin
                 state <=  #1  IDLE;
               end
    GNT0 : if (gnt[1] == 1'b1) begin
                 state <=  #1  GNT0;
               end else begin
                 gnt[1] <= 0;
                 state <=  #1  IDLE;
               end
    GNT1 : if (req[1] == 1'b1) begin
                 state <=  #1  GNT2;
				 gnt[1] <= req[1];
               end
    GNT2 : if (gnt[0] == 1'b1) begin
                 state <=  #1  GNT1;
				 gnt[1] <= req[1];
               end
    default : state <=  #1  IDLE;
 endcase
 end

 endmodule

  module fsm2 (
 clock,
 reset,
 req,
 gnt
 );
 input   clock,reset;
 inout [1:0] req ;
 output [1:0]  gnt ;
 wire    clock,reset;
 wire [1:0] req ;
 reg  [1:0]   gnt ;

  parameter SIZE = 3           ;
 parameter IDLE  = 3'b001,GNT0 = 3'b010,GNT1 = 3'b100,GNT2 = 3'b101,GNT3 = 3'b111;

 reg [SIZE-1:0] state;
 reg [SIZE-1:0] next_state;

  always @ (posedge clock)
 begin : FSM
 if (reset == 1'b1) begin
   state <=  #1  IDLE;
   gnt[0] <= 0;
   gnt[1] <= 0;
 end else
  case(state)
    IDLE : if (req[0] == 1'b1) begin
                 state <=  #1  GNT0;
`ifndef BUG
                 gnt[0] <= 1;
`else
                 gnt[0] <= 1'bZ;
`endif
               end else if (req[1] == 1'b1) begin
                 gnt[1] <= 1;
                 state <=  #1  GNT0;
               end else begin
                 state <=  #1  IDLE;
               end
    GNT0 : if (gnt[1] == 1'b1) begin
                 state <=  #1  GNT0;
               end else begin
                 gnt[1] <= 0;
                 state <=  #1  IDLE;
               end
    GNT1 : if (req[1] == 1'b1) begin
                 state <=  #1  GNT2;
				 gnt[1] <= req[1];
               end
    GNT2 : if (gnt[0] == 1'b1) begin
                 state <=  #1  GNT1;
				 gnt[1] <= req[1];
               end
    default : state <=  #1  IDLE;
 endcase
 end

 endmodule

 module top (
input clk,
input rst,
input a,
input b,
output g0,
output g1
);
wire [1:0] g ;
wire [1:0] r ;
fsm u_fsm ( .clock(clk),
            .reset(rst),
            .req(r),
            .gnt(g));
assign g0 = g[0];
assign g1 = g[1];

assign r[0] = a;
assign r[1] = b;

endmodule
