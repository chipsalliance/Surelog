module mux2 (S,A,B,Y);
    input S;
    input A,B;
    output reg Y;
`ifndef BUG

    always @(*)
		Y = (S)? B : A;
`else

    always @(*)
		Y = (~S)? B : A;
`endif
endmodule

module mux4 ( S, D, Y );

input[1:0] S;
input[3:0] D;
output Y;

reg Y;
wire[1:0] S;
wire[3:0] D;

always @*
begin
    case( S )
       0 : Y = D[0];
       1 : Y = D[1];
`ifndef BUG
       2 : Y = D[2];
`else
       2 : Y = D[3];
`endif
       3 : Y = D[3];
   endcase
end

endmodule

module mux8 ( S, D, Y );

input[2:0] S;
input[7:0] D;
output Y;

reg Y;
wire[2:0] S;
wire[7:0] D;

always @*
begin
   case( S )
       0 : Y = D[0];
       1 : Y = D[1];
       2 : Y = D[2];
       3 : Y = D[3];
`ifndef BUG
       4 : Y = D[4];
`else
       4 : Y = D[7];
`endif
       5 : Y = D[5];
       6 : Y = D[6];
       7 : Y = D[7];
   endcase
end

endmodule

module mux16 (D, S, Y);
 	input  [15:0] D;
 	input  [3:0] S;
 	output Y;

assign Y = D[S];

endmodule


module top (
input [3:0] S,
input [15:0] D,
output M2,M4,M8,M16
);

mux2 u_mux2 (
        .S (S[0]),
        .A (D[0]),
        .B (D[1]),
        .Y (M2)
    );


mux4 u_mux4 (
        .S (S[1:0]),
        .D (D[3:0]),
        .Y (M4)
    );

mux8 u_mux8 (
        .S (S[2:0]),
        .D (D[7:0]),
        .Y (M8)
    );

mux16 u_mux16 (
        .S (S[3:0]),
        .D (D[15:0]),
        .Y (M16)
    );

reg b,c = 1.01;
wire a;


endmodule

module concatenation_operator();
  reg [3:0]  r_VAL_1 = 4'b0111;
  reg [3:0]  r_VAL_2 = 4'b1100;
  wire [7:0] w_CAT;

  reg  [3:0]       r_UNSIGNED = 4'b0010;
  reg signed [3:0] r_SIGNED   = 4'b1110;
  wire [7:0]       w_CAT_2;
  wire [15:0]      w_CAT_3;

  reg              r_CLOCK = 1'b0;
  reg [7:0]        r_SHIFT_REG = 8'h01;

  // Demonstrates a common concatenation.
  assign w_CAT = {r_VAL_1, r_VAL_2};

  // Demonstrates concatenation of different types
  assign w_CAT_2 = {r_SIGNED, r_UNSIGNED};

  // Demonstrates Verilog padding upper bits with 0.
  assign w_CAT_3 = {r_VAL_1, r_VAL_2};

  // Generate a clock to drive shift register below
  always #1 r_CLOCK = !r_CLOCK;

  // Demonstrate Shifting of a 1 through an 8 bit register.
  always @(posedge r_CLOCK)
    begin
      r_SHIFT_REG[7:0] <= {r_SHIFT_REG[6:0], r_SHIFT_REG[7]};
    end

endmodule // concatenation_operator

module replication_operator();
  reg [3:0]  r_VAL_1 = 4'b0111;

  parameter c_MULTIPLIER = 4'b0010;

  parameter WIDTH = 1;
wire [WIDTH-1:0] connection;

generate
  if (WIDTH > 1) begin
    assign connection = { {WIDTH-1{1'b0}}, 1'b1 };
  end
  else begin
    assign connection = 1'b1 ;
  end
endgenerate


endmodule // replication_operator

module Shift (A, Y1, Y2);



                 input [7:0] A;

                 output [7:0] Y1, Y2;

                 parameter B=3; reg [7:0] Y1, Y2;



                 always @(A)

                 begin

                                  Y1=A<<B; //logical shift left

                                  Y2=A>>B; //logical shift right

                 end

endmodule

module SShift (A, Y1, Y2);



                 input [7:0] A;

                 output [7:0] Y1, Y2;

                 parameter B=3; reg [7:0] Y1, Y2;



                 always @(A)

                 begin

                                  Y1=A<<<B; //logical shift left

                                  Y2=A>>>B; //logical shift right

                 end

endmodule
