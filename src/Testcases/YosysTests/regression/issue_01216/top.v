module top (hz100, pb, ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0, left, right, red, green, blue);
  input hz100;
  input [20:0] pb;
  output [7:0] ss7;
  output [7:0] ss6;
  output [7:0] ss5;
  output [7:0] ss4;
  output [7:0] ss3;
  output [7:0] ss2;
  output [7:0] ss1;
  output [7:0] ss0;
  output [7:0] left;
  output [7:0] right;
  output red;
  output green;
  output blue;

  reg [4:0] op;
  reg [31:0] save;
  reg [31:0] entry;
  reg [31:0] nextresult;

  wire [31:0] source = displaysave ? save : entry;
  assign {left,right} = source[15:0];

  wire [4:0] key;
  wire pressed;
  scankey sk(.clk(hz100), .strobe(pressed), .out(key), .in(pb));

  always @ (posedge pressed)
      begin
        casez (key)
          5'b0????: begin
            entry <= {28'b0,key[3:0]};
          end
          5'b1????: begin
            save <= nextresult;
            op <= key;
          end

        endcase
      end

  always @(*)
    case (op)
      0: nextresult = entry;
      default: nextresult = save;
    endcase

endmodule

module scankey(clk, in, out, strobe);
    input wire clk;
    output wire [4:0] out;
    output wire       strobe;
    input  wire [20:0] in;
    wire active;
    reg [4:0] highest;

    reg [1:0] delay;
    always @(posedge clk)
      delay <= delay<<1 | active;
    assign strobe = delay[1];

    assign {active,out} = in[20] == 1 ? 6'b110100 :
                          in[19] == 1 ? 6'b110011 :
                          in[18] == 1 ? 6'b110010 :
                          in[17] == 1 ? 6'b110001 :
                          in[16] == 1 ? 6'b110000 :
                          in[15] == 1 ? 6'b101111 :
                          in[14] == 1 ? 6'b101110 :
                          in[13] == 1 ? 6'b101101 :
                          in[12] == 1 ? 6'b101100 :
                          in[11] == 1 ? 6'b101011 :
                          in[10] == 1 ? 6'b101010 :
                          in[ 9] == 1 ? 6'b101001 :
                          in[ 8] == 1 ? 6'b101000 :
                          in[ 7] == 1 ? 6'b100111 :
                          in[ 6] == 1 ? 6'b100110 :
                          in[ 5] == 1 ? 6'b100101 :
                          in[ 4] == 1 ? 6'b100100 :
                          in[ 3] == 1 ? 6'b100011 :
                          in[ 2] == 1 ? 6'b100010 :
                          in[ 1] == 1 ? 6'b100001 :
                          in[ 0] == 1 ? 6'b100000 : 6'b000000;
endmodule
