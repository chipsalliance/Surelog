/*
:name: integers-sized
:description: Integer literal constants
:tags: 5.7.1
*/
module top();
  logic  [3:0] a;
  logic  [4:0] b;
  logic [ 2:0] c;
  logic [11:0] d;
  logic [15:0] e;

  initial begin
    a = 4'b1001; // is a 4-bit binary number
    b = 5'D3;    // is a 5-bit decimal number
    c = 3'b01x;  // is a 3-bit number with the least
                 // significant bit unknown
    d = 12'hx;   // is a 12-bit unknown number
    e = 16'hz;   // is a 16-bit high-impedance number
  end

endmodule
