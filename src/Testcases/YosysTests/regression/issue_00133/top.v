module top(input [7:0] a, output reg [7:0] y);
  always @* begin:myblock
    reg [7:0] myarray [0:1];
    myarray[0] = a + 23;
    myarray[1] = myarray[0] - 42;
    y = myarray[1] + 19;
  end
endmodule
