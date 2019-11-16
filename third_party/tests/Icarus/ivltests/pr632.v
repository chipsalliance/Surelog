`timescale 1ns/10ps 
module test;

reg [15:0] a1;

initial
  begin
    $monitor ("a1[0]=%b\n",a1);
    for (a1 = 16'h01; a1 != 16'h1f; a1 = a1 + 1)
        begin
           #1;
        end
  end
endmodule
