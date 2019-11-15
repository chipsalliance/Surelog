`timescale 1ns/1ns
module top;
  
  initial begin
    $timeformat(-9,6,"ns",20);
    $display("here");
    $display("in top, time: %t",$time);

    $finish;
  end

endmodule


