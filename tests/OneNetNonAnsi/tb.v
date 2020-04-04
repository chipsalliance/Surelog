module tb ();
  logic i, o;

  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns i = %0d, o = %0d",$time,i, o);
    #100 $finish();
  end
  
  initial 
  begin 
    i = 0;
    #5 i = 1;   
  end 

  dut dut1(i,o);

endmodule
