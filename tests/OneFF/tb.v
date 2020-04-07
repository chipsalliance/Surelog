
module tb; 
  reg clk;
  logic rstn;
  logic d;
  reg o;

  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns clk = %0d, %0d",$time,clk, o);   
    #100 $finish();
  end
  
  initial 
    begin
    rstn = 0;
    clk = 0; 
    d = 0;  
    #2 rstn = 1;
    assert(o == 0) $display("OK!"); else $fatal(1, "FAILED ASSERTION");  
    #10 d = 1;
    #5 assert(o == 1) $display("OK!"); else $fatal(1, "FAILED ASSERTION");  
    #20 d = 0; 
    #10 assert(o == 0) $display("OK!"); else $fatal(1, "FAILED ASSERTION");   
  end 
    
  always 
    #5 clk = !clk; 

  dut dut1(d, rstn, clk, o);
  
endmodule



