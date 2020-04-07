module tb; 
  reg clk;
  logic div;
  logic rstn;
  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns clk = %0d, %0d",$time,clk, div);
    #100 $finish();
  end
  
  initial 
  begin 
    rstn = 0;
    clk = 0; 
    #2 rstn = 1;
  end 
    
  always 
    #5 clk = !clk; 

  dut dut1(rstn, clk, div);
  
  property divide(bit a, int n); 
  @(posedge clk) $rose(a) |=> !a[*n-1] ##1 $rose(a); 
  endproperty // divide
   
  ap_div2: assert property(@ (posedge clk) divide(div, 2)) $display("OK!"); else $fatal(1, "FAILED ASSERTION");
  
endmodule // tb


