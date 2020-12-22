module and_tb(output logic o); 
  logic a, b;
 
  initial begin
    $monitor("@%0dns %0d & %0d = %0d",$time,a, b, o);
    #100 $finish();
  end
  
  initial 
  begin 
     a = 1'b0;
     b = 1'b0;
     #1 assert(o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
     #5
     a = 1'b0;
     b = 1'b1;
     #1 assert(o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
     #5
     a = 1'b1;
     b = 1'b0;
     #1 assert(o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
     #5
     a = 1'b1;
     b = 1'b1;
     #1 assert(o == (a & b)) $display("OK!"); else $fatal(1, "o != (a & b)!");
  end 

  dut dut1(a,b,o);
 
endmodule
