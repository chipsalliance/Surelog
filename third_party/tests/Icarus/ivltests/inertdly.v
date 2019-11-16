module test ();

reg a,b;

always @(inp)
  a = #5 inp;
always @(inp)
  b = #3 inp;

reg inp,error;

initial
  begin
      $dumpfile("test.vcd");
      $dumpvars(0,test);
      #1 ;		// 1 ns
      error = 0;
      inp = 0;
      #6;		// 7 ns
      if(a !== 0)
         begin
            $display("FAILED - a doesn't clear to 0 at init");
            error = 1;
         end
      if(b !== 0)
         begin
            $display("FAILED - b doesn't clear to 0 at init");
            error = 1;
         end
      #1;		// 8 ns
      inp = 1;		// Create a 4 ns pulse 
      #4 ;
      inp = 0;		// 12 ns
      #4 ;
  end

initial 
  begin
      # 12;
      // We should see a as 0, and b as 1
      if(a !== 0)
         begin
            $display("FAILED - a propagated pulse early");
            error = 1;
         end
      if(b !== 1)
         begin
            $display("FAILED - b doesn't propagate pulse as expected");
            error = 1;
         end
      # 3; // 15 ns
      if(a !== 0)
         begin
            $display("FAILED - a propagated pulse and shouldn't ");
            error = 1;
         end
      if(error == 0)
         $display("PASSED");
    
  end
 
endmodule        
