module top ();
    function foo();
      for ( int i=0;i<4; i = i+1) begin
         f2(i,0);
      end
      for ( int j =0;j<4; j++) begin
         f2(j,0);
      end
    endfunction
  
endmodule
