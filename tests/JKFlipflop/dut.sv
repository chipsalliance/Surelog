module JKFlipflop(J,K,clk,reset,q);
  input J,K,clk,reset;
  output q;
  wire w;
  assign w=(J&~q)|(~K&q);
  D_Flipflop dff(w,clk,reset,q);
endmodule

module D_Flipflop(Din,clk,reset,q); ////////////// (Din) Missing in vpiPort UHDM output for uhdmtopModules
    input Din,clk,reset;
    output reg q;
    always@(posedge clk)
    begin
    if(reset)
    q=1'b0;
    else
    q=Din;
    end
endmodule
 
