interface I;
logic [7:0] r;
const int x=1;
bit R;
modport A (output .P(r[3:0]), input .Q(x), R);
modport B (output .P(r[7:4]), input .Q(2), R);
endinterface

module sub (interface I);
  
  initial I.P = 4'b1010;
endmodule
  
module top();
  I inst();
  sub s (inst.A);
  
  initial #1 $display("0x%0b", inst.r);
  
endmodule
