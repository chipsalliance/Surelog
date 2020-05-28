module bottom1 (input a, input b) ;
 bottom2 u1 (a, b);
 bottom3 u2 (a, b);
endmodule

module bottom2 (input a, input b) ;
 bottom4 u2 (a, b);
endmodule


module bottom4 (input a, input b) ;
bottom2 u2 (a, b);
endmodule


module bottom5 (input a, input b) ;
endmodule


module my_module (a, b, c);
input a, b;
output c;
  assign c = a & b ;
endmodule
 
module top (a, b, c) ;
input [3:0] a, b;
output [3:0] c;
  my_module inst [3:0][2:0][1:0] (a, b, c);
  my_module inst1  (a, b, c);
endmodule



module test(a, b);

  parameter POWER1 = 1;
  parameter POWER2 = 1;
  and u0(a,b);
     generate
	if (POWER1 > 2) begin : g1
      and u1(a,b);
    end else if (POWER2 == 1) begin :g1
      and u2(a,b);
    end else if (POWER2 > 0) begin :g1
      and u3(a,b);
    end
  endgenerate

 generate
    if (POWER1 > 0) begin : g1
       if (POWER2 >= 1) begin :g1
         and u4(a,b);
       end
    end
  endgenerate

 and u4(a,b);

 
 
     case (POWER1)
        0, 1, 2: begin : u1        // If p==2 and q==0,1, or 2, then instantiate
            xor g1(a, b, c); // XOR with hierarchical name test.u1.g1
          end
        3: begin : u1        // If p==2 and q==0,1, or 2, then instantiate
            and g1(a, b, c); // XOR with hierarchical name test.u1.g1
          end
        default: begin : u1        // If p==2 and q!=0,1, or 2, then instantiate
            xnor g1(a, b, c); // XNOR with hierarchical name test.u1.g1
          end
      endcase



endmodule






































