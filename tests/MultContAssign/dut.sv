

module top();

	int v;
   assign (highz0, weak1)    inout_i1 = pu;
   assign (weak0, highz1)    inout_i1 = ~pd;

	assign v = 12;
	assign v = 13;


   assign (weak0, weak1)    inout_i2 = pu;
   assign (weak1, weak0)     inout_i2 = ~pd;


   if (0) assign (weak0, weak1)    inout_i3 = pu;
   else assign (weak1, weak0)     inout_i3 = ~pd;


      assign    out = (sel == 2'b00)? v0 : 2'bz;
      assign    out = (sel == 2'b01)? v1 : 2'bz;

      assign     (pull1, pull0) pull_up_1 = 1'b1;
      
      assign     pull_up_1 = (driver_1_en) ? driver_1 : 1'bz;


parameter NUM_WAYS = 1;
generate
   case (NUM_WAYS)
       1:
       begin
           assign fill_way = 0;
        
       end
       2:
       begin
           assign fill_way = !lru_flags[0];
     
       end
   endcase    
endgenerate

endmodule


module wandwor_test0 (A, B, X);
	input A, B;
	output wor X;
  
	assign X = A, X = B;
	
endmodule


module top2;
  uwire two;

  assign two = 1'b1;
  assign two = 1'b0;

  initial $display("Failed: this should be a compile time error!");
endmodule
