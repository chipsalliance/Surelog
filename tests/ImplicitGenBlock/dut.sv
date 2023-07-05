

//`default_nettype none
/*
module top;
  generate
     //   if (1) begin
                        
      //          wire t;
     //   end

        if (1) begin : blk1
                
                wire t1;
                wire t2;
        end else if (0)
        begin  : blk2
                wire t3;
                wire t4;
        end
          else begin : blk3
                wire t5;
                wire t6;
        end
  endgenerate
endmodule
*/


module top;
        generate
                
                if (1) begin
                        
                        wire t;
                        
                        begin : foo
                                wire x1;
                                wire y1;
                                
                                begin : bar1
                                  wire z1;
                                end
                                
                        end
                        
                        wire u;
                        
                        
                end
                
           
                begin : bar2
                        wire x2;
                        
                        wire y2;
                        begin : baz
                                wire x3;
                               wire z3;
                        end
                        
                end
               
        endgenerate
     
        assign genblk1.t = 1;
        assign genblk1.foo.x1 = 1;
        assign genblk1.u = 1;
        assign bar2.x2 = 1;
        assign bar2.y2 = 1;
        assign bar2.baz.x3 = 1;
        assign bar2.baz.z3 = 1;
       
endmodule

