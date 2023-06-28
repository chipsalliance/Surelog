package pkg;
   parameter logic [3:0] A = 4'hF;
endpackage

module top(output a);
   assign a = pkg::A[0];
endmodule

/*
`default_nettype none
module named_genblk_top;
        generate
                
                if (1) begin
                        
                        wire t;
                        
                        begin : foo
                                wire x1;
                                //wire y1;
                                
                                begin : bar1
                                  wire z1;
                                end
                                
                        end
                        
                        //wire u;
                        
                        
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
        assign genblk1.foo.x = 1;
        assign genblk1.u = 1;
        assign bar.x = 1;
        assign bar.y = 1;
        assign bar.baz.x = 1;
        assign bar.baz.z = 1;
        
endmodule
*/