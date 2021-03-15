

module top ();
 localparam i = 0;
 parameter dims_p              = 2;
parameter dirs_lp         = dims_p*2+1;

  localparam bit [1:0][4:0][4:0] StrictXY
                            = {
                               {//  SNEWP (input)
                                 5'b01111 // S
                                ,5'b10111 // N
                                ,5'b00011 // E
                                ,5'b00101 // W
                                ,5'b11111 // P (output)
                                }
                               ,
                               {//  SNEWP (output)
                                 5'b01001 // S
                                ,5'b10001 // N
                                ,5'b11011 // E
                                ,5'b11101 // W
                                ,5'b11111 // P (input)
                                }
                               };

   localparam  bit [1:0][2:0][2:0] StrictX
                             = {   // EWP (input)
                                {  3'b011 // E
                                  ,3'b101 // W
                                  ,3'b111 // P (output)
                                }
                               ,   // EWP (output)
                                {  3'b011 // E
                                  ,3'b101 // W
                                  ,3'b111 // P (input)
                                }
                              };                            

 parameter bit [1:0][dirs_lp-1:0][dirs_lp-1:0] routing_matrix_p =  (dims_p == 2) ? StrictXY : StrictX;
//parameter bit [1:0][dirs_lp-1:0][dirs_lp-1:0] routing_matrix_p = StrictXY ;



localparam output_dirs_sparse_lp = (($bits(routing_matrix_p[0][i]) < 65) ? 1'b0 : ('X)) + ((((routing_matrix_p[0][i])>>(0))&1'b1) +(((routing_matrix_p[0][i])>>(1))&1'b1) +(((routing_matrix_p[0][i])>>(2))&1'b1) +(((routing_matrix_p[0][i])>>(3))&1'b1) +(((routing_matrix_p[0][i])>>(4))&1'b1) +(((routing_matrix_p[0][i])>>(5))&1'b1) +(((routing_matrix_p[0][i])>>(6))&1'b1)+(((routing_matrix_p[0][i])>>(7))&1'b1) +(((routing_matrix_p[0][i])>>(8))&1'b1)+(((routing_matrix_p[0][i])>>(9))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(10))&1'b1)+(((routing_matrix_p[0][i])>>(11))&1'b1)+(((routing_matrix_p[0][i])>>(12))&1'b1)+(((routing_matrix_p[0][i])>>(13))&1'b1)+(((routing_matrix_p[0][i])>>(14))&1'b1)+(((routing_matrix_p[0][i])>>(15))&1'b1)+(((routing_matrix_p[0][i])>>(16))&1'b1)+(((routing_matrix_p[0][i])>>(17))&1'b1)+(((routing_matrix_p[0][i])>>(18))&1'b1)+(((routing_matrix_p[0][i])>>(19))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(20))&1'b1)+(((routing_matrix_p[0][i])>>(21))&1'b1)+(((routing_matrix_p[0][i])>>(22))&1'b1)+(((routing_matrix_p[0][i])>>(23))&1'b1)+(((routing_matrix_p[0][i])>>(24))&1'b1)+(((routing_matrix_p[0][i])>>(25))&1'b1)+(((routing_matrix_p[0][i])>>(26))&1'b1)+(((routing_matrix_p[0][i])>>(27))&1'b1)+(((routing_matrix_p[0][i])>>(28))&1'b1)+(((routing_matrix_p[0][i])>>(29))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(30))&1'b1)+(((routing_matrix_p[0][i])>>(31))&1'b1)+(((routing_matrix_p[0][i])>>(32))&1'b1)+(((routing_matrix_p[0][i])>>(33))&1'b1)+(((routing_matrix_p[0][i])>>(34))&1'b1)+(((routing_matrix_p[0][i])>>(35))&1'b1)+(((routing_matrix_p[0][i])>>(36))&1'b1)+(((routing_matrix_p[0][i])>>(37))&1'b1)+(((routing_matrix_p[0][i])>>(38))&1'b1)+(((routing_matrix_p[0][i])>>(39))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(40))&1'b1)+(((routing_matrix_p[0][i])>>(41))&1'b1)+(((routing_matrix_p[0][i])>>(42))&1'b1)+(((routing_matrix_p[0][i])>>(43))&1'b1)+(((routing_matrix_p[0][i])>>(44))&1'b1)+(((routing_matrix_p[0][i])>>(45))&1'b1)+(((routing_matrix_p[0][i])>>(46))&1'b1)+(((routing_matrix_p[0][i])>>(47))&1'b1)+(((routing_matrix_p[0][i])>>(48))&1'b1)+(((routing_matrix_p[0][i])>>(49))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(50))&1'b1)+(((routing_matrix_p[0][i])>>(51))&1'b1)+(((routing_matrix_p[0][i])>>(52))&1'b1)+(((routing_matrix_p[0][i])>>(53))&1'b1)+(((routing_matrix_p[0][i])>>(54))&1'b1)+(((routing_matrix_p[0][i])>>(55))&1'b1)+(((routing_matrix_p[0][i])>>(56))&1'b1)+(((routing_matrix_p[0][i])>>(57))&1'b1)+(((routing_matrix_p[0][i])>>(58))&1'b1)+(((routing_matrix_p[0][i])>>(59))&1'b1) 
                                                                                       +(((routing_matrix_p[0][i])>>(60))&1'b1)+(((routing_matrix_p[0][i])>>(61))&1'b1)+(((routing_matrix_p[0][i])>>(62))&1'b1)+(((routing_matrix_p[0][i])>>(63))&1'b1))
;



initial begin
  $display ("d = %d", output_dirs_sparse_lp );
end
 
if (output_dirs_sparse_lp != 5) begin
  BAD bad();
end

endmodule


module middle ();
 
  parameter int A3[0:2] = '{1, 2, 3};
  parameter A = A3[0];

if (A != 1) begin
  BAD bad();
end
 
endmodule


module bottom ();
 
  parameter int A3[0:2] = {1, 2, 3};
  parameter A = A3[2];

if (A != 3) begin
  BAD bad();
end
 
endmodule

