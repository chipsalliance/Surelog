module dut2 #() ();   

typedef struct packed {                             
  logic [5:0] q;                                                                                         
} struct_typedef;        
struct_typedef read_buf;                                                                                 
                                                                                                         
assign read_buf.q[1] = 1'b1;                                                                             
                                                
endmodule

