package uvm_pkg;

task uvm_wait_for_nba_region;

  int nba;
  int next_nba;

  next_nba++;
  nba <= next_nba;
  @(nba);


endtask

endpackage // uvm_pkg
   
   
module gen_errors;
 parameter width_a = 8;
   task A;
     input [width_a-1:0] l;
   
     input  B;
     integer B;
     output  C;
     integer C;
     inout [31:0] E;
     reg   [31:0] E;
     integer internal;
     parameter llen = width_a;
     begin
       C = B;
     end
     
   endtask
 

endmodule
