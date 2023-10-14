
module top();
logic count, clk, reset;
  
sequence seq_count_increment;
@(posedge clk) (count + 1'b1) or (count == 4'b1111);
endsequence

// OK
property p1_count_increment;
  seq_count_increment |=> count;
endproperty

// OK
property p1_count_increment;
  @(posedge clk) seq_count_increment |=> count;
endproperty

// Not OK
property p2_count_increment;
  @(posedge clk) count |=> seq_count_increment ;
endproperty

// Not OK
property p3_count_increment;
  @(posedge clk) seq_count_increment |=> seq_count_increment;
endproperty

endmodule

/*
module system_assertion();

logic clk = 0;
always #1 clk = ~clk;

logic req, gnt;

//-------------------------------------------------
// Property Specification Layer
//-------------------------------------------------
sequence s_req;
  @ (posedge clk)
  $rose(req) ##1 $past(!req,1);
endsequence


property system_prop;
  @ (posedge clk) 
  s_req |=> s_gnt;
endproperty

endmodule

*/