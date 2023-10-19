module top();

sequence s_req_bad;
  @ (posedge clk)
  $rose(req) ##1 $past(!req,0);
endsequence


sequence s_req_ok;
  @ (posedge clk)
  $rose(req) ##1 $past(!req,1);
endsequence

endmodule
