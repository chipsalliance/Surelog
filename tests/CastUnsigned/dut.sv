
module top();
  typedef virtual blah_if#(N) foo_if;
	parameter signed INIT = '0;


  always_comb begin : proc_stall_tieoff
      if (setup_received == string'(i)) begin
        hw2reg.stall = unsigned'(i);
      end 
  end

endmodule  
