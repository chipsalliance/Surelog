module top ();
  always_comb begin : csr_read_write
  dmstatus.allnonexistent = logic'(32'(hartsel_o) > (NrHarts - 1));
  end
endmodule  

