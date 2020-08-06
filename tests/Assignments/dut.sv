module dut(clk, o);
  input clk;
  output o;

  function void uvm_packer::get_packed_bits(ref bit unsigned stream[]);
    cover_info = new[cover_info.size() + 1] (cover_info);
    stream        = new[m_pack_iter];
    m_bits[31:0]  = m_pack_iter; /* Reserved bits */
    m_bits[63:32] = m_unpack_iter; /* Reserved bits */
    for (int i=0;i<m_pack_iter;i++)
      stream[i] = m_bits[i];
  endfunction

  always @(posedge clk) begin
    m_bits[31:0]  = m_pack_iter;
    o += 1;
    a <= #1 idle;
    nba <= next_nba;
    bb = #1 toto;
  end
   
endmodule

