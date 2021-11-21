module tnoc_flit_if_dummy_sender_array #(
  parameter int ENTRIES = 1
)(
  tnoc_flit_if.sender sender_if[ENTRIES]
);
  for (genvar i = 0;i < ENTRIES;++i) begin : g
    assign  sender_if[i].valid  = '0;
  end
endmodule
