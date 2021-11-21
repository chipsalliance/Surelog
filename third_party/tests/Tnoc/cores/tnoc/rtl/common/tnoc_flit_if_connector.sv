module tnoc_flit_if_connector (
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if
);
  always_comb begin
    sender_if.valid       = receiver_if.valid;
    receiver_if.ready     = sender_if.ready;
    sender_if.flit        = receiver_if.flit;
    receiver_if.vc_ready  = sender_if.vc_ready;
  end
endmodule
