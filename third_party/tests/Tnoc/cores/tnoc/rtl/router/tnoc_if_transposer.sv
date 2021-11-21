module tnoc_if_transposer (
  tnoc_flit_if.receiver           receiver_if[25],
  tnoc_port_control_if.controller controller_if[25],
  tnoc_flit_if.sender             sender_if[25],
  tnoc_port_control_if.requester  requester_if[25]
);
  for (genvar i = 0;i < 5;++i) begin : g
    for (genvar j = 0;j < 5;++j) begin : g
      tnoc_flit_if_connector u_flit_if_connector (
        receiver_if[5*i+j], sender_if[5*j+i]
      );

      always_comb begin
        requester_if[5*j+i].request         = controller_if[5*i+j].request;
        requester_if[5*j+i].free            = controller_if[5*i+j].free;
        requester_if[5*j+i].start_of_packet = controller_if[5*i+j].start_of_packet;
        requester_if[5*j+i].end_of_packet   = controller_if[5*i+j].end_of_packet;
        controller_if[5*i+j].grant          = requester_if[5*j+i].grant;
      end
    end
  end
endmodule
