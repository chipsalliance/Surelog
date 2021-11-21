module tnoc_flit_if_dummy_sender (
  tnoc_flit_if.sender sender_if
);
  assign  sender_if.valid = '0;
endmodule
