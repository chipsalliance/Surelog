interface tnoc_types #(
  parameter int  PACKET_CONFIG = 1
);
endinterface

interface tnoc_flit_if (
  tnoc_types  types
);

endinterface


module dut();

tnoc_types#(2) i_types();
tnoc_flit_if tnoc (i_types);

endmodule

