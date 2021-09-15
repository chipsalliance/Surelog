interface logic_gate_if;

logic[3:0] a;

endinterface


module or_ex(
    input logic[3:0] a
);

  logic_gate_if lg ();  

  assign lg.a = a;

endmodule // or_ex
