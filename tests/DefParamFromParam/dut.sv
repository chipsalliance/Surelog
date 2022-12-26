module fifo #(
    parameter width1 = 9,
    parameter width2 = 8
);
endmodule
module top #(
    parameter width_a = 10,
    parameter width_b = width_a
);
    fifo fifo_inst ();
    defparam fifo_inst.width1 = width_a;
    defparam fifo_inst.width2 = width_b;
endmodule
