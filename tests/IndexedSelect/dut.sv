module test;

parameter FOO=3;
parameter FOO_REPL={FOO{32'd4}};

parameter DEBUG = FOO_REPL[0+:32];


generate
    genvar i;
    for (i = 0; i < FOO_REPL[0+:32]; i=i+1) begin : genfoo
        $display("test");
    end
endgenerate


endmodule