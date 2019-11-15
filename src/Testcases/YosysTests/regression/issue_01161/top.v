module error_design(a, b, z0, z1);

    input               a;
    input               b;

    output              z0, z1;

    assign z0 = a;
    assign z0 = b;

    assign z1 = b;

endmodule
