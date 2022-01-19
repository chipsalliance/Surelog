package my_pkg;
    typedef struct {
        logic[2:0] first;
        int second;
    } variable_type;
endpackage
module top import my_pkg::variable_type;
(
    input variable_type a, b
);
endmodule
