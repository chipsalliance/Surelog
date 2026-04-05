module mod1
(
);
typedef struct packed {
    logic [63:0] f1;
    logic [7:0] f2;
} td1;
typedef struct packed {
    logic [63:0] f1;
    logic [7:0] f2;
} td2;

td2 inst1;

generate
if(1) begin : GEN1
    td1 [3:0] pipe;
    assign inst1 = '{
        f1 : pipe[3].f1[63:0],
        f2 : pipe[3].f2[7:0]
    };
end : GEN1
endgenerate

endmodule
