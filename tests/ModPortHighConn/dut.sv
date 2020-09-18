
module moduleA (inout port0, port1);
endmodule

module top;
    wire [1:0] topA, topB;
    moduleA instanceA(.port0(topA[0]), .port1(topB[0]));
    moduleA instanceB(topA[1], topB[0]);
    moduleA instanceC(topA[1], topB[0]||topB[1]);
    moduleA instanceD(topA[1]||topA[0], topB[0]);
endmodule

