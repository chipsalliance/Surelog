module bidirtest (
A, EO, Q, BI
);

inout BI;
output Q;
input A;
input EO;

assign BI = (EO == 1'b1) ? A : 1'bz;
assign Q = BI;

endmodule
