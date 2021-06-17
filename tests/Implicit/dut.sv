
module dff_from_nand();
wire Q,Q_BAR;
reg  D,CLK;

nand U1 (X,D,CLK) ; 
not (X_BAR, X);
endmodule

