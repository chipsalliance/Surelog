
module test #(
  parameter int BobaCount = 2,
  parameter int unsigned NumBobaDrinkersDefault[BobaCount] = '{default: '1},
  parameter int unsigned NumBobaDrinkers[BobaCount] = '{'1, '1},
  parameter int unsigned NumBobaDrinkersMulti[BobaCount] = '{BobaCount{'1}}
)();
endmodule

