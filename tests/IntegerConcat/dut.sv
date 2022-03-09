package pkg;
localparam int FLASH_INFO_PER_BANK=4;
parameter int InfosPerBank    = FLASH_INFO_PER_BANK;
parameter int InfoPageW       = $clog2(InfosPerBank);
parameter int NumSeeds = 2;
parameter int CreatorInfoPage = 1;
parameter int OwnerInfoPage = 2;
parameter logic [NumSeeds-1:0][InfoPageW-1:0] SeedInfoPageSel =
{
  CreatorInfoPage,
  OwnerInfoPage
};

endpackage

module test #(
  parameter logic [3:0] p
)
();
endmodule

module dut();
import pkg::*;

test #(.p(SeedInfoPageSel)) t();
endmodule
