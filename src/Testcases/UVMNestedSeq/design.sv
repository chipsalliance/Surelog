
`include "uvm_macros.svh"

interface dut_if;

  logic clock, reset;
  logic cmd;
  logic [7:0] addr;
  logic [7:0] data;

endinterface


module dut(dut_if dif);

  import uvm_pkg::*;

  always @(posedge dif.clock)
  begin
    `uvm_info("", $sformatf("DUT received cmd=%b, addr=%d, data=%d",
                            dif.cmd, dif.addr, dif.data), UVM_MEDIUM)
  end
  
endmodule
