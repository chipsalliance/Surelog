// `pt.BB'(bank)` — a size cast whose casting type is a MEMBER of a
// struct-valued parameter.  The bare name `pt` resolved to the struct TYPE, so
// the cast took the whole struct's width and the enclosing concatenation lost
// its other operands (VeeR/Caliptra boot_flow_monitor, el2_ifu_mem_ctl).
package cfg_pkg;
  typedef struct packed { int NB; int BITS; int LO; int BB; } cfg_t;
  localparam cfg_t DEF = '{NB: 4, BITS: 16, LO: 4, BB: 2};
endpackage
module dut #(parameter cfg_pkg::cfg_t pt = cfg_pkg::DEF) (
  input  logic [pt.NB-1:0][pt.BITS-1:pt.LO] addr_bank,
  input  logic [pt.NB-1:0] en,
  output logic [pt.NB-1:0][pt.BITS-1:0] read_addr,
  output logic hit
);
  always_comb begin
    hit = '0;
    for (int bank = 0; bank < pt.NB; bank++) begin
      read_addr[bank] = {addr_bank[bank], pt.BB'(bank), {(pt.LO - pt.BB){1'b0}}};
      hit |= en[bank] && (read_addr[bank] inside {[16'h0100:16'h01ff]});
    end
  end
endmodule
module top (
  input  logic [3:0][15:4] addr_bank,
  input  logic [3:0] en,
  output logic [3:0][15:0] read_addr,
  output logic hit
);
  dut u (.addr_bank(addr_bank), .en(en), .read_addr(read_addr), .hit(hit));
endmodule
