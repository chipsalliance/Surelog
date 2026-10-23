// $bits() of a TYPE PARAMETER bound to a struct whose member is typed by an
// ANCESTOR's type parameter: hpdcache's `hpdcache_dir_entry_t` (member
// `hpdcache_tag_t tag`, hpdcache's own type parameter) is relayed to
// hpdcache_memctrl, which sizes its directory SRAMs with
// `localparam ENTRY_WIDTH = $bits(hpdcache_dir_entry_t)`.  The member was
// measured at its DEFAULT (logic, 1 bit): 1+1+1+1+1 = 5 instead of 48, and
// every 48-bit directory entry was read back as a 5-bit slice.
// Expected: u.u_mem.ENTRY_WIDTH = 48, every dir_sram.DATA_SIZE = 48.
module sram #(parameter int ADDR_SIZE = 4, parameter int DATA_SIZE = 1) (
    input logic clk, input logic we, input logic [ADDR_SIZE-1:0] addr,
    input logic [DATA_SIZE-1:0] wdata, output logic [DATA_SIZE-1:0] rdata);
  logic [DATA_SIZE-1:0] mem [2**ADDR_SIZE];
  always_ff @(posedge clk) begin if (we) mem[addr] <= wdata; rdata <= mem[addr]; end
endmodule
module memctrl #(parameter int unsigned WAYS = 2, parameter type dir_entry_t = logic) (
    input logic clk, input logic [WAYS-1:0] we, input logic [3:0] addr,
    input dir_entry_t [WAYS-1:0] wentry, output dir_entry_t [WAYS-1:0] rentry, output logic [WAYS-1:0] valid_o);
  localparam int unsigned ENTRY_WIDTH = $bits(dir_entry_t);
  localparam int unsigned RAM_WIDTH = ENTRY_WIDTH;
  genvar w;
  for (w = 0; w < int'(WAYS); w++) begin : gen_sram
    sram #(.ADDR_SIZE(4), .DATA_SIZE(RAM_WIDTH)) dir_sram (.clk(clk), .we(we[w]), .addr(addr), .wdata(wentry[w]), .rdata(rentry[w]));
    assign valid_o[w] = rentry[w].valid;
  end
endmodule
module cache #(parameter int unsigned WAYS = 2, parameter type tag_t = logic) (
    input logic clk, input logic [WAYS-1:0] we, input logic [3:0] addr,
    input tag_t [WAYS-1:0] wtag, input logic [WAYS-1:0] wvalid,
    output tag_t [WAYS-1:0] rtag, output logic [WAYS-1:0] valid_o);
  typedef struct packed { tag_t tag; logic valid; logic wback; logic dirty; logic fetch; } dir_entry_t;
  dir_entry_t [WAYS-1:0] wentry, rentry;
  for (genvar i = 0; i < WAYS; i++) begin : g
    assign wentry[i] = '{tag: wtag[i], valid: wvalid[i], wback: 1'b0, dirty: 1'b0, fetch: 1'b0};
    assign rtag[i] = rentry[i].tag;
  end
  memctrl #(.WAYS(WAYS), .dir_entry_t(dir_entry_t)) u_mem (.clk, .we, .addr, .wentry, .rentry, .valid_o);
endmodule
module top (input logic clk, input logic [1:0] we, input logic [3:0] addr,
            input logic [1:0][43:0] wtag, input logic [1:0] wvalid,
            output logic [1:0][43:0] rtag, output logic [1:0] valid_o);
  typedef logic [43:0] my_tag_t;
  cache #(.WAYS(2), .tag_t(my_tag_t)) u (.*);
endmodule
