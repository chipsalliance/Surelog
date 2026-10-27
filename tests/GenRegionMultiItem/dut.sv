// A bare `generate ... endgenerate` region holds a LIST of generate items, and
// compileGenStmt compiled only the FIRST one -- so every item after it was
// dropped from the model, silently, with no error reported.
//
// ZipCPU's zipmmu writes its TLB priority encoder exactly this way:
//
//     generate
//       integer i;                                 // item 1
//       always @(posedge i_clk) begin ... end      // item 2 -- was dropped
//     endgenerate
//
// so `s_tlb_addr` had no driver at all and the MMU's physical page number was
// wrong from the first lookup on (20 diverging co-simulated cycles under
// uhdm2rtlil, which read the model through UHDM).  A region with a single
// item -- the common wrapper around one block -- was unaffected, which is why
// it went unnoticed.
//
// Both always blocks below must appear in the model: `q` registers `d`, and
// `enc` is the priority encoder whose loop runs over the region's own
// `integer i`.  A third item after them pins that the walk does not stop at
// the second either.
module dut (
    input  wire       i_clk,
    input  wire       d,
    input  wire [3:0] match,
    output reg        q,
    output reg  [1:0] enc,
    output reg        seen
);
  generate
    integer i;

    always @(posedge i_clk) begin
      q <= d;
    end

    always @(posedge i_clk) begin
      enc <= 2'b0;
      for (i = 0; i < 4; i = i + 1)
        if (match[i]) enc <= i[1:0];
    end

    always @(posedge i_clk) begin
      seen <= |match;
    end
  endgenerate
endmodule
