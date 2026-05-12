// Reproduction of a UCSB victim-cache snippet.  The original snippet has
// only an input port and reads internal state (`dll_q`, `lru_q`, `mru_q`)
// that is undriven, so co-sim sees `'x` on everything and isn't useful.
//
// To make the test controllable + observable, the internal state is
// driven from input ports (flat-packed bit vectors for the unpacked
// struct array) and the always_comb's results are forwarded to output
// ports.  The for-loop-with-`break` over the unpacked struct array —
// the actual subject of the test — is preserved, including the
// anonymous-packed-struct + `dll_d[4]` unpacked-dim declaration form.

module ucsbece154b_victim_cache(
    input  logic [7:0]  raddr_i,
    // Drive the internal state the always_comb reads:
    input  logic [23:0] dll_q_flat_i,   // 4 entries × 6-bit packed struct, low elem = LSBs
    input  logic [1:0]  lru_q_i,
    input  logic [1:0]  mru_q_i,
    // Expose the computed signals so co-sim can compare them:
    output logic [1:0]  read_index_o,
    output logic [1:0]  lru_d_o,
    output logic [1:0]  mru_d_o,
    output logic [23:0] dll_d_flat_o
);

localparam OFFSET_WIDTH = 1;
localparam TAG_SIZE = 1;

logic [TAG_SIZE-1:0] rtag;
assign rtag = raddr_i[OFFSET_WIDTH +: TAG_SIZE];

integer i;
integer j;
integer k;

typedef logic [1:0] way_index_t;

// Anonymous packed struct + unpacked-array dim — the original snippet's
// declaration form, kept verbatim.
struct packed {
    logic [TAG_SIZE-1:0] tag;
    way_index_t lru;
    way_index_t mru;
    logic valid;
} dll_d[4], dll_q[4];

way_index_t lru_d, lru_q, mru_d, mru_q;
way_index_t read_index;

// Pack the flat 24-bit input into the 4-element unpacked struct array;
// element 0 sits at the LSBs.
always_comb begin
    for (j = 0; j < 4; j++) begin
        dll_q[j] = dll_q_flat_i[j*6 +: 6];
    end
end
assign lru_q = lru_q_i;
assign mru_q = mru_q_i;

// Original always_comb (the construct under test) — same shape as the
// source snippet except the "no entry matches" sentinel is `'1` instead
// of `'x`.  The original `read_index = 'x` makes the no-match case a
// don't-care; Yosys's synth then folds the priority-encoder output to a
// concrete value (it picked 3) while Verilator's 2-state RTL view reads
// the `'x` as 0, producing a co-sim divergence that's purely an
// x-propagation artefact.  Forcing `'1` keeps the same observable
// behaviour for any matching entry (the `break` still wins first) and
// gives both forms the same deterministic value when nothing matches.
always_comb begin
    read_index = '1;
    lru_d = lru_q;
    mru_d = mru_q;
    dll_d = dll_q;

    for (i = 0; i < 4; i++) begin
        if (dll_d[i].valid && (rtag==dll_d[i].tag)) begin
            read_index = way_index_t'(i);
            break;
        end
    end
end

// Forward the computed values to outputs.
assign read_index_o = read_index;
assign lru_d_o      = lru_d;
assign mru_d_o      = mru_d;
always_comb begin
    for (k = 0; k < 4; k++) begin
        dll_d_flat_o[k*6 +: 6] = dll_d[k];
    end
end

endmodule
