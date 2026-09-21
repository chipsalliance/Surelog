// Sibling UNNAMED generate blocks must get DISTINCT names.
//
// genBlkIndex used to be a local of DesignElaboration::elaborateInstance_,
// which is entered once per sub-instance batch, so it restarted at 1 for every
// sibling generate construct and named them all `genblk1`.  Two sibling
// `if (C) ... else ...` constructs then shared one fullName,
// getComponentDefinition() returned the SAME ModuleDefinition for both, and
// that definition accumulated BOTH constructs' always blocks -- each was
// elaborated twice and drove its target net twice.
//
// Downstream this produced 81 driver conflicts in CVA6's ex_stage
// (vaddr_to_be_flushed 64 bits, asid_to_be_flushed 16, and
// current_instruction_is_sfence_vma), which is worse than a wrong value: the
// duplicate feedback constrains a SAT equivalence miter to the inputs where
// the two sides agree, so the proof can pass vacuously.
//
// The two `else` arms below must appear as genblk1 and genblk2, each holding
// exactly ONE always block.
module dut (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic [7:0] rs1_i,
  output logic       sfence_o,
  output logic [7:0] vaddr_o
);
  parameter bit RVS = 1'b1;
  parameter bit RVH = 1'b0;

  if (RVS) begin
    // first sibling conditional construct
    if (RVH) begin
      always_ff @(posedge clk_i or negedge rst_ni)
        if (!rst_ni) sfence_o <= 1'b0;
        else         sfence_o <= rs1_i[1];
    end else begin
      always_ff @(posedge clk_i or negedge rst_ni)
        if (!rst_ni) sfence_o <= 1'b0;
        else         sfence_o <= rs1_i[0];
    end

    // second sibling conditional construct -- must NOT reuse the first's name
    if (RVH) begin
      always_ff @(posedge clk_i or negedge rst_ni)
        if (!rst_ni) vaddr_o <= '0;
        else         vaddr_o <= rs1_i ^ 8'hFF;
    end else begin
      always_ff @(posedge clk_i or negedge rst_ni)
        if (!rst_ni) vaddr_o <= '0;
        else         vaddr_o <= rs1_i;
    end
  end else begin
    assign sfence_o = 1'b0;
    assign vaddr_o  = '0;
  end
endmodule
