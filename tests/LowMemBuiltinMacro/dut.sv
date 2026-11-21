// Under -lowmem / -mp the preprocessing is done by a child process, which must
// see the same builtin macros (`SURELOG, `SV_COV_*) as a single-process run.
`ifdef SURELOG
module top(output logic o);
  assign o = `SV_COV_OK;
endmodule
`else
module top(output logic o) this_branch_is_a_syntax_error
`endif
