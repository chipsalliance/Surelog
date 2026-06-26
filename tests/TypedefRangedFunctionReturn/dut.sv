// Regression for UHDM ExprEval::size(): when a function's return type is a
// packed array of a typedef (`word [1:0]`, i.e. 2 * 32 = 64 bits), a constant
// call must const-fold to a 64-bit value.  Before the fix the logic_typespec
// size() case ignored Elem_typespec and sized `word [1:0]` as the outer range
// [1:0] = 2 bits, truncating the folded return (0x...DEADBEEF_ABCD1234 -> 2'b00).
module top(output logic [63:0] o);
   typedef logic [31:0] word;

   function automatic word [1:0] get_two();
      return {32'hDEAD_BEEF, 32'hABCD_1234};
   endfunction

   assign o = get_two();
endmodule
