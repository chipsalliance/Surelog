package fpnew_pkg;
typedef enum logic [1:0] {
    ADDMUL, DIVSQRT, NONCOMP, CONV
  } opgroup_e;


function automatic int unsigned num_operands(opgroup_e grp);
    unique case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3; // vectorial casts use 3 operands
      default: return 0;
    endcase
  endfunction

endpackage

module GOOD ();
endmodule

module top ();
   import fpnew_pkg::*;
  
   parameter p = num_operands(DIVSQRT);

   if (p == 2) begin
     GOOD good();
   end
endmodule

