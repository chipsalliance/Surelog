// A module that imports a package with `pkg::*` and then declares a parameter
// whose name the package also uses.  LRM 26.3: the local declaration wins.
// `CoproInstr` in the package is a 3-entry table of 73-bit issue_t; the module's
// own `CoproInstr` is a 2-entry table of 65-bit copro_t bound to p::CoproCompInstr.
// Before the fix the module's parameter took the PACKAGE parameter's typespec
// (array of issue_t), so the pattern was sized 73 x 3 and every field read
// landed at the wrong offset.
package p;
  typedef struct packed { logic accept; logic [31:0] instr; } resp_t;
  typedef struct packed { logic [15:0] instr; logic [15:0] mask; resp_t resp; } copro_t;
  typedef struct packed { logic [31:0] instr; logic [31:0] mask; logic [8:0] resp; } issue_t;
  parameter int unsigned NbInstr = 3;
  parameter issue_t CoproInstr [NbInstr] = '{'{instr: 32'h11, mask: 32'h22, resp: 9'd1}, '{instr: 32'h33, mask: 32'h44, resp: 9'd2}, '{instr: 32'h55, mask: 32'h66, resp: 9'd3}};
  parameter int unsigned NbCompInstr = 2;
  parameter copro_t CoproCompInstr [NbCompInstr] = '{
    '{instr : 16'hE000, mask : 16'hF003, resp : '{accept : 1'b1, instr : 32'h7B}},
    '{instr : 16'hF000, mask : 16'hF003, resp : '{accept : 1'b1, instr : 32'h157B}}
  };
endpackage
module dec #(parameter type copro_t = logic, parameter int NbInstr = 1, parameter copro_t CoproInstr [NbInstr] = {0})
  (input [15:0] x, output [1:0] sel, output [15:0] m0, output [15:0] i1);
  assign sel = {((CoproInstr[1].mask & x) == CoproInstr[1].instr),
                ((CoproInstr[0].mask & x) == CoproInstr[0].instr)};
  assign m0 = CoproInstr[0].mask;
  assign i1 = CoproInstr[1].instr;
endmodule
module dut import p::*; #(
  parameter type copro_t = p::copro_t,
  parameter int NbInstr = p::NbCompInstr,
  parameter copro_t CoproInstr [NbInstr] = p::CoproCompInstr
) (input [15:0] x, output [NbInstr-1:0] sel, output [15:0] m0, output [15:0] i1);
  dec #(.copro_t(copro_t), .NbInstr(NbInstr), .CoproInstr(CoproInstr)) u (.x(x), .sel(sel), .m0(m0), .i1(i1));
endmodule
