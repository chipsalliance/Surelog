package cfg_pkg;
  typedef struct packed { int unsigned XLEN; logic FLAG; } cfg_t;
  localparam cfg_t DefaultCfg = '{XLEN: 32'd64, FLAG: 1'b1};
  localparam logic [3:0] IRQ_S_SOFT = 4'd1;
  localparam logic [3:0] IRQ_M_SOFT = 4'd3;
endpackage
module child #(parameter type it_t = logic, parameter it_t INT = '0) (input logic sel, output logic [63:0] o);
  assign o = sel ? INT.S_SW : INT.M_SW;
endmodule
module top import cfg_pkg::*; #(parameter cfg_t Cfg = DefaultCfg) (input logic sel, output logic [63:0] o);
  localparam type it_t = struct packed { logic [Cfg.XLEN-1:0] S_SW; logic [Cfg.XLEN-1:0] M_SW; };
  localparam it_t INT = '{
      S_SW: (Cfg.XLEN'(1) << (Cfg.XLEN - 1)) | Cfg.XLEN'(IRQ_S_SOFT),
      M_SW: (Cfg.XLEN'(1) << (Cfg.XLEN - 1)) | Cfg.XLEN'(IRQ_M_SOFT)
  };
  child #(.it_t(it_t), .INT(INT)) dut (.sel(sel), .o(o));
endmodule
