
module pwm_top (

  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,


  output        pwm_o,
  output        pwm_o_2,
  output        pwm1_oe,
  output        pwm2_oe

);


localparam int AW = 8;
localparam int DW = 32;
localparam int DBW = DW/8;  

logic         re;
logic         we;
logic [7:0]   addr;
logic [31:0]  wdata;
logic [3:0]   be;
logic [31:0]  rdata;
logic         err;

//assign err = '0;

pwm pwm_core(

.clk_i      (clk_i),												
.rst_ni     (rst_ni),												

.re_i       (re),												
.we_i       (we),												
.addr_i     (addr),												
.wdata_i    (wdata),												
.be_i       (be),										    
.rdata_o    (rdata),												
//.error_o    (err),												
.o_pwm      (pwm_o),
.o_pwm_2    (pwm_o_2),
.oe_pwm1    (pwm1_oe),
.oe_pwm2    (pwm2_oe)

);

tlul_adapter_reg #(
  .RegAw(AW),
  .RegDw(DW)
) u_reg_if (
  .clk_i,
  .rst_ni,

  .tl_i (tl_i),
  .tl_o (tl_o),

  .we_o    (we),
  .re_o    (re),
  .addr_o  (addr),
  .wdata_o (wdata),
  .be_o    (be),
  .rdata_i (rdata),
  .error_i (1'b0)
);

endmodule
