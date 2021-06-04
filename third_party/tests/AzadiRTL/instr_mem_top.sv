module instr_mem_top
(
  input clk_i,
  input rst_ni,
  
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
// iccm controller interface 
  input  [11:0] iccm_ctrl_addr,
  input  [31:0] iccm_ctrl_wdata,
  input         iccm_ctrl_we,
  input         prog_rst_ni,
    

// sram interface 
  output  logic        csb,
  output  logic [11:0] addr_o,
  output  logic [31:0] wdata_o,
  output  logic [3:0]  wmask_o,
  output  logic        we_o,
  input   logic [31:0] rdata_i
);


logic rvalid;

logic        tl_we;
logic [31:0] tl_wmask;
logic [31:0] tl_wdata;
logic [11:0] tl_addr;
logic        tl_req;
logic [3:0]  mask_sel;

assign mask_sel[0] = (tl_wmask[7:0]   != 8'b0) ? 1'b1: 1'b0;
assign mask_sel[1] = (tl_wmask[15:8]  != 8'b0) ? 1'b1: 1'b0;
assign mask_sel[2] = (tl_wmask[23:16] != 8'b0) ? 1'b1: 2'b0;
assign mask_sel[3] = (tl_wmask[31:24] != 8'b0) ? 1'b1: 2'b0;

assign csb     = ~(tl_req | iccm_ctrl_we);

assign addr_o  = (prog_rst_ni) ? tl_addr  : iccm_ctrl_addr;
assign wdata_o = (prog_rst_ni) ? tl_wdata : iccm_ctrl_wdata;
assign we_o    = ~((prog_rst_ni) ? tl_we  : iccm_ctrl_we);
assign wmask_o = (prog_rst_ni) ? mask_sel : 4'b1111;


 tlul_sram_adapter #(
  .SramAw       (12),
  .SramDw       (32), 
  .Outstanding  (2),  
  .ByteAccess   (1),
  .ErrOnWrite   (0),  // 1: Writes not allowed, automatically error
  .ErrOnRead    (0)   // 1: Reads not allowed, automatically error  

) inst_mem (
  .clk_i     (clk_i),
  .rst_ni    (rst_ni),
  .tl_i      (tl_i),
  .tl_o      (tl_o), 
  .req_o     (tl_req),
  .gnt_i     (1'b1),
  .we_o      (tl_we),
  .addr_o    (tl_addr),
  .wdata_o   (tl_wdata),
  .wmask_o   (tl_wmask),
  .rdata_i   ((rst_ni) ? rdata_i: '0),
  .rvalid_i  (rvalid),
  .rerror_i  (2'b0)
);

 always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    rvalid <= 1'b0;
  end else if (iccm_ctrl_we | tl_we) begin
    rvalid <= 1'b0;
  end else begin 
    rvalid <= tl_req;
  end
 end


endmodule