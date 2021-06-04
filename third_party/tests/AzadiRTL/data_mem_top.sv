module data_mem_top
(
  input clk_i,
  input rst_ni,

// tl-ul insterface
  input tlul_pkg::tl_h2d_t tl_d_i,
  output tlul_pkg::tl_d2h_t tl_d_o,
  
// sram interface
  output  logic        csb,
  output  logic [11:0] addr_o,
  output  logic [31:0] wdata_o,
  output  logic [3:0]  wmask_o,
  output  logic        we_o,
  input   logic [31:0] rdata_i
);

  logic        tl_req;
  logic [31:0] tl_wmask;
  logic        we_i;
  logic        rvalid_o;

  assign wmask_o[0] = (tl_wmask[7:0]   != 8'b0) ? 1'b1: 1'b0;
  assign wmask_o[1] = (tl_wmask[15:8]  != 8'b0) ? 1'b1: 1'b0;
  assign wmask_o[2] = (tl_wmask[23:16] != 8'b0) ? 1'b1: 2'b0;
  assign wmask_o[3] = (tl_wmask[31:24] != 8'b0) ? 1'b1: 2'b0; 
  
  assign we_o    = ~we_i;
  assign csb     = ~tl_req;

tlul_sram_adapter #(
  .SramAw       (12),
  .SramDw       (32), 
  .Outstanding  (4),  
  .ByteAccess   (1),
  .ErrOnWrite   (0),  // 1: Writes not allowed, automatically error
  .ErrOnRead    (0) 

) data_mem (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .tl_i     (tl_d_i),
    .tl_o     (tl_d_o), 
    .req_o    (tl_req),
    .gnt_i    (1'b1),
    .we_o     (we_i),
    .addr_o   (addr_o),
    .wdata_o  (wdata_o),
    .wmask_o  (tl_wmask),
    .rdata_i  (rst_ni? rdata_i: '0), // (reset) ? rdata_o: '0
    .rvalid_i (rvalid_o),
    .rerror_i (2'b0)

);

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      rvalid_o <= 1'b0;
    end else if (we_i) begin
      rvalid_o <= 1'b0;
    end else begin 
      rvalid_o <= tl_req;
    end
  end

endmodule
