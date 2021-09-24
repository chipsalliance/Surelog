module rv_dm #(
  parameter int              NrHarts = 1,
  parameter logic [31:0]     IdcodeValue = 32'h 0000_0001
) (
  input  logic               clk_i,       // clock
  input  logic               rst_ni,      // asynchronous reset active low, connect PoR
                                          // here, not the system reset
  input  lc_ctrl_pkg::lc_tx_t hw_debug_en_i,
  input  logic               testmode_i,
  output logic               ndmreset_o,  // non-debug module reset
  output logic               dmactive_o,  // debug module is active
  output logic [NrHarts-1:0] debug_req_o, // async debug request
  input  logic [NrHarts-1:0] unavailable_i, // communicate whether the hart is unavailable
                                            // (e.g.: power down)

  // bus device with debug memory, for an execution based technique
  input  tlul_pkg::tl_h2d_t  tl_d_i,
  output tlul_pkg::tl_d2h_t  tl_d_o,

  // bus host, for system bus accesses
  output tlul_pkg::tl_h2d_t  tl_h_o,
  input  tlul_pkg::tl_d2h_t  tl_h_i,

  input  jtag_pkg::jtag_req_t jtag_req_i,
  output jtag_pkg::jtag_rsp_t jtag_rsp_o
);

  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  logic dmi_rst_n;

endmodule // rv_dm

module dmidpi #(
  parameter string Name = "dmi0", // name of the interface (display only)
  parameter int ListenPort = 44853 // TCP port to listen on
)(
  input  bit        clk_i,
  input  bit        rst_ni,

  output bit        dmi_req_valid,
  input  bit        dmi_req_ready,
  output bit [6:0]  dmi_req_addr,
  output bit [1:0]  dmi_req_op,
  output bit [31:0] dmi_req_data,
  input  bit        dmi_rsp_valid,
  output bit        dmi_rsp_ready,
  input  bit [31:0] dmi_rsp_data,
  input  bit [1:0]  dmi_rsp_resp,
  output bit        dmi_rst_n
);
endmodule // dmidpi

module top;
  bind rv_dm dmidpi u_dmidpi (
    .clk_i,
    .rst_ni,
    .dmi_req_valid,
    .dmi_req_ready,
    .dmi_req_addr   (dmi_req.addr),
    .dmi_req_op     (dmi_req.op),
    .dmi_req_data   (dmi_req.data),
    .dmi_rsp_valid,
    .dmi_rsp_ready,
    .dmi_rsp_data   (dmi_rsp.data),
    .dmi_rsp_resp   (dmi_rsp.resp),
    .dmi_rst_n      (dmi_rst_n)
  );
endmodule // top
