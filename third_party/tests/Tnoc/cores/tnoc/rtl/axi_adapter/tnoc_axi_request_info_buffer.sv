interface tnoc_axi_request_info_buffer
  import  tnoc_axi_pkg::*;
#(
  parameter tnoc_axi_config AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG,
  parameter type            REQUEST_INFO  = logic,
  parameter bit             USE_UPDATE    = 0
)(
  tnoc_axi_types  axi_types,
  input var logic i_clk,
  input var logic i_rst_n
);
  typedef axi_types.tnoc_axi_id tnoc_axi_id;

  localparam  int ENTRIES = 2**AXI_CONFIG.id_width;

  logic         initialize_valid;
  tnoc_axi_id   initialize_id;
  REQUEST_INFO  initialize_info;
  logic         update_valid;
  tnoc_axi_id   update_id;
  REQUEST_INFO  update_info;
  REQUEST_INFO  request_info[ENTRIES];

  function automatic void initialize(
    logic         valid,
    tnoc_axi_id   id,
    REQUEST_INFO  info
  );
    initialize_valid  = valid;
    initialize_id     = id;
    initialize_info   = info;
  endfunction

  function automatic void update(
    logic         valid,
    tnoc_axi_id   id,
    REQUEST_INFO  info
  );
    update_valid  = valid;
    update_id     = id;
    update_info   = info;
  endfunction

  function automatic REQUEST_INFO get(tnoc_axi_id id);
    return request_info[id];
  endfunction

  always_ff @(posedge i_clk) begin
    if (initialize_valid) begin
      request_info[initialize_id] <= initialize_info;
    end
    if (USE_UPDATE && update_valid) begin
      request_info[update_id] <= update_info;
    end
  end
endinterface
