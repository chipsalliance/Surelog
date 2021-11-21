interface tnoc_axi_id_locker
  import  tnoc_axi_pkg::*;
#(
  parameter tnoc_axi_config AXI_CONFIG  = TNOC_DEFAULT_AXI_CONFIG
)(
  tnoc_axi_types  axi_types,
  input var logic i_clk,
  input var logic i_rst_n
);
  localparam  int TOTAL_ID  = 2**AXI_CONFIG.id_width;

  typedef axi_types.tnoc_axi_id tnoc_axi_id;

  logic [TOTAL_ID-1:0]  id_locked;
  logic                 lock_valid;
  tnoc_axi_id           lock_id;
  logic                 free_valid;
  tnoc_axi_id           free_id;

  function automatic logic is_locked(tnoc_axi_id id);
    return id_locked[id];
  endfunction

  function automatic void lock(logic valid, tnoc_axi_id id);
    lock_valid  = valid;
    lock_id     = id;
  endfunction

  function automatic void free(logic valid, tnoc_axi_id id);
    free_valid  = valid;
    free_id     = id;
  endfunction

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      id_locked <= '0;
    end
    else begin
      if (free_valid) begin
        id_locked[free_id]  <= '0;
      end
      if (lock_valid) begin
        id_locked[lock_id]  <= '1;
      end
    end
  end

`ifndef SYNTHESIS
  int in_flight_id_count;
  always_comb begin
    in_flight_id_count  = $countones(id_locked);
  end
`endif
endinterface
