`ifndef TNOC_BFM_FLIT_IF_SV
`define TNOC_BFM_FLIT_IF_SV
interface tnoc_bfm_flit_if (
  input var bit i_clk,
  input var bit i_rst_n
);
  import  tnoc_bfm_types_pkg::tnoc_bfm_flit;

  bit           valid;
  bit           ready;
  tnoc_bfm_flit flit;
  bit           vc_ready;
  bit           ack;

  always_comb begin
    ack = valid & ready;
  end

  clocking master_cb @(posedge i_clk);
    output  valid;
    input   ready;
    output  flit;
    input   vc_ready;
    input   ack;
  endclocking

  clocking slave_cb @(posedge i_clk);
    input   valid;
    output  ready;
    input   flit;
    output  vc_ready;
    input   ack;
  endclocking

  clocking monitor_cb @(posedge i_clk);
    input valid;
    input ready;
    input flit;
    input vc_ready;
    input ack;
  endclocking

  modport initiator(
    output  valid,
    input   ready,
    output  flit,
    input   vc_ready,
    input   ack
  );

  modport target(
    input   valid,
    output  ready,
    input   flit,
    output  vc_ready,
    input   ack
  );

  modport monitor (
    input valid,
    input ready,
    input flit,
    input vc_ready,
    input ack
  );

  ast_keep_request_until_transfer_is_completed:
  assert property (
    @(posedge i_clk)
    (valid && (!ready)) |=>
      ($stable(valid) && $stable(flit))
  );
endinterface
`endif
