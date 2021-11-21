`ifndef TNOC_FLIT_IF_SV
`define TNOC_FLIT_IF_SV
interface tnoc_flit_if
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types  types
);
//--------------------------------------------------------------
//  Localparam declarations
//--------------------------------------------------------------
  localparam  int FLITS         = (is_local_port(PORT_TYPE)) ? CHANNELS : 1;
  localparam  int CHANNEL_WIDTH = (CHANNELS >= 2) ? $clog2(CHANNELS) : 1;

//--------------------------------------------------------------
//  Variable declarations
//--------------------------------------------------------------
  typedef types.tnoc_flit tnoc_flit;

  logic [CHANNELS-1:0]  valid;
  logic [CHANNELS-1:0]  ready;
  tnoc_flit [FLITS-1:0] flit;
  logic [CHANNELS-1:0]  vc_ready;

//--------------------------------------------------------------
//  API
//--------------------------------------------------------------
  function automatic logic [CHANNELS-1:0] get_ack();
    return valid & ready;
  endfunction

  function automatic logic get_channel_ack(
    logic [CHANNEL_WIDTH-1:0] channel
  );
    return valid[channel] & ready[channel];
  endfunction

  function automatic logic get_head_flit_valid(
    logic [CHANNEL_WIDTH-1:0] channel
  );
    logic head;

    if (FLITS >= 2) begin
      head  = flit[channel].head;
    end
    else begin
      head  = flit[0].head;
    end

    return (head) ? valid[channel] : '0;
  endfunction

  function automatic logic get_head_flit_ack(
    logic [CHANNEL_WIDTH-1:0] channel
  );
    return (get_head_flit_valid(channel) && ready[channel]) ? '1 : '0;
  endfunction

  function automatic logic get_tail_flit_ack(
    logic [CHANNEL_WIDTH-1:0] channel
  );
    logic tail;

    if (FLITS >= 2) begin
      tail  = flit[channel].tail;
    end
    else begin
      tail  = flit[0].tail;
    end

    return (tail) ? get_channel_ack(channel) : '0;
  endfunction

//--------------------------------------------------------------
//  Modport
//--------------------------------------------------------------
  modport sender (
    output  valid,
    input   ready,
    output  flit,
    input   vc_ready,
    import  get_ack,
    import  get_channel_ack,
    import  get_head_flit_valid,
    import  get_head_flit_ack,
    import  get_tail_flit_ack
  );

  modport receiver (
    input   valid,
    output  ready,
    input   flit,
    output  vc_ready,
    import  get_ack,
    import  get_channel_ack,
    import  get_head_flit_valid,
    import  get_head_flit_ack,
    import  get_tail_flit_ack
  );

  modport monitor (
    input   valid,
    input   ready,
    input   flit,
    input   vc_ready,
    import  get_ack,
    import  get_channel_ack,
    import  get_head_flit_valid,
    import  get_head_flit_ack,
    import  get_tail_flit_ack
  );

//--------------------------------------------------------------
//  Debug
//--------------------------------------------------------------
`ifndef SYNTHESIS
  typedef types.tnoc_common_header  tnoc_common_header;

  for (genvar i = 0; i < CHANNELS;++i) begin : g_debug
    localparam  int FLIT_INDEX  = (is_local_port(PORT_TYPE)) ? i : 0;

    tnoc_common_header  common_header;
    always_comb begin
      if (get_head_flit_valid(i)) begin
        common_header = tnoc_common_header'(flit[FLIT_INDEX].data);
      end
    end
  end
`endif
endinterface
`endif
