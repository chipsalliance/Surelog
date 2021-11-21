`ifndef TNOC_PORT_CONTROL_IF_SV
`define TNOC_PORT_CONTROL_IF_SV
interface tnoc_port_control_if
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG  = TNOC_DEFAULT_PACKET_CONFIG
);
  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;

  logic [CHANNELS-1:0]  request;
  logic [CHANNELS-1:0]  grant;
  logic [CHANNELS-1:0]  free;
  logic [CHANNELS-1:0]  start_of_packet;
  logic [CHANNELS-1:0]  end_of_packet;

  modport requester (
    output  request,
    input   grant,
    output  free,
    output  start_of_packet,
    output  end_of_packet
  );

  modport controller (
    input   request,
    output  grant,
    input   free,
    input   start_of_packet,
    input   end_of_packet
  );
endinterface
`endif
