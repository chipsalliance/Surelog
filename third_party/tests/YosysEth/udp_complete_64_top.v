module udp_complete_64_top #(
    parameter ARP_CACHE_ADDR_WIDTH = 9,
    parameter ARP_REQUEST_RETRY_COUNT = 4,
    parameter ARP_REQUEST_RETRY_INTERVAL = 125000000*2,
    parameter ARP_REQUEST_TIMEOUT = 125000000*30,
    parameter UDP_CHECKSUM_GEN_ENABLE = 1,
    parameter UDP_CHECKSUM_PAYLOAD_FIFO_ADDR_WIDTH = 11,
    parameter UDP_CHECKSUM_HEADER_FIFO_ADDR_WIDTH = 3
)
(
    input  wire        clk,
    input  wire        rst,
    
    /*
     * Ethernet frame input
     */
    input  wire        s_eth_hdr_valid,
    output wire        s_eth_hdr_ready,
    input  wire [47:0] s_eth_dest_mac,
    input  wire [47:0] s_eth_src_mac,
    input  wire [15:0] s_eth_type,
    input  wire [63:0] s_eth_payload_axis_tdata,
    input  wire [7:0]  s_eth_payload_axis_tkeep,
    input  wire        s_eth_payload_axis_tvalid,
    output wire        s_eth_payload_axis_tready,
    input  wire        s_eth_payload_axis_tlast,
    input  wire        s_eth_payload_axis_tuser,
    
    /*
     * Ethernet frame output
     */
    output wire        m_eth_hdr_valid,
    input  wire        m_eth_hdr_ready,
    output wire [47:0] m_eth_dest_mac,
    output wire [47:0] m_eth_src_mac,
    output wire [15:0] m_eth_type,
    output wire [63:0] m_eth_payload_axis_tdata,
    output wire [7:0]  m_eth_payload_axis_tkeep,
    output wire        m_eth_payload_axis_tvalid,
    input  wire        m_eth_payload_axis_tready,
    output wire        m_eth_payload_axis_tlast,
    output wire        m_eth_payload_axis_tuser,
    
    /*
     * IP input
     */
    input  wire        s_ip_hdr_valid,
    output wire        s_ip_hdr_ready,
    input  wire [5:0]  s_ip_dscp,
    input  wire [1:0]  s_ip_ecn,
    input  wire [15:0] s_ip_length,
    input  wire [7:0]  s_ip_ttl,
    input  wire [7:0]  s_ip_protocol,
    input  wire [31:0] s_ip_source_ip,
    input  wire [31:0] s_ip_dest_ip,
    input  wire [63:0] s_ip_payload_axis_tdata,
    input  wire [7:0]  s_ip_payload_axis_tkeep,
    input  wire        s_ip_payload_axis_tvalid,
    output wire        s_ip_payload_axis_tready,
    input  wire        s_ip_payload_axis_tlast,
    input  wire        s_ip_payload_axis_tuser,
    
    /*
     * IP output
     */
    output wire        m_ip_hdr_valid,
    input  wire        m_ip_hdr_ready,
    output wire [47:0] m_ip_eth_dest_mac,
    output wire [47:0] m_ip_eth_src_mac,
    output wire [15:0] m_ip_eth_type,
    output wire [3:0]  m_ip_version,
    output wire [3:0]  m_ip_ihl,
    output wire [5:0]  m_ip_dscp,
    output wire [1:0]  m_ip_ecn,
    output wire [15:0] m_ip_length,
    output wire [15:0] m_ip_identification,
    output wire [2:0]  m_ip_flags,
    output wire [12:0] m_ip_fragment_offset,
    output wire [7:0]  m_ip_ttl,
    output wire [7:0]  m_ip_protocol,
    output wire [15:0] m_ip_header_checksum,
    output wire [31:0] m_ip_source_ip,
    output wire [31:0] m_ip_dest_ip,
    output wire [63:0] m_ip_payload_axis_tdata,
    output wire [7:0]  m_ip_payload_axis_tkeep,
    output wire        m_ip_payload_axis_tvalid,
    input  wire        m_ip_payload_axis_tready,
    output wire        m_ip_payload_axis_tlast,
    output wire        m_ip_payload_axis_tuser,
    
    /*
     * UDP input
     */
    input  wire        s_udp_hdr_valid,
    output wire        s_udp_hdr_ready,
    input  wire [5:0]  s_udp_ip_dscp,
    input  wire [1:0]  s_udp_ip_ecn,
    input  wire [7:0]  s_udp_ip_ttl,
    input  wire [31:0] s_udp_ip_source_ip,
    input  wire [31:0] s_udp_ip_dest_ip,
    input  wire [15:0] s_udp_source_port,
    input  wire [15:0] s_udp_dest_port,
    input  wire [15:0] s_udp_length,
    input  wire [15:0] s_udp_checksum,
    input  wire [63:0] s_udp_payload_axis_tdata,
    input  wire [7:0]  s_udp_payload_axis_tkeep,
    input  wire        s_udp_payload_axis_tvalid,
    output wire        s_udp_payload_axis_tready,
    input  wire        s_udp_payload_axis_tlast,
    input  wire        s_udp_payload_axis_tuser,
    
    /*
     * UDP output
     */
    output wire        m_udp_hdr_valid,
    input  wire        m_udp_hdr_ready,
    output wire [47:0] m_udp_eth_dest_mac,
    output wire [47:0] m_udp_eth_src_mac,
    output wire [15:0] m_udp_eth_type,
    output wire [3:0]  m_udp_ip_version,
    output wire [3:0]  m_udp_ip_ihl,
    output wire [5:0]  m_udp_ip_dscp,
    output wire [1:0]  m_udp_ip_ecn,
    output wire [15:0] m_udp_ip_length,
    output wire [15:0] m_udp_ip_identification,
    output wire [2:0]  m_udp_ip_flags,
    output wire [12:0] m_udp_ip_fragment_offset,
    output wire [7:0]  m_udp_ip_ttl,
    output wire [7:0]  m_udp_ip_protocol,
    output wire [15:0] m_udp_ip_header_checksum,
    output wire [31:0] m_udp_ip_source_ip,
    output wire [31:0] m_udp_ip_dest_ip,
    output wire [15:0] m_udp_source_port,
    output wire [15:0] m_udp_dest_port,
    output wire [15:0] m_udp_length,
    output wire [15:0] m_udp_checksum,
    output wire [63:0] m_udp_payload_axis_tdata,
    output wire [7:0]  m_udp_payload_axis_tkeep,
    output wire        m_udp_payload_axis_tvalid,
    input  wire        m_udp_payload_axis_tready,
    output wire        m_udp_payload_axis_tlast,
    output wire        m_udp_payload_axis_tuser,

    /*
     * Status
     */
    output wire        ip_rx_busy,
    output wire        ip_tx_busy,
    output wire        udp_rx_busy,
    output wire        udp_tx_busy,
    output wire        ip_rx_error_header_early_termination,
    output wire        ip_rx_error_payload_early_termination,
    output wire        ip_rx_error_invalid_header,
    output wire        ip_rx_error_invalid_checksum,
    output wire        ip_tx_error_payload_early_termination,
    output wire        ip_tx_error_arp_failed,
    output wire        udp_rx_error_header_early_termination,
    output wire        udp_rx_error_payload_early_termination,
    output wire        udp_tx_error_payload_early_termination,

    /*
     * Configuration
     */
    input  wire [47:0] local_mac,
    input  wire [31:0] local_ip,
    input  wire [31:0] gateway_ip,
    input  wire [31:0] subnet_mask,
    input  wire        clear_arp_cache
);
udp_complete_64 #(
    .ARP_CACHE_ADDR_WIDTH(ARP_CACHE_ADDR_WIDTH),
    .ARP_REQUEST_RETRY_COUNT(ARP_REQUEST_RETRY_COUNT),
    .ARP_REQUEST_RETRY_INTERVAL(ARP_REQUEST_RETRY_INTERVAL),
    .ARP_REQUEST_TIMEOUT(ARP_REQUEST_TIMEOUT),
    .UDP_CHECKSUM_GEN_ENABLE(UDP_CHECKSUM_GEN_ENABLE),
    .UDP_CHECKSUM_PAYLOAD_FIFO_ADDR_WIDTH(UDP_CHECKSUM_PAYLOAD_FIFO_ADDR_WIDTH),
    .UDP_CHECKSUM_HEADER_FIFO_ADDR_WIDTH(UDP_CHECKSUM_HEADER_FIFO_ADDR_WIDTH)
) top
(
    .clk(clk),
    .rst(rst),
    
    .s_eth_hdr_valid(s_eth_hdr_valid),
    .s_eth_hdr_ready(s_eth_hdr_ready),
    .s_eth_dest_mac(s_eth_dest_mac),
    .s_eth_src_mac(s_eth_src_mac),
    .s_eth_type(s_eth_type),
    .s_eth_payload_axis_tdata(s_eth_payload_axis_tdata),
    .s_eth_payload_axis_tkeep(s_eth_payload_axis_tkeep),
    .s_eth_payload_axis_tvalid(s_eth_payload_axis_tvalid),
    .s_eth_payload_axis_tready(s_eth_payload_axis_tready),
    .s_eth_payload_axis_tlast(s_eth_payload_axis_tlast),
    .s_eth_payload_axis_tuser(s_eth_payload_axis_tuser),
    
    .m_eth_hdr_valid(m_eth_hdr_valid),
    .m_eth_hdr_ready(m_eth_hdr_ready),
    .m_eth_dest_mac(m_eth_dest_mac),
    .m_eth_src_mac(m_eth_src_mac),
    .m_eth_type(m_eth_type),
    .m_eth_payload_axis_tdata(m_eth_payload_axis_tdata),
    .m_eth_payload_axis_tkeep(m_eth_payload_axis_tkeep),
    .m_eth_payload_axis_tvalid(m_eth_payload_axis_tvalid),
    .m_eth_payload_axis_tready(m_eth_payload_axis_tready),
    .m_eth_payload_axis_tlast(m_eth_payload_axis_tlast),
    .m_eth_payload_axis_tuser(m_eth_payload_axis_tuser),
    
    .s_ip_hdr_valid(s_ip_hdr_valid),
    .s_ip_hdr_ready(s_ip_hdr_ready),
    .s_ip_dscp(s_ip_dscp),
    .s_ip_ecn(s_ip_ecn),
    .s_ip_length(s_ip_length),
    .s_ip_ttl(s_ip_ttl),
    .s_ip_protocol(s_ip_protocol),
    .s_ip_source_ip(s_ip_source_ip),
    .s_ip_dest_ip(s_ip_dest_ip),
    .s_ip_payload_axis_tdata(s_ip_payload_axis_tdata),
    .s_ip_payload_axis_tkeep(s_ip_payload_axis_tkeep),
    .s_ip_payload_axis_tvalid(s_ip_payload_axis_tvalid),
    .s_ip_payload_axis_tready(s_ip_payload_axis_tready),
    .s_ip_payload_axis_tlast(s_ip_payload_axis_tlast),
    .s_ip_payload_axis_tuser(s_ip_payload_axis_tuser),
    
    .m_ip_hdr_valid(m_ip_hdr_valid),
    .m_ip_hdr_ready(m_ip_hdr_ready),
    .m_ip_eth_dest_mac(m_ip_eth_dest_mac),
    .m_ip_eth_src_mac(m_ip_eth_src_mac),
    .m_ip_eth_type(m_ip_eth_type),
    .m_ip_version(m_ip_version),
    .m_ip_ihl(m_ip_ihl),
    .m_ip_dscp(m_ip_dscp),
    .m_ip_ecn(m_ip_ecn),
    .m_ip_length(m_ip_length),
    .m_ip_identification(m_ip_identification),
    .m_ip_flags(m_ip_flags),
    .m_ip_fragment_offset(m_ip_fragment_offset),
    .m_ip_ttl(m_ip_ttl),
    .m_ip_protocol(m_ip_protocol),
    .m_ip_header_checksum(m_ip_header_checksum),
    .m_ip_source_ip(m_ip_source_ip),
    .m_ip_dest_ip(m_ip_dest_ip),
    .m_ip_payload_axis_tdata(m_ip_payload_axis_tdata),
    .m_ip_payload_axis_tkeep(m_ip_payload_axis_tkeep),
    .m_ip_payload_axis_tvalid(m_ip_payload_axis_tvalid),
    .m_ip_payload_axis_tready(m_ip_payload_axis_tready),
    .m_ip_payload_axis_tlast(m_ip_payload_axis_tlast),
    .m_ip_payload_axis_tuser(m_ip_payload_axis_tuser),
    
    .s_udp_hdr_valid(s_udp_hdr_valid),
    .s_udp_hdr_ready(s_udp_hdr_ready),
    .s_udp_ip_dscp(s_udp_ip_dscp),
    .s_udp_ip_ecn(s_udp_ip_ecn),
    .s_udp_ip_ttl(s_udp_ip_ttl),
    .s_udp_ip_source_ip(s_udp_ip_source_ip),
    .s_udp_ip_dest_ip(s_udp_ip_dest_ip),
    .s_udp_source_port(s_udp_source_port),
    .s_udp_dest_port(s_udp_dest_port),
    .s_udp_length(s_udp_length),
    .s_udp_checksum(s_udp_checksum),
    .s_udp_payload_axis_tdata(s_udp_payload_axis_tdata),
    .s_udp_payload_axis_tkeep(s_udp_payload_axis_tkeep),
    .s_udp_payload_axis_tvalid(s_udp_payload_axis_tvalid),
    .s_udp_payload_axis_tready(s_udp_payload_axis_tready),
    .s_udp_payload_axis_tlast(s_udp_payload_axis_tlast),
    .s_udp_payload_axis_tuser(s_udp_payload_axis_tuser),
    
    .m_udp_hdr_valid(m_udp_hdr_valid),
    .m_udp_hdr_ready(m_udp_hdr_ready),
    .m_udp_eth_dest_mac(m_udp_eth_dest_mac),
    .m_udp_eth_src_mac(m_udp_eth_src_mac),
    .m_udp_eth_type(m_udp_eth_type),
    .m_udp_ip_version(m_udp_ip_version),
    .m_udp_ip_ihl(m_udp_ip_ihl),
    .m_udp_ip_dscp(m_udp_ip_dscp),
    .m_udp_ip_ecn(m_udp_ip_ecn),
    .m_udp_ip_length(m_udp_ip_length),
    .m_udp_ip_identification(m_udp_ip_identification),
    .m_udp_ip_flags(m_udp_ip_flags),
    .m_udp_ip_fragment_offset(m_udp_ip_fragment_offset),
    .m_udp_ip_ttl(m_udp_ip_ttl),
    .m_udp_ip_protocol(m_udp_ip_protocol),
    .m_udp_ip_header_checksum(m_udp_ip_header_checksum),
    .m_udp_ip_source_ip(m_udp_ip_source_ip),
    .m_udp_ip_dest_ip(m_udp_ip_dest_ip),
    .m_udp_source_port(m_udp_source_port),
    .m_udp_dest_port(m_udp_dest_port),
    .m_udp_length(m_udp_length),
    .m_udp_checksum(m_udp_checksum),
    .m_udp_payload_axis_tdata(m_udp_payload_axis_tdata),
    .m_udp_payload_axis_tkeep(m_udp_payload_axis_tkeep),
    .m_udp_payload_axis_tvalid(m_udp_payload_axis_tvalid),
    .m_udp_payload_axis_tready(m_udp_payload_axis_tready),
    .m_udp_payload_axis_tlast(m_udp_payload_axis_tlast),
    .m_udp_payload_axis_tuser(m_udp_payload_axis_tuser),

    .ip_rx_busy(ip_rx_busy),
    .ip_tx_busy(ip_tx_busy),
    .udp_rx_busy(udp_rx_busy),
    .udp_tx_busy(udp_tx_busy),
    .ip_rx_error_header_early_termination(ip_rx_error_header_early_termination),
    .ip_rx_error_payload_early_termination(ip_rx_error_payload_early_termination),
    .ip_rx_error_invalid_header(ip_rx_error_invalid_header),
    .ip_rx_error_invalid_checksum(ip_rx_error_invalid_checksum),
    .ip_tx_error_payload_early_termination(ip_tx_error_payload_early_termination),
    .ip_tx_error_arp_failed(ip_tx_error_arp_failed),
    .udp_rx_error_header_early_termination(udp_rx_error_header_early_termination),
    .udp_rx_error_payload_early_termination(udp_rx_error_payload_early_termination),
    .udp_tx_error_payload_early_termination(udp_tx_error_payload_early_termination),

    .local_mac(local_mac),
    .local_ip(local_ip),
    .gateway_ip(gateway_ip),
    .subnet_mask(subnet_mask),
    .clear_arp_cache(clear_arp_cache)
);
endmodule

`include "verilog-ethernet/rtl/udp_complete_64.v"
`include "verilog-ethernet/rtl/udp_64.v"
`include "verilog-ethernet/rtl/ip_complete_64.v"
`include "verilog-ethernet/rtl/ip_arb_mux.v"
`include "verilog-ethernet/rtl/../lib/axis/rtl/arbiter.v"
`include "verilog-ethernet/rtl/arp_64.v"
`include "verilog-ethernet/rtl/ip_64.v"
`include "verilog-ethernet/rtl/eth_arb_mux.v"
`include "verilog-ethernet/rtl/udp_checksum_gen_64.v"
`include "verilog-ethernet/rtl/udp_ip_tx_64.v"
`include "verilog-ethernet/rtl/udp_ip_rx_64.v"
`include "verilog-ethernet/lib/axis/rtl/axis_fifo.v"
`include "verilog-ethernet/rtl/ip_eth_tx_64.v"
`include "verilog-ethernet/rtl/ip_eth_rx_64.v"
`include "verilog-ethernet/rtl/arp_cache.v"
`include "verilog-ethernet/rtl/arp_eth_tx_64.v"
`include "verilog-ethernet/rtl/arp_eth_rx_64.v"
`include "verilog-ethernet/lib/axis/rtl/priority_encoder.v"
`include "verilog-ethernet/rtl/lfsr.v"
