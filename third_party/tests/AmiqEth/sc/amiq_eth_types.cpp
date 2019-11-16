/******************************************************************************
 * (C) Copyright 2014 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        amiq_eth_types.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare all types used in amiq_eth package
 *******************************************************************************/

#ifndef __AMIQ_ETH_TYPES
//protection against multiple includes
#define __AMIQ_ETH_TYPES

//**************************************************************************
//General types
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_PREAMBLE_WIDTH> amiq_eth_preamble;

typedef sc_bv<AMIQ_ETH_SFD_WIDTH> amiq_eth_sfd;

typedef sc_bv<AMIQ_ETH_ADDRESS_WIDTH> amiq_eth_address;

typedef sc_bv<AMIQ_ETH_LENGTH_TYPE_WIDTH> amiq_eth_length_type;

typedef sc_bv<AMIQ_ETH_FCS_WIDTH> amiq_eth_fcs;

typedef sc_bv<AMIQ_ETH_DATA_WIDTH> amiq_eth_data;

typedef sc_bv<AMIQ_ETH_EXTENSION_WIDTH> amiq_eth_extension;

typedef enum {
	SC_AMIQ_ETH_IPV4 = AMIQ_ETH_IPV4,
	SC_AMIQ_ETH_ARP = AMIQ_ETH_ARP,
	SC_AMIQ_ETH_WAKE_ON_LAN = AMIQ_ETH_WAKE_ON_LAN,
	SC_AMIQ_ETH_IETF_TRILL = AMIQ_ETH_IETF_TRILL,
	SC_AMIQ_ETH_DECNET_PHASE_IV = AMIQ_ETH_DECNET_PHASE_IV,
	SC_AMIQ_ETH_RARP = AMIQ_ETH_RARP,
	SC_AMIQ_ETH_APPLE_TALK = AMIQ_ETH_APPLE_TALK,
	SC_AMIQ_ETH_AARP = AMIQ_ETH_AARP,
	SC_AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING = AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING,
	SC_AMIQ_ETH_IPX_1 = AMIQ_ETH_IPX_1,
	SC_AMIQ_ETH_IPX_2 = AMIQ_ETH_IPX_2,
	SC_AMIQ_ETH_QNX_QNET = AMIQ_ETH_QNX_QNET,
	SC_AMIQ_ETH_IPV6 = AMIQ_ETH_IPV6,
	SC_AMIQ_ETH_MAC_CONTROL = AMIQ_ETH_MAC_CONTROL,
	SC_AMIQ_ETH_SLOW_PROTOCOLS = AMIQ_ETH_SLOW_PROTOCOLS,
	SC_AMIQ_ETH_COBRANET = AMIQ_ETH_COBRANET,
	SC_AMIQ_ETH_MPLS_UNICAST = AMIQ_ETH_MPLS_UNICAST,
	SC_AMIQ_ETH_MPLS_MULTICAST = AMIQ_ETH_MPLS_MULTICAST,
	SC_AMIQ_ETH_PPPOE_DISCOVERY = AMIQ_ETH_PPPOE_DISCOVERY,
	SC_AMIQ_ETH_PPPOE_SESSION = AMIQ_ETH_PPPOE_SESSION,
	SC_AMIQ_ETH_JUMBO_FRAMES = AMIQ_ETH_JUMBO_FRAMES,
	SC_AMIQ_ETH_HOMEPLUG = AMIQ_ETH_HOMEPLUG,
	SC_AMIQ_ETH_EAP_OVER_LAN = AMIQ_ETH_EAP_OVER_LAN,
	SC_AMIQ_ETH_PROFINET = AMIQ_ETH_PROFINET,
	SC_AMIQ_ETH_SCSI_OVER_ETHERNET = AMIQ_ETH_SCSI_OVER_ETHERNET,
	SC_AMIQ_ETH_ATA_OVER_ETHERNET = AMIQ_ETH_ATA_OVER_ETHERNET,
	SC_AMIQ_ETH_ETHERCAT = AMIQ_ETH_ETHERCAT,
	SC_AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING = AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING,
	SC_AMIQ_ETH_POWERLINK = AMIQ_ETH_POWERLINK,
	SC_AMIQ_ETH_LLDP = AMIQ_ETH_LLDP,
	SC_AMIQ_ETH_SERCOS_III = AMIQ_ETH_SERCOS_III,
	SC_AMIQ_ETH_HOMEPLUG_AV_MME = AMIQ_ETH_HOMEPLUG_AV_MME,
	SC_AMIQ_ETH_MEDIA_REDUNDANCY = AMIQ_ETH_MEDIA_REDUNDANCY,
	SC_AMIQ_ETH_MAC_SECURITY = AMIQ_ETH_MAC_SECURITY,
	SC_AMIQ_ETH_PTP = AMIQ_ETH_PTP,
	SC_AMIQ_ETH_CFM_OAM = AMIQ_ETH_CFM_OAM,
	SC_AMIQ_ETH_FCOE = AMIQ_ETH_FCOE,
	SC_AMIQ_ETH_FCOE_INIT = AMIQ_ETH_FCOE_INIT,
	SC_AMIQ_ETH_ROCE = AMIQ_ETH_ROCE,
	SC_AMIQ_ETH_HSR = AMIQ_ETH_HSR,
	SC_AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL = AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL,
	SC_AMIQ_ETH_Q_IN_Q = AMIQ_ETH_Q_IN_Q,
	SC_AMIQ_ETH_LLT_FOR_CLUSTER_SERVER = AMIQ_ETH_LLT_FOR_CLUSTER_SERVER
} ethernet_legal_protocols;

//**************************************************************************
//Types required by Ethernet Magic packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_MAGIC_PACKET_PATTERN_WIDTH> amiq_eth_magic_packet_pattern;

typedef sc_bv<AMIQ_ETH_MAGIC_CLIENT_DATA_SIZE_WIDTH> amiq_eth_magic_cliet_data_size;

typedef sc_bv<AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH> amiq_eth_magic_synch_stream;

//**************************************************************************
//Types required by Ethernet SNAP packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_SNAP_PACKET_PROTOCOL_IDENTIFIER_WIDTH> amiq_eth_snap_protocol_identifier;

//**************************************************************************
//Types required by Ethernet Jumbo packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_JUMBO_CLIENT_DATA_SIZE_WIDTH> amiq_eth_jumbo_client_data_size;

//**************************************************************************
//Types required by Ethernet Priority Flow Control packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_PFC_OPCODE_WIDTH> amiq_eth_pfc_opcode;

typedef sc_bv<AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_WIDTH> amiq_eth_pfc_class_enable_vector;

typedef sc_bv<AMIQ_ETH_PFC_PARAMETER_WIDTH> amiq_eth_pfc_parameter;

//**************************************************************************
//Types required by Ethernet Pause packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_PAUSE_OPCODE_WIDTH> amiq_eth_pause_opcode;

typedef sc_bv<AMIQ_ETH_PAUSE_PARAMETER_WIDTH> amiq_eth_pause_parameter;

//**************************************************************************
//Types required by Ethernet Configuration Testing Protocol packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_SKIPCOUNT_WIDTH> amiq_eth_ethernet_configuration_testing_skipcount;

typedef enum {
	REPLY = AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_REPLY_FUNCTION, FORWARD = AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FORWARD_FUNCTION
} amiq_eth_ethernet_configuration_testing_function;

typedef sc_bv<AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_DATA_SIZE_WIDTH> amiq_eth_ethernet_configuration_testing_data_size;

typedef sc_bv<AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FUNCTION_WIDTH> amiq_eth_ethernet_configuration_testing_function_w;

//**************************************************************************
//Types required by Ethernet High-availability Seamless Redundancy packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_HSR_PATH_WIDTH> amiq_eth_hsr_path;

typedef sc_bv<AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH> amiq_eth_hsr_size;

typedef sc_bv<AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH> amiq_eth_hsr_seq;

//**************************************************************************
//Types required by Ethernet Internet Protocol Version 4 packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_VERSION_WIDTH> amiq_eth_ipv4_header_version;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_IHL_WIDTH> amiq_eth_ipv4_header_ihl;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_DSCP_WIDTH> amiq_eth_ipv4_header_dscp;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_ECN_WIDTH> amiq_eth_ipv4_header_ecn;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_TOTAL_LENGTH_WIDTH> amiq_eth_ipv4_header_total_length;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_IDENTIFICATION_WIDTH> amiq_eth_ipv4_header_identification;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_FLAGS_WIDTH> amiq_eth_ipv4_header_flags;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_FRAGMENT_OFFSET_WIDTH> amiq_eth_ipv4_header_fragment_offset;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_TTL_WIDTH> amiq_eth_ipv4_header_ttl;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_PROTOCOL_WIDTH> amiq_eth_ipv4_header_protocol;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_CHECKSUM_WIDTH> amiq_eth_ipv4_header_checksum;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_SOURCE_IP_ADDRESS_WIDTH> amiq_eth_ipv4_header_source_ip_address;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_DESTINATION_IP_ADDRESS_WIDTH> amiq_eth_ipv4_header_destination_ip_address;

typedef sc_bv<AMIQ_ETH_IPV4_HEADER_OPTION_WIDTH> amiq_eth_ipv4_header_option;

//**************************************************************************
//Types required by Ethernet Address Resolution Protocol packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_ARP_HTYPE_WIDTH> amiq_eth_arp_htype;

typedef sc_bv<AMIQ_ETH_ARP_PTYPE_WIDTH> amiq_eth_arp_ptype;

typedef sc_bv<AMIQ_ETH_ARP_HLEN_WIDTH> amiq_eth_arp_hlen;

typedef sc_bv<AMIQ_ETH_ARP_PLEN_WIDTH> amiq_eth_arp_plen;

typedef sc_bv<AMIQ_ETH_ARP_OPER_WIDTH> amiq_eth_arp_oper;

typedef sc_bv<AMIQ_ETH_ARP_SHA_WIDTH> amiq_eth_arp_sha;

typedef sc_bv<AMIQ_ETH_ARP_SPA_WIDTH> amiq_eth_arp_spa;

typedef sc_bv<AMIQ_ETH_ARP_THA_WIDTH> amiq_eth_arp_tha;

typedef sc_bv<AMIQ_ETH_ARP_TPA_WIDTH> amiq_eth_arp_tpa;

//**************************************************************************
//Types required by Ethernet Fibre Channel over Ethernet (FCoE) packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_FCOE_EOF_WIDTH> amiq_eth_fcoe_eof;

typedef enum {
	SC_AMIQ_ETH_FCOE_EOFn = AMIQ_ETH_FCOE_EOFn, SC_AMIQ_ETH_FCOE_EOFt = AMIQ_ETH_FCOE_EOFt, SC_AMIQ_ETH_FCOE_EOFni = AMIQ_ETH_FCOE_EOFni, SC_AMIQ_ETH_FCOE_EOFa = AMIQ_ETH_FCOE_EOFa
} amiq_eof_legal;

typedef sc_bv<AMIQ_ETH_FCOE_FRAME_SIZE_WIDTH> amiq_eth_fcoe_frame_size;

typedef sc_bv<AMIQ_ETH_FCOE_RESERVED_SIZE_WIDTH> amiq_eth_fcoe_reserved_size;

typedef sc_bv<AMIQ_ETH_FCOE_VERSION_WIDTH> amiq_eth_fcoe_version;

typedef sc_bv<AMIQ_ETH_FCOE_SOF_WIDTH> amiq_eth_fcoe_sof;

typedef enum {
	SC_AMIQ_ETH_FCOE_SOFf = AMIQ_ETH_FCOE_SOFf,
	SC_AMIQ_ETH_FCOE_SOFi2 = AMIQ_ETH_FCOE_SOFi2,
	SC_AMIQ_ETH_FCOE_SOFn2 = AMIQ_ETH_FCOE_SOFn2,
	SC_AMIQ_ETH_FCOE_SOFi3 = AMIQ_ETH_FCOE_SOFi3,
	SC_AMIQ_ETH_FCOE_SOFn3 = AMIQ_ETH_FCOE_SOFn3
} amiq_sof_legal;

//**************************************************************************
//Types required by Ethernet Precision Time Protocol packet
//*****************************************************************************

typedef sc_bv<AMIQ_ETH_PTP_TRANSPORT_SPECIFIC_WIDTH> amiq_eth_ptp_transport_specific_w;
typedef enum {
	PTP_in_IEEE1588 = AMIQ_ETH_PTP_IN_IEEE1588, PTP_in_802_1_as = AMIQ_ETH_PTP_IN_802_1_AS
} amiq_eth_ptp_transport_specific;

typedef sc_bv<AMIQ_ETH_PTP_MESSAGE_TYPE_WIDTH> amiq_eth_ptp_message_type_w;
typedef enum {
	PTP_SyncMessage = AMIQ_ETH_PTP_SYNCMESSAGE,
	PTP_Delay_ReqMessage = AMIQ_ETH_PTP_DELAY_REQMESSAGE,
	PTP_Pdelay_ReqMessage = AMIQ_ETH_PTP_PDELAY_REQMESSAGE,
	PTP_Pdelay_RespMessage = AMIQ_ETH_PTP_PDELAY_RESPMESSAGE,
	PTP_Follow_UpMessage = AMIQ_ETH_PTP_FOLLOW_UPMESSAGE,
	PTP_Delay_RespMessage = AMIQ_ETH_PTP_DELAY_RESPMESSAGE,
	PTP_Pdelay_Resp_Follow_UpMessage = AMIQ_ETH_PTP_PDELAY_RESP_FOLLOW_UPMESSAGE,
	PTP_AnnounceMessage = AMIQ_ETH_PTP_ANNOUNCEMESSAGE,
	PTP_SignallingMessage = AMIQ_ETH_PTP_SIGNALLINGMESSAGE,
	PTP_ManagementMessage = AMIQ_ETH_PTP_MANAGEMENTMESSAGE
} amiq_eth_ptp_message_type;

typedef sc_bv<AMIQ_ETH_PTP_VERSION_WIDTH> amiq_eth_ptp_version;

typedef sc_bv<AMIQ_ETH_PTP_RESERVED_WIDTH> amiq_eth_ptp_reserved;

typedef sc_bv<AMIQ_ETH_PTP_MESSAGE_LENGTH_WIDTH> amiq_eth_ptp_message_length;

typedef sc_bv<AMIQ_ETH_PTP_DOMAIN_NUMBER_WIDTH> amiq_eth_ptp_domain_number;

typedef sc_bv<AMIQ_ETH_PTP_FLAGS_WIDTH> amiq_eth_ptp_flags;

typedef sc_bv<AMIQ_ETH_PTP_CORRECTION_FIELD_WIDTH> amiq_eth_ptp_correction_field;

typedef sc_bv<AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_WIDTH> amiq_eth_ptp_source_port_identity;

typedef sc_bv<AMIQ_ETH_PTP_SEQUENCE_ID_WIDTH> amiq_eth_ptp_sequence_id;

typedef sc_bv<AMIQ_ETH_PTP_CONTROL_FIELD_WIDTH> amiq_eth_ptp_control_field_w;
typedef enum {
	PTP_SyncMessage_ctrl = AMIQ_ETH_PTP_SYNCMESSAGE_CTRL,
	PTP_Delay_ReqMessage_ctrl = AMIQ_ETH_PTP_DELAY_REQMESSAGE_CTRL,
	PTP_Follow_UpMessage_ctrl = AMIQ_ETH_PTP_FOLLOW_UPMESSAGE_CTRL,
	PTP_Delay_RespMessage_ctrl = AMIQ_ETH_PTP_DELAY_RESPMESSAGE_CTRL,
	PTP_ManagementMessage_ctrl = AMIQ_ETH_PTP_MANAGEMENTMESSAGE_CTRL
} amiq_eth_ptp_control_field;

typedef sc_bv<AMIQ_ETH_PTP_LOG_MESSAGE_WIDTH> amiq_eth_ptp_log_message;

typedef sc_bv<AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_WIDTH> amiq_eth_ptp_origin_timestamp;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_CURRENT_UTC_OFFSET_WIDTH> amiq_eth_ptp_announce_message_current_utc_offset;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_PRIORITY_1_WIDTH> amiq_eth_ptp_announce_message_grandmaster_priority_1;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_CLOCK_QUALITY_WIDTH> amiq_eth_ptp_announce_message_grandmaster_clock_quality;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_PRIORITY_2_WIDTH> amiq_eth_ptp_announce_message_grandmaster_priority_2;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_IDENTITY_WIDTH> amiq_eth_ptp_announce_message_grandmaster_identity;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_STEPS_REMOVED_WIDTH> amiq_eth_ptp_announce_message_steps_removed;

typedef sc_bv<AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_TIME_SOURCE_WIDTH> amiq_eth_ptp_announce_message_time_source;

#endif
