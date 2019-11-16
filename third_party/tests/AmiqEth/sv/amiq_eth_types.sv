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
 * NAME:        amiq_eth_types.sv
 * PROJECT:     amiq_eth
 * Description: This file declare all types used in amiq_eth package
 *******************************************************************************/

`ifndef __AMIQ_ETH_TYPES
    //protection against multiple includes
    `define __AMIQ_ETH_TYPES

//{{{**************************************************************************
//General types
//*****************************************************************************

typedef bit[`AMIQ_ETH_PREAMBLE_WIDTH - 1:0] amiq_eth_preamble;

typedef bit[`AMIQ_ETH_SFD_WIDTH - 1:0] amiq_eth_sfd;

typedef bit[`AMIQ_ETH_ADDRESS_WIDTH - 1:0] amiq_eth_address;

typedef bit[`AMIQ_ETH_LENGTH_TYPE_WIDTH - 1:0] amiq_eth_length;

typedef bit[`AMIQ_ETH_FCS_WIDTH - 1:0] amiq_eth_fcs;

typedef bit[`AMIQ_ETH_DATA_WIDTH - 1:0] amiq_eth_data;

typedef bit[`AMIQ_ETH_EXTENSION_WIDTH - 1:0] amiq_eth_extension;

typedef enum bit[`AMIQ_ETH_LENGTH_TYPE_WIDTH-1:0] {
    AMIQ_ETH_IPV4 = `AMIQ_ETH_IPV4 ,
    AMIQ_ETH_ARP = `AMIQ_ETH_ARP ,
    AMIQ_ETH_WAKE_ON_LAN = `AMIQ_ETH_WAKE_ON_LAN ,
    AMIQ_ETH_IETF_TRILL = `AMIQ_ETH_IETF_TRILL ,
    AMIQ_ETH_DECNET_PHASE_IV = `AMIQ_ETH_DECNET_PHASE_IV ,
    AMIQ_ETH_RARP = `AMIQ_ETH_RARP ,
    AMIQ_ETH_APPLE_TALK = `AMIQ_ETH_APPLE_TALK ,
    AMIQ_ETH_AARP = `AMIQ_ETH_AARP ,
    AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING = `AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING ,
    AMIQ_ETH_IPX_1 = `AMIQ_ETH_IPX_1 ,
    AMIQ_ETH_IPX_2 = `AMIQ_ETH_IPX_2 ,
    AMIQ_ETH_QNX_QNET = `AMIQ_ETH_QNX_QNET,
    AMIQ_ETH_IPV6 = `AMIQ_ETH_IPV6,
    AMIQ_ETH_MAC_CONTROL = `AMIQ_ETH_MAC_CONTROL ,
    AMIQ_ETH_SLOW_PROTOCOLS = `AMIQ_ETH_SLOW_PROTOCOLS ,
    AMIQ_ETH_COBRANET = `AMIQ_ETH_COBRANET ,
    AMIQ_ETH_MPLS_UNICAST = `AMIQ_ETH_MPLS_UNICAST ,
    AMIQ_ETH_MPLS_MULTICAST = `AMIQ_ETH_MPLS_MULTICAST ,
    AMIQ_ETH_PPPOE_DISCOVERY = `AMIQ_ETH_PPPOE_DISCOVERY ,
    AMIQ_ETH_PPPOE_SESSION = `AMIQ_ETH_PPPOE_SESSION ,
    AMIQ_ETH_JUMBO_FRAMES = `AMIQ_ETH_JUMBO_FRAMES ,
    AMIQ_ETH_HOMEPLUG = `AMIQ_ETH_HOMEPLUG ,
    AMIQ_ETH_EAP_OVER_LAN = `AMIQ_ETH_EAP_OVER_LAN ,
    AMIQ_ETH_PROFINET = `AMIQ_ETH_PROFINET ,
    AMIQ_ETH_SCSI_OVER_ETHERNET = `AMIQ_ETH_SCSI_OVER_ETHERNET ,
    AMIQ_ETH_ATA_OVER_ETHERNET = `AMIQ_ETH_ATA_OVER_ETHERNET ,
    AMIQ_ETH_ETHERCAT = `AMIQ_ETH_ETHERCAT ,
    AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING = `AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING ,
    AMIQ_ETH_POWERLINK = `AMIQ_ETH_POWERLINK ,
    AMIQ_ETH_LLDP = `AMIQ_ETH_LLDP ,
    AMIQ_ETH_SERCOS_III = `AMIQ_ETH_SERCOS_III ,
    AMIQ_ETH_HOMEPLUG_AV_MME = `AMIQ_ETH_HOMEPLUG_AV_MME ,
    AMIQ_ETH_MEDIA_REDUNDANCY = `AMIQ_ETH_MEDIA_REDUNDANCY ,
    AMIQ_ETH_MAC_SECURITY = `AMIQ_ETH_MAC_SECURITY ,
    AMIQ_ETH_PTP = `AMIQ_ETH_PTP ,
    AMIQ_ETH_CFM_OAM = `AMIQ_ETH_CFM_OAM ,
    AMIQ_ETH_FCOE = `AMIQ_ETH_FCOE ,
    AMIQ_ETH_FCOE_INIT = `AMIQ_ETH_FCOE_INIT ,
    AMIQ_ETH_ROCE = `AMIQ_ETH_ROCE ,
    AMIQ_ETH_HSR = `AMIQ_ETH_HSR ,
    AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL = `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL ,
    AMIQ_ETH_Q_IN_Q = `AMIQ_ETH_Q_IN_Q ,
    AMIQ_ETH_LLT_FOR_CLUSTER_SERVER = `AMIQ_ETH_LLT_FOR_CLUSTER_SERVER
} amiq_eth_ether_type;

//}}}

//{{{**************************************************************************
//Types required by Ethernet SNAP packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_SNAP_PROTOCOL_IDENTIFIER_WIDTH - 1:0] amiq_eth_snap_protocol_identifier;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Jumbo packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_JUMBO_CLIENT_DATA_SIZE_WIDTH - 1:0] amiq_eth_jumbo_client_data_size;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Priority Flow Control packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_PFC_OPCODE_WIDTH - 1:0] amiq_eth_pfc_opcode;

typedef bit[`AMIQ_ETH_PFC_PARAMETER_WIDTH - 1:0] amiq_eth_pfc_parameter;

typedef bit[`AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_WIDTH - 1:0] amiq_eth_pfc_class_enable_vector;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Pause packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_PAUSE_PARAMETER_WIDTH - 1:0] amiq_eth_pause_parameter;

typedef bit[`AMIQ_ETH_PAUSE_OPCODE_WIDTH - 1:0] amiq_eth_pause_opcode;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Configuration Testing Protocol packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_SKIPCOUNT_WIDTH - 1:0] amiq_eth_ethernet_configuration_testing_skipcount;

typedef enum bit[`AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FUNCTION_WIDTH - 1:0] {
    REPLY = `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_REPLY_FUNCTION ,
    FORWARD = `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FORWARD_FUNCTION
} amiq_eth_ethernet_configuration_testing_function;

//}}}

//{{{**************************************************************************
//Types required by Ethernet High-availability Seamless Redundancy packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_HSR_PATH_WIDTH - 1:0] amiq_eth_hsr_path;

typedef bit[`AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH - 1:0] amiq_eth_hsr_size;

typedef bit[`AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH - 1:0] amiq_eth_hsr_seq;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Internet Protocol Version 4 packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_IPV4_HEADER_VERSION_WIDTH - 1:0] amiq_eth_ipv4_header_version;

typedef bit[`AMIQ_ETH_IPV4_HEADER_IHL_WIDTH - 1:0] amiq_eth_ipv4_header_ihl;

typedef bit[`AMIQ_ETH_IPV4_HEADER_DSCP_WIDTH - 1:0] amiq_eth_ipv4_header_dscp;

typedef bit[`AMIQ_ETH_IPV4_HEADER_ECN_WIDTH - 1:0] amiq_eth_ipv4_header_ecn;

typedef bit[`AMIQ_ETH_IPV4_HEADER_TOTAL_LENGTH_WIDTH - 1:0] amiq_eth_ipv4_header_total_length;

typedef bit[`AMIQ_ETH_IPV4_HEADER_IDENTIFICATION_WIDTH - 1:0] amiq_eth_ipv4_header_identification;

typedef bit[`AMIQ_ETH_IPV4_HEADER_FLAGS_WIDTH - 1:0] amiq_eth_ipv4_header_flags;

typedef bit[`AMIQ_ETH_IPV4_HEADER_FRAGMENT_OFFSET_WIDTH - 1:0] amiq_eth_ipv4_header_fragment_offset;

typedef bit[`AMIQ_ETH_IPV4_HEADER_TTL_WIDTH - 1:0] amiq_eth_ipv4_header_ttl;

typedef bit[`AMIQ_ETH_IPV4_HEADER_PROTOCOL_WIDTH - 1:0] amiq_eth_ipv4_header_protocol;

typedef bit[`AMIQ_ETH_IPV4_HEADER_CHECKSUM_WIDTH - 1:0] amiq_eth_ipv4_header_checksum;

typedef bit[`AMIQ_ETH_IPV4_HEADER_SOURCE_IP_ADDRESS_WIDTH - 1:0] amiq_eth_ipv4_header_source_ip_address;

typedef bit[`AMIQ_ETH_IPV4_HEADER_DESTINATION_IP_ADDRESS_WIDTH - 1:0] amiq_eth_ipv4_header_destination_ip_address;

typedef bit[`AMIQ_ETH_IPV4_HEADER_OPTION_WIDTH - 1:0] amiq_eth_ipv4_header_option;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Address Resolution Protocol packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_ARP_HTYPE_WIDTH - 1:0] amiq_eth_arp_htype;

typedef bit[`AMIQ_ETH_ARP_PTYPE_WIDTH - 1:0] amiq_eth_arp_ptype;

typedef bit[`AMIQ_ETH_ARP_HLEN_WIDTH - 1:0] amiq_eth_arp_hlen;

typedef bit[`AMIQ_ETH_ARP_PLEN_WIDTH - 1:0] amiq_eth_arp_plen;

typedef bit[`AMIQ_ETH_ARP_OPER_WIDTH - 1:0] amiq_eth_arp_oper;

typedef bit[`AMIQ_ETH_ARP_SHA_WIDTH - 1:0] amiq_eth_arp_sha;

typedef bit[`AMIQ_ETH_ARP_SPA_WIDTH - 1:0] amiq_eth_arp_spa;

typedef bit[`AMIQ_ETH_ARP_THA_WIDTH - 1:0] amiq_eth_arp_tha;

typedef bit[`AMIQ_ETH_ARP_TPA_WIDTH - 1:0] amiq_eth_arp_tpa;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Fibre Channel over Ethernet (FCoE) packet
//*****************************************************************************

typedef bit[`AMIQ_ETH_FCOE_VERSION_WIDTH - 1:0] amiq_eth_fcoe_version;

typedef enum bit[`AMIQ_ETH_FCOE_SOF_WIDTH - 1:0] {
    AMIQ_ETH_FCOE_SOFf = `AMIQ_ETH_FCOE_SOFf,
    AMIQ_ETH_FCOE_SOFi2 = `AMIQ_ETH_FCOE_SOFi2,
    AMIQ_ETH_FCOE_SOFn2 = `AMIQ_ETH_FCOE_SOFn2,
    AMIQ_ETH_FCOE_SOFi3 = `AMIQ_ETH_FCOE_SOFi3,
    AMIQ_ETH_FCOE_SOFn3 = `AMIQ_ETH_FCOE_SOFn3
} amiq_eth_fcoe_sof;

typedef enum bit[`AMIQ_ETH_FCOE_EOF_WIDTH - 1:0] {
    AMIQ_ETH_FCOE_EOFn = `AMIQ_ETH_FCOE_EOFn,
    AMIQ_ETH_FCOE_EOFt = `AMIQ_ETH_FCOE_EOFt,
    AMIQ_ETH_FCOE_EOFni = `AMIQ_ETH_FCOE_EOFni,
    AMIQ_ETH_FCOE_EOFa = `AMIQ_ETH_FCOE_EOFa
} amiq_eth_fcoe_eof;

//}}}

//{{{**************************************************************************
//Types required by Ethernet Precision Time Protocol packet
//*****************************************************************************

typedef enum bit[`AMIQ_ETH_PTP_TRANSPORT_SPECIFIC_WIDTH - 1:0] {
    PTP_in_IEEE1588 = `AMIQ_ETH_PTP_IN_IEEE1588,
    PTP_in_802_1_as = `AMIQ_ETH_PTP_IN_802_1_AS
} amiq_eth_ptp_transport_specific;

typedef enum bit[`AMIQ_ETH_PTP_MESSAGE_TYPE_WIDTH - 1:0] {
    PTP_SyncMessage = `AMIQ_ETH_PTP_SYNCMESSAGE,
    PTP_Delay_ReqMessage = `AMIQ_ETH_PTP_DELAY_REQMESSAGE,
    PTP_Pdelay_ReqMessage = `AMIQ_ETH_PTP_PDELAY_REQMESSAGE,
    PTP_Pdelay_RespMessage = `AMIQ_ETH_PTP_PDELAY_RESPMESSAGE,
    PTP_Follow_UpMessage = `AMIQ_ETH_PTP_FOLLOW_UPMESSAGE,
    PTP_Delay_RespMessage = `AMIQ_ETH_PTP_DELAY_RESPMESSAGE,
    PTP_Pdelay_Resp_Follow_UpMessage = `AMIQ_ETH_PTP_PDELAY_RESP_FOLLOW_UPMESSAGE,
    PTP_AnnounceMessage = `AMIQ_ETH_PTP_ANNOUNCEMESSAGE,
    PTP_SignallingMessage = `AMIQ_ETH_PTP_SIGNALLINGMESSAGE,
    PTP_ManagementMessage = `AMIQ_ETH_PTP_MANAGEMENTMESSAGE
} amiq_eth_ptp_message_type;

typedef bit[`AMIQ_ETH_PTP_VERSION_WIDTH - 1:0] amiq_eth_ptp_version;

typedef bit[`AMIQ_ETH_PTP_MESSAGE_LENGTH_WIDTH - 1:0] amiq_eth_ptp_message_length;

typedef bit[`AMIQ_ETH_PTP_DOMAIN_NUMBER_WIDTH - 1:0] amiq_eth_ptp_domain_number;

typedef bit[`AMIQ_ETH_PTP_FLAGS_WIDTH - 1:0] amiq_eth_ptp_flags;

typedef bit[`AMIQ_ETH_PTP_CORRECTION_FIELD_WIDTH - 1:0] amiq_eth_ptp_correction_field;

typedef bit[`AMIQ_ETH_PTP_SEQUENCE_ID_WIDTH - 1:0] amiq_eth_ptp_sequence_id;

typedef enum bit[`AMIQ_ETH_PTP_CONTROL_FIELD_WIDTH - 1:0] {
    PTP_SyncMessage_ctrl = `AMIQ_ETH_PTP_SYNCMESSAGE_CTRL,
    PTP_Delay_ReqMessage_ctrl = `AMIQ_ETH_PTP_DELAY_REQMESSAGE_CTRL,
    PTP_Follow_UpMessage_ctrl = `AMIQ_ETH_PTP_FOLLOW_UPMESSAGE_CTRL,
    PTP_Delay_RespMessage_ctrl = `AMIQ_ETH_PTP_DELAY_RESPMESSAGE_CTRL,
    PTP_ManagementMessage_ctrl = `AMIQ_ETH_PTP_MANAGEMENTMESSAGE_CTRL
} amiq_eth_ptp_control_field_type;

typedef bit[`AMIQ_ETH_PTP_LOG_MESSAGE_WIDTH - 1:0] amiq_eth_ptp_log_message;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_CURRENT_UTC_OFFSET_WIDTH - 1:0] amiq_eth_ptp_announce_message_current_utc_offset;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_PRIORITY_1_WIDTH - 1:0] amiq_eth_ptp_announce_message_grandmaster_priority_1;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_CLOCK_QUALITY_WIDTH - 1:0] amiq_eth_ptp_announce_message_grandmaster_clock_quality;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_PRIORITY_2_WIDTH - 1:0] amiq_eth_ptp_announce_message_grandmaster_priority_2;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_GRANDMASTER_IDENTITY_WIDTH - 1:0] amiq_eth_ptp_announce_message_grandmaster_identity;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_STEPS_REMOVED_WIDTH - 1:0] amiq_eth_ptp_announce_message_steps_removed;

typedef bit[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_TIME_SOURCE_WIDTH - 1:0] amiq_eth_ptp_announce_message_time_source;

//}}}

`endif