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
 * NAME:        amiq_eth_ethernet_protocols.sv
 * PROJECT:     amiq_eth
 * Description: This file declare all the values of the "Ethernet type" field 
 *                 from the Ethernet packet described in 
 *                     docs/ieee_802.3-2012/802.3-2012_section1.pdf, 
 *                     chapter 3. Media Access Control (MAC) frame and packet specifications
 *******************************************************************************/

`ifndef __AMIQ_ETH_ETHERNET_PROTOCOLS
    //protection against multiple includes
    `define __AMIQ_ETH_ETHERNET_PROTOCOLS

`ifndef AMIQ_ETH_IPV4
    //Internet Protocol version 4 (IPv4)
    `define AMIQ_ETH_IPV4 16'h0800
`endif    

`ifndef AMIQ_ETH_ARP
    //Address Resolution Protocol (ARP)
    `define AMIQ_ETH_ARP 16'h0806
`endif    

`ifndef AMIQ_ETH_WAKE_ON_LAN
    //Wake-on-LAN
    `define AMIQ_ETH_WAKE_ON_LAN 16'h0842
`endif    

`ifndef AMIQ_ETH_IETF_TRILL
    //IETF TRILL Protocol
    `define AMIQ_ETH_IETF_TRILL 16'h22F3
`endif    

`ifndef AMIQ_ETH_DECNET_PHASE_IV
    //DECnet Phase IV
    `define AMIQ_ETH_DECNET_PHASE_IV 16'h6003
`endif    

`ifndef AMIQ_ETH_RARP
    //Reverse Address Resolution Protocol
    `define AMIQ_ETH_RARP 16'h8035
`endif    

`ifndef AMIQ_ETH_APPLE_TALK
    //AppleTalk (Ethertalk)
    `define AMIQ_ETH_APPLE_TALK 16'h809B
`endif    

`ifndef AMIQ_ETH_AARP
    //AppleTalk Address Resolution Protocol (AARP)
    `define AMIQ_ETH_AARP 16'h80F3
`endif    
    
`ifndef AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING
    //VLAN-tagged frame (IEEE 802.1Q) & Shortest Path Bridging IEEE 802.1aq
    `define AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING 16'h8100
`endif    

`ifndef AMIQ_ETH_IPX_1
    //IPX 1
    `define AMIQ_ETH_IPX_1 16'h8137
`endif    

`ifndef AMIQ_ETH_IPX_2
    //IPX 2
    `define AMIQ_ETH_IPX_2 16'h8138
`endif    

`ifndef AMIQ_ETH_QNX_QNET
    //QNX Qnet
    `define AMIQ_ETH_QNX_QNET 16'h8204
`endif    

`ifndef AMIQ_ETH_IPV6
    //Internet Protocol Version 6 (IPv6)
    `define AMIQ_ETH_IPV6 16'h86DD
`endif    

`ifndef AMIQ_ETH_MAC_CONTROL
    //Ethernet flow control
    `define AMIQ_ETH_MAC_CONTROL 16'h8808
`endif    


`ifndef AMIQ_ETH_SLOW_PROTOCOLS
    //Slow Protocols (IEEE 802.3)
    `define AMIQ_ETH_SLOW_PROTOCOLS 16'h8809
`endif    

`ifndef AMIQ_ETH_COBRANET
    //CobraNet
    `define AMIQ_ETH_COBRANET 16'h8819
`endif    

`ifndef AMIQ_ETH_MPLS_UNICAST
    //MPLS unicast
    `define AMIQ_ETH_MPLS_UNICAST 16'h8847
`endif    

`ifndef AMIQ_ETH_MPLS_MULTICAST
    //MPLS multicast
    `define AMIQ_ETH_MPLS_MULTICAST 16'h8848
`endif    

`ifndef AMIQ_ETH_PPPOE_DISCOVERY
    //PPPoE Discovery Stage
    `define AMIQ_ETH_PPPOE_DISCOVERY 16'h8863
`endif    

`ifndef AMIQ_ETH_PPPOE_SESSION
    //PPPoE Session Stage
    `define AMIQ_ETH_PPPOE_SESSION 16'h8864
`endif    

`ifndef AMIQ_ETH_JUMBO_FRAMES
    //Jumbo Frames
    `define AMIQ_ETH_JUMBO_FRAMES 16'h8870
`endif    

`ifndef AMIQ_ETH_HOMEPLUG
    //HomePlug 1.0 MME
    `define AMIQ_ETH_HOMEPLUG 16'h887B
`endif    

`ifndef AMIQ_ETH_EAP_OVER_LAN
    //EAP over LAN (IEEE 802.1X)
    `define AMIQ_ETH_EAP_OVER_LAN 16'h888E
`endif    

`ifndef AMIQ_ETH_PROFINET
    //PROFINET Protocol
    `define AMIQ_ETH_PROFINET 16'h8892
`endif    

`ifndef AMIQ_ETH_SCSI_OVER_ETHERNET
    //HyperSCSI (SCSI over Ethernet)
    `define AMIQ_ETH_SCSI_OVER_ETHERNET 16'h889A
`endif    

`ifndef AMIQ_ETH_ATA_OVER_ETHERNET
    //ATA over Ethernet
    `define AMIQ_ETH_ATA_OVER_ETHERNET 16'h88A2
`endif    

`ifndef AMIQ_ETH_ETHERCAT
    //EtherCAT Protocol
    `define AMIQ_ETH_ETHERCAT 16'h88A4
`endif    

`ifndef AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING
    //Provider Bridging (IEEE 802.1ad) & Shortest Path Bridging IEEE 802.1aq
    `define AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING 16'h88A8
`endif    

`ifndef AMIQ_ETH_POWERLINK
    //Ethernet Powerlink
    `define AMIQ_ETH_POWERLINK 16'h88AB
`endif    

`ifndef AMIQ_ETH_LLDP
    //Link Layer Discovery Protocol (LLDP)
    `define AMIQ_ETH_LLDP 16'h88CC
`endif    

`ifndef AMIQ_ETH_SERCOS_III
    //SERCOS III
    `define AMIQ_ETH_SERCOS_III 16'h88CD
`endif    

`ifndef AMIQ_ETH_HOMEPLUG_AV_MME
    //HomePlug AV MME
    `define AMIQ_ETH_HOMEPLUG_AV_MME 16'h88E1
`endif    

`ifndef AMIQ_ETH_MEDIA_REDUNDANCY
    //Media Redundancy Protocol (IEC62439-2)
    `define AMIQ_ETH_MEDIA_REDUNDANCY 16'h88E3
`endif    

`ifndef AMIQ_ETH_MAC_SECURITY
    //MAC security (IEEE 802.1AE)
    `define AMIQ_ETH_MAC_SECURITY 16'h88E5
`endif    

`ifndef AMIQ_ETH_PTP
    //Precision Time Protocol (PTP) over Ethernet (IEEE 1588)
    `define AMIQ_ETH_PTP 16'h88F7
`endif    

`ifndef AMIQ_ETH_CFM_OAM
    //IEEE 802.1ag Connectivity Fault Management (CFM) Protocol / ITU-T Recommendation Y.1731 (OAM)
    `define AMIQ_ETH_CFM_OAM 16'h8902
`endif    

`ifndef AMIQ_ETH_FCOE
    //Fibre Channel over Ethernet (FCoE)
    `define AMIQ_ETH_FCOE 16'h8906
`endif    

`ifndef AMIQ_ETH_FCOE_INIT
    //FCoE Initialization Protocol
    `define AMIQ_ETH_FCOE_INIT 16'h8914
`endif    

`ifndef AMIQ_ETH_ROCE
    //RDMA over Converged Ethernet (RoCE)
    `define AMIQ_ETH_ROCE 16'h8915
`endif    

`ifndef AMIQ_ETH_HSR
    //High-availability Seamless Redundancy (HSR)
    `define AMIQ_ETH_HSR 16'h892F
`endif    

`ifndef AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL
    //Ethernet Configuration Testing Protocol
    `define AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL 16'h9000
`endif    

`ifndef AMIQ_ETH_Q_IN_Q
    //Q-in-Q
    `define AMIQ_ETH_Q_IN_Q 16'h9100
`endif    

`ifndef AMIQ_ETH_LLT_FOR_CLUSTER_SERVER
    //Veritas Low Latency Transport (LLT) for Veritas Cluster Server
    `define AMIQ_ETH_LLT_FOR_CLUSTER_SERVER 16'hCAFE
`endif    

`endif