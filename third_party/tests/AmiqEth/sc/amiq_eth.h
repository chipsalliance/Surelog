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
 * NAME:        amiq_eth.h
 * PROJECT:     amiq_eth
 * Description: This file includes all the C++ files which are part of
 *              amiq_eth package.
 *******************************************************************************/

#ifndef __AMIQ_ETH
//protection against multiple includes
#define __AMIQ_ETH

#include <systemc.h>
#include "sysc/utils/sc_report.h"

#include "amiq_eth_defines.cpp"
#include "amiq_eth_ethernet_protocols.cpp"
#include "amiq_eth_packer.cpp"
#include "amiq_eth_types.cpp"
#include "amiq_eth_packet.cpp"
#include "amiq_eth_packet_ether_type.cpp"
#include "amiq_eth_packet_length.cpp"
#include "amiq_eth_packet_pause.cpp"
#include "amiq_eth_packet_pfc_pause.cpp"
#include "amiq_eth_packet_snap.cpp"
#include "amiq_eth_packet_jumbo.cpp"
#include "amiq_eth_packet_magic.cpp"
#include "amiq_eth_packet_ethernet_configuration_testing.cpp"
#include "amiq_eth_packet_ipv4.cpp"
#include "amiq_eth_packet_hsr_base.cpp"
#include "amiq_eth_packet_hsr_standard.cpp"
#include "amiq_eth_packet_fcoe.cpp"
#include "amiq_eth_packet_arp.cpp"
#include "amiq_eth_packet_ptp.cpp"

#endif
