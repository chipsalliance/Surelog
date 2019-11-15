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
 * NAME:        amiq_eth_pkg.sv
 * PROJECT:     amiq_eth
 * Description: This file includes all the files which are part of
 *              amiq_eth package.
 *******************************************************************************/

`ifndef __AMIQ_ETH_PKG
	//protection against multiple includes
	`define __AMIQ_ETH_PKG

package amiq_eth_pkg;

	`include "uvm_macros.svh"

	import uvm_pkg::*;

	`include "amiq_eth_defines.sv"
	`include "amiq_eth_ethernet_protocols.sv"
	`include "amiq_eth_types.sv"
	`include "amiq_eth_packet.sv"
	`include "amiq_eth_pcap_util.sv"
	`include "amiq_eth_packet_length.sv"
	`include "amiq_eth_packet_ether_type.sv"
	`include "amiq_eth_packet_snap.sv"
	`include "amiq_eth_packet_jumbo.sv"
	`include "amiq_eth_packet_magic.sv"
	`include "amiq_eth_packet_pause.sv"
	`include "amiq_eth_packet_pfc_pause.sv"
	`include "amiq_eth_packet_ethernet_configuration_testing.sv"
	`include "amiq_eth_packet_hsr_base.sv"
	`include "amiq_eth_packet_hsr_standard.sv"
	`include "amiq_eth_packet_ipv4.sv"
	`include "amiq_eth_packet_fcoe.sv"
	`include "amiq_eth_packet_arp.sv"
	`include "amiq_eth_packet_ptp.sv"

endpackage

`endif