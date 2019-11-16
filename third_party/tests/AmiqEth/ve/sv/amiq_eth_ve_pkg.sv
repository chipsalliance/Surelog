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
 * NAME:        amiq_eth_ve_pkg.sv
 * PROJECT:     amiq_eth
 * Description: This file includes all the files which are part of
 *              amiq_eth verification environment.
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_PKG
    //protection against multiple includes
    `define __AMIQ_ETH_VE_PKG
    
`include "amiq_eth_pkg.sv"

`ifndef AMIQ_ETH_SKIP_UVMC_INCLUDE 
	`include "uvmc_pkg.sv"
`endif

`ifndef AMIQ_ETH_WIRESHARK_FILE
    `define AMIQ_ETH_WIRESHARK_FILE "wireshark_file"
`endif

package amiq_eth_ve_pkg;
    import uvm_pkg::*;
    import uvmc_pkg::*;
    import amiq_eth_pkg::*;
    
    `include "amiq_eth_ve_producer.sv"
    `include "amiq_eth_ve_consumer.sv"
    `include "amiq_eth_ve_scoreboard.sv"
    `include "amiq_eth_ve_env.sv"
    `include "amiq_eth_ve_test_basic.sv"
    `include "amiq_eth_ve_test_packets.sv"
    `include "amiq_eth_ve_test_magic_packets.sv"
    `include "amiq_eth_ve_test_jumbo_packets.sv"
    `include "amiq_eth_ve_test_snap_packets.sv"
    `include "amiq_eth_ve_test_pause_packets.sv"
    `include "amiq_eth_ve_test_pfc_pause_packets.sv"
    `include "amiq_eth_ve_test_ipv4_packets.sv"
    `include "amiq_eth_ve_test_ethernet_configuration_testing_packets.sv"
    `include "amiq_eth_ve_test_hsr_standard_packets.sv"
    `include "amiq_eth_ve_test_fcoe_packets.sv"
    `include "amiq_eth_ve_test_arp_packets.sv"
    `include "amiq_eth_ve_test_ptp_packets.sv"
    
endpackage 

`endif
    