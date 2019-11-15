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
 * NAME:        amiq_eth_ve_test_arp_packets.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the test for ARP packets.
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_TEST_ARP_PACKETS
    //protection against multiple includes
    `define __AMIQ_ETH_VE_TEST_ARP_PACKETS

//test class for generating arp ethernet packets and test SV-SC round trip logic
class amiq_eth_ve_test_arp_packets extends amiq_eth_ve_test_packets;
    `uvm_component_utils(amiq_eth_ve_test_arp_packets)

    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

    //generate correct type of ethernet class
    //@return ethernet packet
    virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_arp result = amiq_eth_packet_arp::type_id::create("packet");

        if(!result.randomize()) begin
            `uvm_error("AMIQ_ETH", "Problem randomizing the ARP packet");
        end
       
        return result;
    endfunction

endclass

`endif
