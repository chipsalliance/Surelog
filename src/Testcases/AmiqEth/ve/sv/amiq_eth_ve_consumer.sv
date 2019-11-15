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
 * NAME:        amiq_eth_ve_consumer.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the logic for consuming the ethernet packets
 *                 in the System-Verilog side
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_CONSUMER
    //protection against multiple includes
    `define __AMIQ_ETH_VE_CONSUMER

//consumer class - it retrieves ethernet packets from System-C side
class amiq_eth_ve_consumer extends uvm_component;
    `uvm_component_utils(amiq_eth_ve_consumer)

    //gets the ID used in messaging
    //@return message ID
    virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction

    //socket for getting ethernet packets from System-C
    uvm_tlm_b_target_socket #(amiq_eth_ve_consumer) in_sc2sv;

    //UVM analysis port for sending to the scoreboard the ethernet packets which came from System-C
    uvm_analysis_port#(amiq_eth_packet) out_sv2sv;

    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);
        in_sc2sv = new("in_sc2sv", this);
        out_sv2sv = new("out_sv2sv", this);
    endfunction

    //function which creates an ethernet packet based on a particular code
    //@param code - ethernet packet code
    //@return ethernet packet
    virtual function amiq_eth_packet get_packet_by_code(bit[63:0] code);
        if(code == `AMIQ_ETH_PACKET_SNAP_CODE) begin
            amiq_eth_packet_snap packet = amiq_eth_packet_snap::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_JUMBO_CODE) begin
            amiq_eth_packet_jumbo packet = amiq_eth_packet_jumbo::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_MAGIC_CODE) begin
            amiq_eth_packet_magic packet = amiq_eth_packet_magic::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_PAUSE_CODE) begin
            amiq_eth_packet_pause packet = amiq_eth_packet_pause::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_PFC_PAUSE_CODE) begin
            amiq_eth_packet_pfc_pause packet = amiq_eth_packet_pfc_pause::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING_CODE) begin
            amiq_eth_packet_ethernet_configuration_testing packet = amiq_eth_packet_ethernet_configuration_testing::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_IPV4_CODE) begin
            amiq_eth_packet_ipv4 packet = amiq_eth_packet_ipv4::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_HSR_STANDARD_CODE) begin
            amiq_eth_packet_hsr_standard packet= amiq_eth_packet_hsr_standard::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_FCOE_CODE) begin
            amiq_eth_packet_fcoe packet= amiq_eth_packet_fcoe::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_ARP_CODE) begin
            amiq_eth_packet_arp packet= amiq_eth_packet_arp::type_id::create("packet");
            return packet;
        end
        else if(code == `AMIQ_ETH_PACKET_PTP_CODE) begin
            amiq_eth_packet_ptp packet= amiq_eth_packet_ptp::type_id::create("packet");
            return packet;
        end
        else begin
            `uvm_fatal(get_id(), $sformatf("Could not convert generic payload to a known Ethernet packet - address code: %X", code))
        end
    endfunction

    //unpack a generic payload class to an ethernet packet
    //@param gp - generic payload
    //@param packet - the ethernet packet in which to unpack the generic payload content
    virtual function void unpack_gp_to_eth(ref uvm_tlm_gp gp, ref amiq_eth_packet packet);
        byte unsigned bytestream[];
        gp.get_data(bytestream);
        
        void'(packet.unpack_bytes(bytestream));
    endfunction
    
    //function for handling the incoming generic payload
    //@param gp - generic payload
    virtual function void handle_incomming_gp(uvm_tlm_gp gp);
        amiq_eth_packet packet = get_packet_by_code(gp.get_address());
        unpack_gp_to_eth(gp, packet);
        out_sv2sv.write(packet);
    endfunction
    
    //implementation of the socket which receives packets from System-C
    //@param t - generic payload
    //@param delay - delay of the generic payload
    virtual task b_transport (uvm_tlm_gp t, uvm_tlm_time delay);
        handle_incomming_gp(t);
    endtask

endclass

`endif
