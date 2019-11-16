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
 * NAME:        amiq_eth_ve_scoreboard.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the scoreboard class. The main purpose of 
 *                 this class is to check if the generated System-Verilog packets
 *                 are the same with the ones which are returned from System-C.
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_SCOREBOARD
    //protection against multiple includes
    `define __AMIQ_ETH_VE_SCOREBOARD

`uvm_analysis_imp_decl(_from_producer)
`uvm_analysis_imp_decl(_from_consumer)

//scoreboard class
class amiq_eth_ve_scoreboard extends uvm_component;
    `uvm_component_utils(amiq_eth_ve_scoreboard)
    
    virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction
    
    bit has_checks = 1;
    
    amiq_eth_packet producer_packets[$];
    
    amiq_eth_packet received_packet;

    uvm_analysis_imp_from_producer#(amiq_eth_packet, amiq_eth_ve_scoreboard) input_port_from_producer;
    uvm_analysis_imp_from_consumer#(amiq_eth_packet, amiq_eth_ve_scoreboard) input_port_from_consumer;
    
    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);
        input_port_from_producer = new("input_port_from_producer", this);
        input_port_from_consumer = new("input_port_from_consumer", this);
    endfunction
    
    //write implementation of the UVM analysis port
    //@param packet - ethernet packet coming from producer class
    virtual function void write_from_producer(amiq_eth_packet packet);
        if(has_checks == 1) begin
            producer_packets.push_back(packet);
        end
    endfunction
    
    //write implementation of the UVM analysis port
    //@param packet - ethernet packet coming from consumer class
    virtual function void write_from_consumer(amiq_eth_packet local_received_packet);
        received_packet = local_received_packet;
        if(has_checks == 1) begin
            if(producer_packets.size() == 0) begin
                `uvm_fatal(get_id(), $sformatf("It was received from consumer a packet while producer list is empty: %s", local_received_packet.convert2string()))    
            end
            
            begin
                amiq_eth_packet expected_packet = producer_packets.pop_front();
                
                if(expected_packet.compare(local_received_packet) == 0) begin
                    `uvm_error(get_id(), $sformatf("Packet mismatch: \nExpected: %s\nReceived: %s", 
                        expected_packet.convert2string(), local_received_packet.convert2string()));
                end
                else begin
                    `uvm_info(get_id(), $sformatf("Successfully detected round trip for packet: %s", local_received_packet.convert2string()), UVM_LOW)
                end
            end
        end
    endfunction
    
    //UVM final phase
    //@param phase - current phase
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
    
        if(producer_packets.size() != 0) begin
            `uvm_error(get_id(), $sformatf("There are still %0d packets in the scoreboard", producer_packets.size()))    
        end
    endfunction
    
endclass

`endif
