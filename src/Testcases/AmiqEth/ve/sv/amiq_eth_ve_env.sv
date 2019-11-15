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
 * NAME:        amiq_eth_ve_env.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the verification environment for testing
 *                 the packing/unpacking logic of ethernet packets and 
 *                 send/receive logic from System-Verilog to System-C
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_ENV
    //protection against multiple includes
    `define __AMIQ_ETH_VE_ENV

//verification environment class
class amiq_eth_ve_env extends uvm_component;
    `uvm_component_utils(amiq_eth_ve_env)
    
    //producer
    amiq_eth_ve_producer producer;
    
    //consumer
    amiq_eth_ve_consumer consumer;
    
    //scoreboard
    amiq_eth_ve_scoreboard scoreboard;
    
    //set a new ethernet packet to producer class
    //@param packet - ethernet packet
    task set(amiq_eth_packet packet);
        producer.send_to_sc(packet);
    endtask
    
    //get the ethernet packet available in the scoreboard
    //@return ethernet packet
    function amiq_eth_packet get();
        return scoreboard.received_packet;
    endfunction
    
    //gets the ID used in messaging
    //@return message ID
    virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction
    
    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);    
    endfunction
    
    //UVM build phase
    //@param phase - current phase
    function void build_phase(uvm_phase phase);
        super.build();
        producer = amiq_eth_ve_producer::type_id::create("producer", this);
        consumer = amiq_eth_ve_consumer::type_id::create("consumer", this);
        scoreboard = amiq_eth_ve_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
    //UVM connect phase
    //@param phase - current phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        uvmc_tlm #()::connect(producer.out_sv2sc, "sv2sc_connection");
        uvmc_tlm #()::connect(consumer.in_sc2sv, "sc2sv_connection");
        
        producer.out_sv2sv.connect(scoreboard.input_port_from_producer);
        consumer.out_sv2sv.connect(scoreboard.input_port_from_consumer);
    endfunction
endclass

`endif
