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
 * NAME:        amiq_eth_ve_producer.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the logic for producing ethernet packets
 *                 and sending them to System-Verilog side
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_PRODUCER
	//protection against multiple includes
	`define __AMIQ_ETH_VE_PRODUCER

//producer class - it sends ethernet packets to System-C side
class amiq_eth_ve_producer extends uvm_component;
	`uvm_component_utils(amiq_eth_ve_producer)

	//socket for sending ethernet packets to System-C
	uvm_tlm_b_initiator_socket #() out_sv2sc;

	//UVM analysis port for sending to the scoreboard the ethernet packets which where also send to System-C
    uvm_analysis_port#(amiq_eth_packet) out_sv2sv;

    //gets the ID used in messaging
    //@return message ID
	virtual function string get_id();
		return "AMIQ_ETH";
	endfunction

	//constructor
	//@param name - name of the component instance
	//@param parent - parent of the component instance
	function new(string name = "", uvm_component parent);
		super.new(name, parent);
		out_sv2sc = new("out_sv2sc", this);
		out_sv2sv = new("out_sv2sv", this);
	endfunction
	
	//task for sending an ethernet packet to System-C
	//@param packet - ethernet packet
	virtual task send_to_sc(amiq_eth_packet packet);
		uvm_tlm_gp gp;
		uvm_tlm_time delay = new("delay",0);

		`uvm_info(get_id(), $sformatf("Sending to SC: %s%s", `AMIQ_ETH_FIELD_SEPARATOR, packet.convert2string()), UVM_MEDIUM);

		gp = packet.to_generic_payload();


		out_sv2sv.write(packet);

		out_sv2sc.b_transport(gp,delay);
	endtask
endclass

`endif
