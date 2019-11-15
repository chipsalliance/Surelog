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
 * NAME:        amiq_eth_ve_producer.cpp
 * PROJECT:     amiq_eth
 * Description: This file declares the logic for producing ethernet packets
 * 				and sending them to System-Verilog side
 *******************************************************************************/

#ifndef __AMIQ_ETH_VE_PRODUCER_CPP
//protection against multiple includes
#define __AMIQ_ETH_VE_PRODUCER_CPP

#include <string>
#include <iomanip>
#include <systemc.h>
#include <tlm.h>
#include "amiq_eth.h"

using std::string;
using namespace tlm;

#include "simple_initiator_socket.h"
using tlm_utils::simple_initiator_socket;

//producer class - it sends ethernet packets to System-Verilog side
class amiq_eth_ve_producer: public tlm_analysis_if<amiq_eth_packet>, sc_module {
public:

	//socket for sending ethernet packets to System-Verilog
	simple_initiator_socket<amiq_eth_ve_producer> out;

	//constructor
	amiq_eth_ve_producer(sc_module_name nm) {

	}

	//function for printing an ethernet packet
	//@param packet - ethernet packet
	virtual void print_packet(const amiq_eth_packet & packet) {
		cout << "Sending to SV from SystemC: " << AMIQ_ETH_FIELD_SEPARATOR;
		packet.do_print(cout);
		cout << endl;
	}

	//function for sending an ethernet packet
	//@param packet - ethernet packet
	virtual void write(const amiq_eth_packet &packet) {
		tlm_generic_payload * gp = packet.to_generic_payload();
		print_packet(packet);
		sc_time delay;
		delay = sc_time(0, SC_NS);
		out->b_transport(*gp, delay);
	}
};

#endif
