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
 * NAME:        amiq_eth_ve_consumer.cpp
 * PROJECT:     amiq_eth
 * Description: This file declares the logic for consuming the ethernet packets
 * 				in the C side
 *******************************************************************************/

#ifndef __AMIQ_ETH_VE_CONSUMER_CPP
//protection against multiple includes
#define __AMIQ_ETH_VE_CONSUMER_CPP

#include <string>
#include <iomanip>
#include <systemc.h>
#include <tlm.h>
#include "amiq_eth.h"

using std::string;
using namespace tlm;

#define HEX(x, width) std::setw(width) << std::setfill('0') << std::hex << (x)

#include "simple_target_socket.h"
using tlm_utils::simple_target_socket;

//consumer class - it retrieves ethernet packets from System-Verilog side
class amiq_eth_ve_consumer: public sc_module {
public:
    //socket for getting ethernet packets from System-Verilog
	simple_target_socket<amiq_eth_ve_consumer> in;

	//port for sending packets to producer
	tlm_analysis_port<amiq_eth_packet> out_sc2sc;

	//cast a TLM command to a string
	//@param command - TLM command
	//@return command as string
	string get_command_as_string(tlm_command command) {
		if (command == TLM_READ_COMMAND) {
			return "TLM_READ_COMMAND";
		} else if (command == TLM_WRITE_COMMAND) {
			return "TLM_WRITE_COMMAND";
		} else if (command == TLM_IGNORE_COMMAND) {
			return "TLM_IGNORE_COMMAND";
		} else {
			return "";
		}
	}

	//cast a TLM response to a string
	//@param command - TLM response
	//@return response as string
	string get_response_as_string(tlm_response_status response) {
		if (response == TLM_OK_RESPONSE) {
			return "TLM_OK_RESPONSE";
		} else if (response == TLM_INCOMPLETE_RESPONSE) {
			return "TLM_INCOMPLETE_RESPONSE";
		} else if (response == TLM_GENERIC_ERROR_RESPONSE) {
			return "TLM_GENERIC_ERROR_RESPONSE";
		} else if (response == TLM_ADDRESS_ERROR_RESPONSE) {
			return "TLM_ADDRESS_ERROR_RESPONSE";
		} else if (response == TLM_COMMAND_ERROR_RESPONSE) {
			return "TLM_COMMAND_ERROR_RESPONSE";
		} else if (response == TLM_BURST_ERROR_RESPONSE) {
			return "TLM_BURST_ERROR_RESPONSE";
		} else if (response == TLM_BYTE_ENABLE_ERROR_RESPONSE) {
			return "TLM_BYTE_ENABLE_ERROR_RESPONSE";
		} else {
			return "";
		}
	}

	//function for printing a generic payload
	//@param gp - generic payload
	void print_gp(tlm_generic_payload &gp) {
		cout << "address: " << HEX(gp.get_address(), 16)<< ", command: " <<get_command_as_string(gp.get_command()) << std::dec << ", data_length: " << gp.get_data_length() << ", response: " <<
				get_response_as_string(gp.get_response_status()) << ", byte_enable_length: " << gp.get_byte_enable_length() << endl;
	}

	//function for printing an ethernet packet
	//@param packet - ethernet packet
	virtual void print_packet(amiq_eth_packet & packet) {
		cout << "Received in System C consumer: " << AMIQ_ETH_FIELD_SEPARATOR;
		packet.do_print(cout);
		cout << endl;
	}

	//unpack a generic payload class to an ethernet packet
	    //@param gp - generic payload
	    //@param packet - the ethernet packet in which to unpack the generic payload content
	virtual void unpack_gp_to_eth(tlm_generic_payload &gp, amiq_eth_packet & packet) {
		std::vector<char> data_vector(gp.get_data_length() * 8);
		amiq_eth_packer * local_packer = new amiq_eth_packer();
		local_packer->reset();

		for(unsigned int i = 0; i < gp.get_data_length(); i++) {
			data_vector[i] = gp.get_data_ptr()[i];
			for(int j = 7; j >= 0; j--) {
				bool bit = (data_vector[i] >> j) & 1;
				(*local_packer) << bit;
			}
		}

		packet.do_unpack((*local_packer));

		delete local_packer;
	}

    //function which creates an ethernet packet based on a particular code
    //@param code - ethernet packet code
    //@return ethernet packet
	virtual amiq_eth_packet * get_packet_by_code(sc_dt::uint64 code) {
		if(code == AMIQ_ETH_PACKET_SNAP_CODE) {
			amiq_eth_packet_snap * packet = (new amiq_eth_packet_snap());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_JUMBO_CODE) {
			amiq_eth_packet_jumbo * packet = (new amiq_eth_packet_jumbo());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_MAGIC_CODE) {
			amiq_eth_packet_magic * packet = (new amiq_eth_packet_magic());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_PAUSE_CODE) {
			amiq_eth_packet_pause * packet = (new amiq_eth_packet_pause());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_PFC_PAUSE_CODE) {
			amiq_eth_packet_pfc_pause * packet = (new amiq_eth_packet_pfc_pause());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING_CODE) {
			amiq_eth_packet_ethernet_configuration_testing * packet = (new amiq_eth_packet_ethernet_configuration_testing());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_IPV4_CODE) {
			amiq_eth_packet_ipv4 * packet = (new amiq_eth_packet_ipv4());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_HSR_STANDARD_CODE) {
			amiq_eth_packet_hsr_standard * packet = (new amiq_eth_packet_hsr_standard());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_FCOE_CODE) {
			amiq_eth_packet_fcoe * packet = (new amiq_eth_packet_fcoe());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_ARP_CODE) {
			amiq_eth_packet_arp * packet = (new amiq_eth_packet_arp());
			return packet;
		}
		else if(code == AMIQ_ETH_PACKET_PTP_CODE) {
			amiq_eth_packet_ptp * packet = (new amiq_eth_packet_ptp());
			return packet;
		}
		else {
			stringstream ss;
			ss << "Could not determine packet code for current packet type: " << std::hex << code;
			string str = ss.str();

			SC_REPORT_ERROR("AMIQ_ETH", str.c_str());
			return NULL;
		}
	}

    //function for handling the incoming generic payload
    //@param gp - generic payload
	virtual void handle_incomming_gp(tlm_generic_payload &gp) {
		amiq_eth_packet * packet = get_packet_by_code(gp.get_address());
		unpack_gp_to_eth(gp, *packet);
		print_packet(*packet);
		out_sc2sc.write(*packet);
	}

    //implementation of the socket which receives packets from System-C
    //@param t - generic payload
    //@param delay - delay of the generic payload
	virtual void b_transport(tlm_generic_payload &gp, sc_time &t) {
		handle_incomming_gp(gp);
	}

	//constructor
	amiq_eth_ve_consumer(sc_module_name nm) : in("in"), out_sc2sc("out_sc2sc") {
		in.register_b_transport(this, &amiq_eth_ve_consumer::b_transport);
	}
};

#endif
