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
 * NAME:        amiq_eth_packet_ethernet_configuration_testing.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Configuration Testing Protocol Ethernet packet.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING
//protection against multiple includes
#define __AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING

using namespace std;

//Ethernet Configuration Testing Protocol packet
class amiq_eth_packet_ethernet_configuration_testing: public amiq_eth_packet_ether_type {

public:

	//SkipCount
	amiq_eth_ethernet_configuration_testing_skipcount skipcount;
	//Function
	amiq_eth_ethernet_configuration_testing_function cfg_test_function;
	//Data
	amiq_eth_ethernet_configuration_testing_data_size data_size;
	amiq_eth_data *data;
	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_ethernet_configuration_testing() {
		ether_type = SC_AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL;
		print_lists = false;
	}

	//destructor
	virtual ~amiq_eth_packet_ethernet_configuration_testing() {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet_ether_type::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SKIPCOUNT: " << std::hex << skipcount.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FUNCTION: " << std::dec << cfg_test_function << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Data Size: " << std::dec << data_size.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < data_size.to_uint(); index++) {
				out << "Data [" << index << "]" << std::hex << data[index].to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "FCS: " << std::hex << fcs.to_uint();
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_data data_item;
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, skipcount);

		amiq_eth_ethernet_configuration_testing_function_w int_f_type;
		int_f_type = cfg_test_function;
		amiq_eth_do_pack(packer, int_f_type);

		amiq_eth_do_pack(packer, data_size);

		for (unsigned int index = 0; index < data_size.to_uint(); index++) {
			amiq_eth_do_pack(packer, data[index]);
		}

		amiq_eth_do_pack(packer, fcs);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_do_unpack(packer, skipcount);

		amiq_eth_ethernet_configuration_testing_function_w local_f_type;
		amiq_eth_do_unpack(packer, local_f_type);
		cfg_test_function = amiq_eth_ethernet_configuration_testing_function(local_f_type.to_int());

		amiq_eth_do_unpack(packer, data_size);

		amiq_eth_data data_item;
		data = new amiq_eth_data[data_size.to_int()];
		for (unsigned int index = 0; index < data_size.to_uint(); index++) {
			amiq_eth_do_unpack(packer, data_item);
			data[index] = data_item;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING_CODE);

		return result;
	}

};

#endif
