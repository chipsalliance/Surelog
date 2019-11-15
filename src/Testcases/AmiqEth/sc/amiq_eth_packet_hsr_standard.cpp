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
 * NAME:        amiq_eth_packet_hsr_standard.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet HSR standard packet.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_HSR_STANDARD
//protection against multiple includes
#define __AMIQ_ETH_PACKET_HSR_STANDARD

using namespace std;

//Ethernet HSR standard packet
class amiq_eth_packet_hsr_standard: public amiq_eth_packet_hsr_base {

public:

	//LPDU
	ethernet_legal_protocols protocol;
	amiq_eth_data *lpdu;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_hsr_standard() {
		print_lists = false;
	}

	//destructor
	virtual ~amiq_eth_packet_hsr_standard() {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet_hsr_base::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		amiq_eth_length_type int_protocol = protocol;
		out << "PROTOCOL: " << std::hex << int_protocol.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		int sz = size.to_int() - (AMIQ_ETH_HSR_PATH_WIDTH + AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH + AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH + AMIQ_ETH_HSR_STANDARD_PROTOCOL_WIDTH) / 8;
		out << "LPDU_SIZE: " << std::hex << sz << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (int index = 0; index < sz; index++) {
				out << "LPDU [" << index << "]" << std::hex << lpdu[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "FCS: " << std::hex << fcs.to_int();
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_data lpdu_item;
		amiq_eth_packet_hsr_base::do_pack(packer);

		amiq_eth_length_type int_protocol = protocol;
		amiq_eth_do_pack(packer, int_protocol);

		int sz = size.to_int() - (AMIQ_ETH_HSR_PATH_WIDTH + AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH + AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH + AMIQ_ETH_HSR_STANDARD_PROTOCOL_WIDTH) / 8;
		for (int index = 0; index < sz; index++) {
			amiq_eth_do_pack(packer, lpdu[index]);
		}

		amiq_eth_do_pack(packer, fcs);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_hsr_base::do_unpack(packer);

		amiq_eth_length_type local_protocol;
		amiq_eth_do_unpack(packer, local_protocol);
		protocol = (ethernet_legal_protocols) local_protocol.to_int();

		amiq_eth_data lpdu_item;
		unsigned int sz = size.to_uint() - (AMIQ_ETH_HSR_PATH_WIDTH + AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH + AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH + AMIQ_ETH_HSR_STANDARD_PROTOCOL_WIDTH) / 8;
		lpdu = new amiq_eth_data[sz];
		for (unsigned int index = 0; index < sz; index++) {
			amiq_eth_do_unpack(packer, lpdu_item);
			lpdu[index] = lpdu_item;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_HSR_STANDARD_CODE);

		return result;
	}

};

#endif
