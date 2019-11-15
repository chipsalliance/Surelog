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
 * NAME:        amiq_eth_packet_pfc_pause.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the PFC Pause Ethernet packet.
 * 				The definition of this packet is described in IEEE 802.3-2012
 * 				For more details see file docs/ieee_802.3-2012/802.3-2012_section2.pdf,pag. 766
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_PFC_PAUSE
//protection against multiple includes
#define __AMIQ_ETH_PACKET_PFC_PAUSE

using namespace std;

//Ethernet PFC Pause packet
class amiq_eth_packet_pfc_pause: public amiq_eth_packet_ether_type {

public:

	//MAC CONTROL OPCODE
	amiq_eth_pause_opcode pfc_opcode;

	//Class Enable Vector
	amiq_eth_pfc_class_enable_vector pfc_class_enable_vector;

	//Time
	amiq_eth_pause_parameter *pfc_parameter;

	//Pad
	amiq_eth_data *pad;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	unsigned int pfc_parameter_size;

	unsigned int pad_size;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_pfc_pause() {
		pad = NULL;
		destination_address = AMIQ_ETH_PFC_PACKET_DESTINATION_ADDRESS;
		ether_type = SC_AMIQ_ETH_MAC_CONTROL;
		pfc_opcode = AMIQ_ETH_PFC_OPCODE;
		pfc_parameter_size = AMIQ_ETH_PFC_NUMBER_OF_PARAMETERS;
		pfc_parameter = new amiq_eth_pause_parameter[pfc_parameter_size];
		pad_size = AMIQ_ETH_PAYLOAD_SIZE_MIN
				- (AMIQ_ETH_PFC_OPCODE_WIDTH + AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_WIDTH + AMIQ_ETH_PFC_PARAMETER_WIDTH * AMIQ_ETH_PFC_NUMBER_OF_PARAMETERS) / AMIQ_ETH_DATA_WIDTH;
		pad = new amiq_eth_data[pad_size];
		for (unsigned int index = 0; index < pad_size; index++) {
			pad[index] = 0;
		}
		print_lists = false;
	}

	//destructor
	virtual ~amiq_eth_packet_pfc_pause() {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet_ether_type::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PFC OPCODE: " << std::dec << pfc_opcode.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PFC Class Enable Vector: " << std::dec << pfc_class_enable_vector.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PFC Parameter Size: " << std::dec << pfc_parameter_size << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < pfc_parameter_size; index++) {
				out << "PFC_PARAMETER [" << index << "]" << std::hex << pfc_parameter[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "Pad Size: " << std::dec << pad_size << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FCS: " << std::hex << fcs.to_int();
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, pfc_opcode);

		amiq_eth_do_pack(packer, pfc_class_enable_vector);

		for (unsigned int index = 0; index < pfc_parameter_size; index++) {
			amiq_eth_do_pack(packer, pfc_parameter[index]);
		}

		for (unsigned int index = 0; index < pad_size; index++) {
			amiq_eth_do_pack(packer, pad[index]);
		}

		amiq_eth_do_pack(packer, fcs);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_do_unpack(packer, pfc_opcode);

		amiq_eth_do_unpack(packer, pfc_class_enable_vector);

		amiq_eth_pfc_parameter parameter_item;
		for (unsigned int index = 0; index < pfc_parameter_size; index++) {
			amiq_eth_do_unpack(packer, parameter_item);
			pfc_parameter[index] = parameter_item;
		}

		amiq_eth_data pad_item;
		for (unsigned int index = 0; index < pad_size; index++) {
			amiq_eth_do_unpack(packer, pad_item);
			pad[index] = pad_item;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_PFC_PAUSE_CODE);

		return result;
	}
};

#endif
