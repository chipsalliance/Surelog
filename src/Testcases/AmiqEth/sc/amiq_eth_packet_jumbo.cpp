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
 * NAME:        amiq_eth_packet_jumbo.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Jumbo Ethernet packet.
 * 				Implementation is done based on: http://en.wikipedia.org/wiki/Jumbo_frame
 * 				Jumbo packets are not supported by IEEE standards:
 * 				SOURCE: http://www.ethernetalliance.org/wp-content/uploads/2011/10/EA-Ethernet-Jumbo-Frames-v0-1.pdf
 * 				Furthermore, IEEE has determined they will not support or define Jumbo frames due to concerns around
 * 				vendor and equipment interoperability.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_JUMBO
//protection against multiple includes
#define __AMIQ_ETH_PACKET_JUMBO

using namespace std;

//Ethernet Jumbo packet
class amiq_eth_packet_jumbo: public amiq_eth_packet_ether_type {

public:

	//MAC Client Data Size
	amiq_eth_jumbo_client_data_size client_data_size;

	//MAC Client Data
	amiq_eth_data *client_data;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//constructor
	amiq_eth_packet_jumbo() {
		client_data = NULL;
	}

	//destructor
	virtual ~amiq_eth_packet_jumbo() {
		client_data = NULL;
	}

	//pack FCS field
	//@param packer - the packer used by this function
	virtual void pack_fcs(amiq_eth_packer& packer) const {
		amiq_eth_do_pack(packer, fcs);
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, client_data_size);

		for (int index = 0; index < client_data_size.to_int(); index++) {
			amiq_eth_do_pack(packer, client_data[index]);
		}

		pack_fcs(packer);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_do_unpack(packer, client_data_size);

		amiq_eth_data temp_data;
		client_data = new amiq_eth_data[client_data_size.to_uint()];

		for (unsigned int index = 0; index < client_data_size.to_uint(); index++) {
			amiq_eth_do_unpack(packer, temp_data);
			client_data[index] = temp_data;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack_for_fcs(packer);

		amiq_eth_data temp_data;
		for (int unsigned index = 0; index < client_data_size.to_uint(); index++) {
			temp_data = client_data[index];
			amiq_eth_do_pack(packer, temp_data);
		}
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		string fcs_info;
		amiq_eth_fcs correct_fcs = get_correct_fcs();

		if (correct_fcs == fcs) {
			fcs_info = "FCS is correct";
		} else {
			stringstream ss;
			ss << "FCS is wrong - expecting " << std::hex << correct_fcs << endl;
			fcs_info = ss.str();
		};

		amiq_eth_packet_ether_type::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Client Data Size: " << std::dec << client_data_size.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_JUMBO_CODE);

		return result;
	}
};

#endif
