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
 * NAME:        amiq_eth_packet_magic.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Magic Ethernet packet.
 * 				The definition of this packet is described in IEEE 802.1X-2010.
 * 				For more details see file docs/ieee_802.1X-2010/802.1X-2010.pdf,
 * 				Annex F - Support for ‘Wake-on-LAN’ protocols.
 * 				A more detail description of the magic packet was found on
 * 				Wiki: http://en.wikipedia.org/wiki/Wake-on-LAN#Magic_packet
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_MAGIC
//protection against multiple includes
#define __AMIQ_ETH_PACKET_MAGIC

using namespace std;

//Ethernet Magic packet
class amiq_eth_packet_magic: public amiq_eth_packet_ether_type {

public:

	//the address of the target device
	amiq_eth_address target_mac;

	//password size
	unsigned int password_size;

	//password
	amiq_eth_data *password;

	//MAC Client Data Size
	amiq_eth_jumbo_client_data_size client_data_size;

	//MAC Client Data
	amiq_eth_data *client_data;

	//fcs
	amiq_eth_fcs fcs;

	//starting index of the magic packet synchronization stream
	int synch_stream_starting_index;

	//constructor
	amiq_eth_packet_magic() {
		client_data = NULL;
		password = NULL;
		synch_stream_starting_index = -1;
	}

	//destructor
	virtual ~amiq_eth_packet_magic() {
		client_data = NULL;
		password = NULL;
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

		amiq_eth_data temp_data;
		for (int unsigned index = 0; index < client_data_size.to_uint(); index++) {
			temp_data = client_data[index];
			amiq_eth_do_pack(packer, temp_data);
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

		get_useful_info_from_client_data();
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
		out << "Starting Index: " << std::dec << synch_stream_starting_index << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Target MAC: " << std::hex << target_mac;
		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//set the information such as magic packet synchronization stream and target address in the client data
	virtual void set_useful_info_in_client_data() {

		std::vector<char> * local_synch_stream = new vector<char>();

		amiq_eth_magic_synch_stream bv_synch_stream = AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM;
		amiq_eth_packer * local_packer = new amiq_eth_packer();
		local_packer->reset();

		amiq_eth_do_pack(*local_packer, bv_synch_stream);

		local_packer->get_bytes(*local_synch_stream);
		local_synch_stream->reserve(local_synch_stream->size());

		for (int unsigned i = 0; i < local_synch_stream->size(); i++) {
			int unsigned client_data_index = i + synch_stream_starting_index;
			client_data[client_data_index] = (*local_synch_stream)[i];
		}

		int target_address_starting_index = synch_stream_starting_index + (AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8);
		int target_address_width_in_bytes = AMIQ_ETH_ADDRESS_WIDTH / 8;

		vector<amiq_eth_data> * target_mac_array = new vector<amiq_eth_data>();
		amiq_eth_address target_mac_copy = target_mac.to_int64();

		for (int i = 0; i < target_address_width_in_bytes; i++) {
			target_mac_copy = target_mac_copy.to_int64() >> (8 * i);
			char data = target_mac_copy.to_int();
			target_mac_array->push_back(data);
		}

		for (int target_mac_index = 0; target_mac_index < AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS; target_mac_index++) {
			for (int byte_index = 0; byte_index < target_address_width_in_bytes; byte_index++) {
				int unsigned client_data_index = target_address_starting_index + (target_mac_index * target_address_width_in_bytes) + byte_index;
				client_data[client_data_index] = (*target_mac_array)[byte_index];
			}
		}
	}

	//extract the information such as magic packet synchronization stream and target address in the client data
	virtual void get_useful_info_from_client_data() {
		int unsigned local_synch_stream_starting_index;

		std::vector<char> * local_synch_stream = new vector<char>();

		amiq_eth_address local_target_mac;

		bool success = false;

		amiq_eth_magic_synch_stream bv_synch_stream = AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM;
		amiq_eth_packer * local_packer = new amiq_eth_packer();
		local_packer->reset();

		amiq_eth_do_pack(*local_packer, bv_synch_stream);

		local_packer->get_bytes(*local_synch_stream);
		local_synch_stream->reserve(local_synch_stream->size());

		unsigned int client_data_index = 0;
		unsigned int synch_stream_index = 0;

		while (client_data_index < client_data_size.to_uint()) {
			if (synch_stream_index < (AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8)) {
				//synchronization stream was not found

				//cout << "Trying to find the synchronization stream at index: " << client_data_index << endl;

				int starting_index = client_data_index;

				for (synch_stream_index = 0; synch_stream_index < (AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8); synch_stream_index++) {
					if (client_data[client_data_index] != (*local_synch_stream)[synch_stream_index]) {
						synch_stream_index = 0;
						client_data_index = starting_index + 1;
						break;
					} else {
						if (synch_stream_index == 0) {
							local_synch_stream_starting_index = client_data_index;
						}

						client_data_index++;
					}
				}

				if (synch_stream_index >= (AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8)) {
					//cout << "Found synchronization stream at index: " << synch_stream_index << endl;
					vector<amiq_eth_data> * target_mac_array = new vector<amiq_eth_data>();
					bool target_mac_byte_mismatch_detected = false;
					unsigned int target_mac_bytes_number = AMIQ_ETH_ADDRESS_WIDTH / 8;

					for (int unsigned target_mac_index = 0; target_mac_index < target_mac_bytes_number; target_mac_index++) {
						//cout << "Searching for target mac address index " << target_mac_index << "..." << endl;
						target_mac_array->push_back(client_data[client_data_index]);

						for (int target_mac_repetition_index = 0; target_mac_repetition_index < AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS; target_mac_repetition_index++) {
							int current_index = client_data_index + ((target_mac_repetition_index * target_mac_bytes_number));

							if ((*target_mac_array)[target_mac_array->size() - 1] != client_data[current_index]) {
								synch_stream_index = 0;
								target_mac_byte_mismatch_detected = 1;
								target_mac_array = new vector<amiq_eth_data>();
								client_data_index = starting_index + 1;
								break;
							}
						}

						if (target_mac_byte_mismatch_detected == 1) {
							break;
						} else {
							client_data_index++;
						}
					}

					if (target_mac_byte_mismatch_detected == 1) {
						continue;
					} else {
						client_data_index = client_data_index + (target_mac_bytes_number * (AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS - 1));

						for (unsigned int i = 0; i < target_mac_array->size(); i++) {
							char data = (*target_mac_array)[i].to_int();
							local_target_mac = (local_target_mac << 8) | (data & 0xFF);
						}

						synch_stream_starting_index = local_synch_stream_starting_index;
						target_mac = local_target_mac;

						success = true;

						password_size = 0;
						if (client_data_index < client_data_size.to_uint() - 6) {
							password_size = 6;
						} else if (client_data_index < client_data_size.to_uint() - 4) {
							password_size = 4;
						} else {
							break;
						}

						password = new amiq_eth_data[password_size];

						for (unsigned int password_index = 0; password_index < password_size; password_index++) {
							password[password_index] = client_data[client_data_index + password_index];
						}

						break;
					}
				}
			}
		}

		if (success != true) {
			stringstream ss;
			ss << "Could not find Magic pattern and Target MAC in the payload of packet: ";
			do_print(ss);
			string str = ss.str();
			SC_REPORT_FATAL("AMIQ_ETH", str.c_str());
		}
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_MAGIC_CODE);

		return result;
	}
};


#endif
