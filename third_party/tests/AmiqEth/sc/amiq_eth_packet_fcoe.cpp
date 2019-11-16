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
 * NAME:        amiq_eth_packet_fcoe.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Fibre Channel over Ethernet (FCoE) packet.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_FCOE
//protection against multiple includes
#define __AMIQ_ETH_PACKET_FCOE

using namespace std;

//Ethernet Fibre Channel over Ethernet (FCoE) packet
class amiq_eth_packet_fcoe: public amiq_eth_packet_ether_type {

public:

	//version
	amiq_eth_fcoe_version version;

	//reserved bits
	amiq_eth_fcoe_reserved_size *fcoe_reserved_before_sof;

	//start of frame
	amiq_sof_legal sof;

	//frame
	amiq_eth_fcoe_frame_size fc_frame_size;
	amiq_eth_data *fc_frame;

	//end of frame
	amiq_eth_fcoe_eof eof;

	//reserved bits
	amiq_eth_fcoe_reserved_size *fcoe_reserved_after_eof;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	bool use_fcs;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_fcoe() {
		ether_type = SC_AMIQ_ETH_FCOE;
		fcoe_reserved_before_sof = new amiq_eth_fcoe_reserved_size[AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE];
		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE; index++) {
			fcoe_reserved_before_sof[index] = 0;
		}
		fcoe_reserved_after_eof = new amiq_eth_fcoe_reserved_size[AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE];
		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE; index++) {
			fcoe_reserved_after_eof[index] = 0;
		}
		use_fcs = 0;
		print_lists = false;
	}

	//destructor
	virtual ~amiq_eth_packet_fcoe() {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet_ether_type::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "VERSION: " << std::hex << version.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE; index++) {
				out << "RSVD_B_SOF [" << index << "]" << std::hex << fcoe_reserved_before_sof[index].to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "SOF: " << std::hex << sof << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FC FRAME Size: " << std::hex << fc_frame_size.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < fc_frame_size.to_uint(); index++) {
				out << "FC_FRAME [" << index << "]" << std::hex << fc_frame[index].to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "EOF: " << std::hex << eof << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE; index++) {
				out << "RSVD_A_EOF [" << index << "]" << std::hex << fcoe_reserved_after_eof[index].to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "FCS: " << std::hex << fcs.to_uint();
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, version);

		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE; index++) {
			amiq_eth_do_pack(packer, fcoe_reserved_before_sof[index]);
		}

		amiq_eth_fcoe_sof local_sof;
		local_sof = sof;
		amiq_eth_do_pack(packer, local_sof);

		amiq_eth_do_pack(packer, fc_frame_size);

		for (unsigned int index = 0; index < fc_frame_size.to_uint(); index++) {
			amiq_eth_do_pack(packer, fc_frame[index]);
		}

		amiq_eth_fcoe_eof local_eof;
		local_eof = eof;
		amiq_eth_do_pack(packer, local_eof);

		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE; index++) {
			amiq_eth_do_pack(packer, fcoe_reserved_after_eof[index]);
		}

		if (use_fcs) {
			amiq_eth_do_pack(packer, fcs);
		}
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_fcoe_reserved_size rsvd;

		amiq_eth_do_unpack(packer, version);

		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE; index++) {
			amiq_eth_do_unpack(packer, rsvd);
			fcoe_reserved_before_sof[index] = rsvd;
		}

		amiq_eth_fcoe_sof local_sof;
		amiq_eth_do_unpack(packer, local_sof);
		sof = amiq_sof_legal(local_sof.to_uint());

		amiq_eth_do_unpack(packer, fc_frame_size);

		amiq_eth_data fc_frame_item;
		fc_frame = new amiq_eth_data[fc_frame_size.to_uint()];
		for (unsigned int index = 0; index < fc_frame_size.to_uint(); index++) {
			amiq_eth_do_unpack(packer, fc_frame_item);
			fc_frame[index] = fc_frame_item;
		}

		amiq_eth_fcoe_eof local_eof;
		amiq_eth_do_unpack(packer, local_eof);
		eof = amiq_eof_legal(local_eof.to_uint());

		for (unsigned int index = 0; index < AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE; index++) {
			amiq_eth_do_unpack(packer, rsvd);
			fcoe_reserved_after_eof[index] = rsvd;
		}

		if (use_fcs) {
			amiq_eth_do_unpack(packer, fcs);
		}
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_FCOE_CODE);

		return result;
	}

};

#endif
