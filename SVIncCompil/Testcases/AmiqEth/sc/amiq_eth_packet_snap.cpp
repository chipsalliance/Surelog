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
 * NAME:        amiq_eth_packet_snap.cpp
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration SNAP (SubNetwork Access Protocol)
 * 				packet.
 * 				The implementation is based on IEEE 802-2001.
 * 				For more details see file docs/ieee_802-2001/802-2001.pdf,
 * 				chapter 10.3 Subnetwork Access Protocol
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_SNAP
//protection against multiple includes
#define __AMIQ_ETH_PACKET_SNAP

using namespace std;

//Ethernet SubNetwork Access Protocol (SNAP) packet
class amiq_eth_packet_snap: public amiq_eth_packet {

public:

	//Length
	amiq_eth_length_type length;

	//Destination Service Access Point
	amiq_eth_data dsap;

	//Source Service Access Point
	amiq_eth_data ssap;

	//Control
	amiq_eth_data ctl;

	//Protocol Identifier
	amiq_eth_snap_protocol_identifier protocol_identifier;

	//Protocol Data
	amiq_eth_data *protocol_data;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//constructor
	amiq_eth_packet_snap() {
		protocol_data = NULL;
	}

	//destructor
	virtual ~amiq_eth_packet_snap() {
		protocol_data = NULL;
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet::do_pack(packer);
		amiq_eth_do_pack(packer, length);
		amiq_eth_do_pack(packer, dsap);
		amiq_eth_do_pack(packer, ssap);
		amiq_eth_do_pack(packer, ctl);
		amiq_eth_do_pack(packer, protocol_identifier);

		for (unsigned int index = 0; index < length.to_uint() - 8; index++) {
			amiq_eth_do_pack(packer, protocol_data[index]);
		}

		amiq_eth_do_pack(packer, fcs);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet::do_unpack(packer);

		amiq_eth_do_unpack(packer, length);
		amiq_eth_do_unpack(packer, dsap);
		amiq_eth_do_unpack(packer, ssap);
		amiq_eth_do_unpack(packer, ctl);
		amiq_eth_do_unpack(packer, protocol_identifier);

		protocol_data = new amiq_eth_data[length.to_int() - 8];
		for (unsigned int index = 0; index < length.to_uint() - 8; index++) {
			amiq_eth_data temp_data;
			amiq_eth_do_unpack(packer, temp_data);
			protocol_data[index] = temp_data;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet::do_pack_for_fcs(packer);

		amiq_eth_do_pack(packer, length);
		amiq_eth_do_pack(packer, dsap);
		amiq_eth_do_pack(packer, ssap);
		amiq_eth_do_pack(packer, ctl);
		amiq_eth_do_pack(packer, protocol_identifier);

		for (int unsigned index = 0; index < length.to_uint() - 8; index++) {
			amiq_eth_do_pack(packer, protocol_data[index]);
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

		amiq_eth_packet::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Length: " << length << AMIQ_ETH_FIELD_SEPARATOR;
		out << "DSAP: " << dsap << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SSAP: " << ssap << AMIQ_ETH_FIELD_SEPARATOR;
		out << "CTL: " << ctl << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PROTOCOL IDENTIFIER: " << protocol_identifier << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * snap_result = (amiq_eth_packet::to_generic_payload());
		snap_result->set_address(AMIQ_ETH_PACKET_SNAP_CODE);

		return snap_result;
	}
};

#endif
