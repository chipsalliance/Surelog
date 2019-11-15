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
 * NAME:        amiq_eth_packet_ether_type.cpp
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration of the basic Ethernet frame
 * 				in which Length/Type field is interpreted as Type.
 * 				The definition of this packet is described in IEEE 802.3-2012.
 * 				For more details see file docs/ieee_802.3-2012/802.3-2012_section1.pdf,
 * 				chapter 3. Media Access Control (MAC) frame and packet specifications
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_ETHER_TYPE
//protection against multiple includes
#define __AMIQ_ETH_PACKET_ETHER_TYPE

using namespace std;

//Basic class for declaring the Ethernet packets in which Length/Type field is interpreted as Type.
class amiq_eth_packet_ether_type: public amiq_eth_packet {

public:

	//Length/Type
	ethernet_legal_protocols ether_type;

	//constructor
	amiq_eth_packet_ether_type() {
		ether_type = (ethernet_legal_protocols) 0;
	}

	//destructor
	virtual ~amiq_eth_packet_ether_type() {

	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		amiq_eth_length_type int_ether_type = ether_type;
		out << "ETHER_TYPE: " << std::hex << int_ether_type.to_int();
	}

	//pack Ethernet type field
	//@param packer - the packer used by this function
	virtual void pack_ether_type(amiq_eth_packer& packer) const {
		amiq_eth_length_type int_ether_type = ether_type;
		amiq_eth_do_pack(packer, int_ether_type);
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet::do_pack(packer);
		pack_ether_type(packer);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet::do_unpack(packer);

		amiq_eth_length_type local_ether_type;
		amiq_eth_do_unpack(packer, local_ether_type);
		ether_type = (ethernet_legal_protocols) local_ether_type.to_int();
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet::do_pack_for_fcs(packer);
		pack_ether_type(packer);
	}

};

#endif
