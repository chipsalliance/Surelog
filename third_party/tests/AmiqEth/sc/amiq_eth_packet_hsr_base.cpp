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
 * NAME:        amiq_eth_packet_hsr_base.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the HSR Ethernet packet.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_HSR_BASE
//protection against multiple includes
#define __AMIQ_ETH_PACKET_HSR_BASE

using namespace std;

//Ethernet HSR packet
class amiq_eth_packet_hsr_base: public amiq_eth_packet_ether_type {

public:

	//Path
	amiq_eth_hsr_path path;

	//Size
	amiq_eth_hsr_size size;

	//Sequence
	amiq_eth_hsr_seq seq;

	//constructor
	amiq_eth_packet_hsr_base() {
		ether_type = SC_AMIQ_ETH_HSR;
	}

	//destructor
	virtual ~amiq_eth_packet_hsr_base() {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		amiq_eth_packet_ether_type::do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PATH: " << std::hex << path.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SIZE: " << std::hex << size.to_int() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SEQ: " << std::hex << seq.to_int();
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, path);

		amiq_eth_do_pack(packer, size);

		amiq_eth_do_pack(packer, seq);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_do_unpack(packer, path);

		amiq_eth_do_unpack(packer, size);

		amiq_eth_do_unpack(packer, seq);
	}
};

#endif
