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
 * NAME:        amiq_eth_packet_arp.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Address Resolution Protocol packet.
 * 				Implementation is done based on: http://en.wikipedia.org/wiki/Address_Resolution_Protocol
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_ARP
//protection against multiple includes
#define __AMIQ_ETH_PACKET_ARP

using namespace std;

//Ethernet Address Resolution Protocol packet
class amiq_eth_packet_arp: public amiq_eth_packet_ether_type {

public:

	//Hardware type (HTYPE) - This field specifies the network protocol type.
	amiq_eth_arp_htype htype;

	//Protocol type (PTYPE) - This field specifies the internetwork protocol for which the ARP request is intended.
	amiq_eth_arp_ptype ptype;

	//Hardware length (HLEN) - Length (in octets) of a hardware address.
	amiq_eth_arp_hlen hlen;

	//Protocol length (PLEN) - Length (in octets) of addresses used in the upper layer protocol. (The upper layer protocol specified in PTYPE.)
	amiq_eth_arp_plen plen;

	//Operation - Specifies the operation that the sender is performing: 1 for request, 2 for reply.
	amiq_eth_arp_oper oper;

	//Sender hardware address (SHA) - Media address of the sender.
	//In an ARP request this field is used to indicate the address of the host sending the request.
	//In an ARP reply this field is used to indicate the address of the host that the request was looking for. (Not necessarily address of the host replying as in the case of virtual media.)
	//Note that switches do not pay attention to this field, particularly in learning MAC addresses.
	amiq_eth_arp_sha sha;

	//Sender protocol address (SPA) - internetwork address of the sender.
	amiq_eth_arp_spa spa;

	//Target hardware address (THA) - Media address of the intended receiver.
	//In an ARP request this field is ignored.
	//In an ARP reply this field is used to indicate the address of the host that originated the ARP request.
	amiq_eth_arp_tha tha;

	//Target protocol address (TPA) - internetwork address of the intended receiver.
	amiq_eth_arp_tpa tpa;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//pack FCS field
	//@param packer - the packer used by this function
	virtual void pack_fcs(amiq_eth_packer& packer) const {
		amiq_eth_do_pack(packer, fcs);
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);

		amiq_eth_do_pack(packer, htype);
		amiq_eth_do_pack(packer, ptype);
		amiq_eth_do_pack(packer, hlen);
		amiq_eth_do_pack(packer, plen);
		amiq_eth_do_pack(packer, oper);
		amiq_eth_do_pack(packer, sha);
		amiq_eth_do_pack(packer, spa);
		amiq_eth_do_pack(packer, tha);
		amiq_eth_do_pack(packer, tpa);

		pack_fcs(packer);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);

		amiq_eth_do_unpack(packer, htype);
		amiq_eth_do_unpack(packer, ptype);
		amiq_eth_do_unpack(packer, hlen);
		amiq_eth_do_unpack(packer, plen);
		amiq_eth_do_unpack(packer, oper);
		amiq_eth_do_unpack(packer, sha);
		amiq_eth_do_unpack(packer, spa);
		amiq_eth_do_unpack(packer, tha);
		amiq_eth_do_unpack(packer, tpa);

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack_for_fcs(packer);
		amiq_eth_do_pack(packer, htype);
		amiq_eth_do_pack(packer, ptype);
		amiq_eth_do_pack(packer, hlen);
		amiq_eth_do_pack(packer, plen);
		amiq_eth_do_pack(packer, oper);
		amiq_eth_do_pack(packer, sha);
		amiq_eth_do_pack(packer, spa);
		amiq_eth_do_pack(packer, tha);
		amiq_eth_do_pack(packer, tpa);
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

		out << "HTYPE: " << std::hex << htype << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PTYPE: " << std::hex << ptype << AMIQ_ETH_FIELD_SEPARATOR;
		out << "HLEN: " << std::hex << hlen << AMIQ_ETH_FIELD_SEPARATOR;
		out << "PLEN: " << std::hex << plen << AMIQ_ETH_FIELD_SEPARATOR;
		out << "OPER: " << std::hex << oper << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SHA: " << std::hex << sha << AMIQ_ETH_FIELD_SEPARATOR;
		out << "SPA: " << std::hex << spa << AMIQ_ETH_FIELD_SEPARATOR;
		out << "THA: " << std::hex << tha << AMIQ_ETH_FIELD_SEPARATOR;
		out << "TPA: " << std::hex << tpa << AMIQ_ETH_FIELD_SEPARATOR;

		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_ARP_CODE);

		return result;
	}
};

#endif
