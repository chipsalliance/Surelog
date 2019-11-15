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
 * NAME:        amiq_eth_packet_ipv4.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the IPV4 Ethernet packet.
 * 				Implementation is done based on: http://en.wikipedia.org/wiki/Internet_Protocol_version_4
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_IPV4
//protection against multiple includes
#define __AMIQ_ETH_PACKET_IPV4

using namespace std;

//Ethernet IPV4 packet header
class amiq_eth_packet_ipv4_header {
public:

	//Version
	amiq_eth_ipv4_header_version version;

	//Internet Header Length (IHL)
	amiq_eth_ipv4_header_ihl ihl;

	//Differentiated Services Code Point (DSCP)
	amiq_eth_ipv4_header_dscp dscp;

	//Explicit Congestion Notification (ECN)
	amiq_eth_ipv4_header_ecn ecn;

	//Total Length
	amiq_eth_ipv4_header_total_length total_length;

	//Identification
	amiq_eth_ipv4_header_identification identification;

	//Flags
	amiq_eth_ipv4_header_flags flags;

	//Fragment Offset
	amiq_eth_ipv4_header_fragment_offset fragment_offset;

	//Time To Live (TTL)
	amiq_eth_ipv4_header_ttl ttl;

	//Protocol
	amiq_eth_ipv4_header_protocol protocol;

	//Header Checksum
	amiq_eth_ipv4_header_checksum checksum;

	//Source address
	amiq_eth_ipv4_header_source_ip_address source_ip_address;

	//Destination address
	amiq_eth_ipv4_header_destination_ip_address destination_ip_address;

	//Options
	amiq_eth_ipv4_header_option *options;

	//constructor
	amiq_eth_packet_ipv4_header() {
		options = NULL;
	}

	//destructor
	~amiq_eth_packet_ipv4_header() {
		options = NULL;
	}

	//get the minimum length of the header, in bits
	//@return the minimum length of the header, in bits
	virtual unsigned int get_minimum_header_length_in_bits() const {
		return (AMIQ_ETH_IPV4_HEADER_VERSION_WIDTH + AMIQ_ETH_IPV4_HEADER_IHL_WIDTH + AMIQ_ETH_IPV4_HEADER_DSCP_WIDTH + AMIQ_ETH_IPV4_HEADER_ECN_WIDTH + AMIQ_ETH_IPV4_HEADER_TOTAL_LENGTH_WIDTH
				+ AMIQ_ETH_IPV4_HEADER_IDENTIFICATION_WIDTH + AMIQ_ETH_IPV4_HEADER_FLAGS_WIDTH + AMIQ_ETH_IPV4_HEADER_FRAGMENT_OFFSET_WIDTH + AMIQ_ETH_IPV4_HEADER_TTL_WIDTH
				+ AMIQ_ETH_IPV4_HEADER_PROTOCOL_WIDTH + AMIQ_ETH_IPV4_HEADER_CHECKSUM_WIDTH + AMIQ_ETH_IPV4_HEADER_SOURCE_IP_ADDRESS_WIDTH + AMIQ_ETH_IPV4_HEADER_DESTINATION_IP_ADDRESS_WIDTH);
	}

	//get the minimum length of the header, in bytes
	//@return the minimum length of the header, in bytes
	virtual unsigned int get_minimum_header_length_in_bytes() {
		return (get_minimum_header_length_in_bits() / 8);
	}

	//get the minimum length of the header, in words
	//@return the minimum length of the header, in words
	virtual unsigned int get_minimum_header_length_in_words() const {
		return (get_minimum_header_length_in_bits() / 32);
	}

	//get the options size in words
	//@param local_ihl - Internet Header Length (IHL)
	//@return the options size in words
	virtual unsigned int get_options_size_in_words() const {
		if (ihl.to_uint() < get_minimum_header_length_in_words()) {
			stringstream ss;
			ss << "Internet Header Length (" << std::dec << ihl << ") should be bigger or equal then Minimum Header Length in words (" << std::dec << get_minimum_header_length_in_words() << ")";
			string str = ss.str();
			SC_REPORT_FATAL("AMIQ_ETH", str.c_str());
		};

		return (ihl.to_uint() - get_minimum_header_length_in_words());
	}

	//get the header length in bytes
	//@return the header length in bytes
	virtual unsigned int get_header_length_in_bytes() const {
		return (ihl.to_uint() * 4);
	}

	//get the data length in bytes
	//@return the data length in bytes
	virtual unsigned int get_data_length_in_bytes() const {
		if (total_length.to_uint() < get_header_length_in_bytes()) {
			stringstream ss;
			ss << "Total Length (" << std::dec << total_length.to_uint() << ") should be bigger or equal to IHL in bytes (" << std::dec << get_header_length_in_bytes() << ")";
			string str = ss.str();
			SC_REPORT_FATAL("AMIQ_ETH", str.c_str());
		};

		return (total_length.to_uint() - get_header_length_in_bytes());
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_do_pack(packer, version);
		amiq_eth_do_pack(packer, ihl);
		amiq_eth_do_pack(packer, dscp);
		amiq_eth_do_pack(packer, ecn);
		amiq_eth_do_pack(packer, total_length);
		amiq_eth_do_pack(packer, identification);
		amiq_eth_do_pack(packer, flags);
		amiq_eth_do_pack(packer, fragment_offset);
		amiq_eth_do_pack(packer, ttl);
		amiq_eth_do_pack(packer, protocol);
		amiq_eth_do_pack(packer, checksum);
		amiq_eth_do_pack(packer, source_ip_address);
		amiq_eth_do_pack(packer, destination_ip_address);

		unsigned int options_size_in_words = get_options_size_in_words();
		for (unsigned int index = 0; index < options_size_in_words; index++) {
			amiq_eth_do_pack(packer, options[index]);
		}
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_do_unpack(packer, version);
		amiq_eth_do_unpack(packer, ihl);
		amiq_eth_do_unpack(packer, dscp);
		amiq_eth_do_unpack(packer, ecn);
		amiq_eth_do_unpack(packer, total_length);
		amiq_eth_do_unpack(packer, identification);
		amiq_eth_do_unpack(packer, flags);
		amiq_eth_do_unpack(packer, fragment_offset);
		amiq_eth_do_unpack(packer, ttl);
		amiq_eth_do_unpack(packer, protocol);
		amiq_eth_do_unpack(packer, checksum);
		amiq_eth_do_unpack(packer, source_ip_address);
		amiq_eth_do_unpack(packer, destination_ip_address);

		unsigned int options_size_in_words = get_options_size_in_words();
		options = new amiq_eth_ipv4_header_option[options_size_in_words];

		for (int unsigned i = 0; i < options_size_in_words; i++) {
			amiq_eth_ipv4_header_option option;
			amiq_eth_do_unpack(packer, option);
			options[i] = option;
		}
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		out << "Version: " << std::hex << version.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "IHL: " << std::dec << ihl.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "DSCP: " << std::hex << dscp.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "ECN: " << std::hex << ecn.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Total Length: " << std::dec << total_length.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Identification: " << std::hex << identification.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Flags: " << std::hex << flags.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Fragment Offset: " << std::hex << fragment_offset.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "TTL: " << std::dec << ttl.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Protocol: " << std::hex << protocol.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Checksum: " << std::hex << checksum.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Source IP: " << std::hex << source_ip_address.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Destination IP: " << std::hex << destination_ip_address.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "Options size: " << std::dec << get_options_size_in_words();
	}

};


//Ethernet IPV4 packet
class amiq_eth_packet_ipv4: public amiq_eth_packet_ether_type {

public:

	//header
	amiq_eth_packet_ipv4_header header;

	//data
	amiq_eth_data *data;

	//pad
	amiq_eth_data *pad;

	//fcs
	amiq_eth_fcs fcs;

	//constructor
	amiq_eth_packet_ipv4() {
		data = NULL;
		pad = NULL;
		header = *(new amiq_eth_packet_ipv4_header());
	}

	//destrucor
	virtual ~amiq_eth_packet_ipv4() {
		data = NULL;
		pad = NULL;
		delete &header;
	}

	//get the pad size based on the value of the input parameters
	//@param min_frame_size - minimum frame size
	//@param - header - Ethernet IPV4 packet header
	//@return the pad size
	virtual unsigned int get_pad_size_by_fields(int unsigned min_frame_size, amiq_eth_packet_ipv4_header header) const {
		unsigned int value = ((header.total_length.to_uint64() + (2 * (AMIQ_ETH_ADDRESS_WIDTH / 8)) + 6));

		if (min_frame_size >= value) {
			return (min_frame_size - value);
		} else {
			return 0;
		}
	}

	//get the pad size
	//@return the pad size
	virtual unsigned int get_pad_size() const {
		return get_pad_size_by_fields(min_frame_size, header);
	}

	//pack data field
	//@param packer - the packer used by this function
	virtual void pack_data(amiq_eth_packer& packer) const {
		for (unsigned int index = 0; index < header.get_data_length_in_bytes(); index++) {
			amiq_eth_do_pack(packer, data[index]);
		}
	}

	//pack pad field
	//@param packer - the packer used by this function
	virtual void pack_pad(amiq_eth_packer& packer) const {
		unsigned int pad_size = get_pad_size();
		for (unsigned int index = 0; index < pad_size; index++) {
			amiq_eth_do_pack(packer, pad[index]);
		}
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
		header.do_pack(packer);
		pack_data(packer);
		pack_pad(packer);
		pack_fcs(packer);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);
		header.do_unpack(packer);

		int unsigned data_length = header.get_data_length_in_bytes();
		data = new amiq_eth_data[data_length];
		for (unsigned int index = 0; index < data_length; index++) {
			amiq_eth_data local_data;
			amiq_eth_do_unpack(packer, local_data);
			data[index] = local_data;
		}

		unsigned int pad_size = get_pad_size();
		pad = new amiq_eth_data[pad_size];
		for (unsigned int index = 0; index < pad_size; index++) {
			amiq_eth_data local_pad;
			amiq_eth_do_unpack(packer, local_pad);
			pad[index] = local_pad;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack_for_fcs(packer);
		header.do_pack(packer);
		pack_data(packer);
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
		header.do_print(out);
		out << AMIQ_ETH_FIELD_SEPARATOR;
		out << "data size: " << std::dec << header.get_data_length_in_bytes() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "pad size: " << std::dec << get_pad_size() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_IPV4_CODE);

		return result;
	}
};


#endif
