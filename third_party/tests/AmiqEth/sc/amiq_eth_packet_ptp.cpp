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
 * NAME:        amiq_eth_packet_ptp.cpp
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Precision Time Protocol packet.
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_PTP
//protection against multiple includes
#define __AMIQ_ETH_PACKET_PTP

using namespace std;

//Ethernet Precision Time Protocol packet header
class amiq_eth_packet_ptp_header: public amiq_eth_object {
public:

	amiq_eth_ptp_transport_specific transport_specific;

	amiq_eth_ptp_message_type message_type;

	amiq_eth_ptp_reserved *ptp_reserved_1;

	amiq_eth_ptp_version version;

	amiq_eth_ptp_message_length message_length;

	amiq_eth_ptp_domain_number domain_number;

	amiq_eth_ptp_reserved *ptp_reserved_2;

	amiq_eth_ptp_flags flags;

	amiq_eth_ptp_correction_field correction_field;

	amiq_eth_ptp_reserved *ptp_reserved_3;

	amiq_eth_ptp_source_port_identity *source_port_identity;

	amiq_eth_ptp_sequence_id sequence_id;

	amiq_eth_ptp_control_field control_field;

	amiq_eth_ptp_log_message log_message;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_ptp_header() {
		source_port_identity = new amiq_eth_ptp_source_port_identity[AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_SIZE];
		ptp_reserved_1 = new amiq_eth_ptp_reserved[AMIQ_ETH_PTP_RESERVED_1_WIDTH];
		for (int unsigned i = 0; i < AMIQ_ETH_PTP_RESERVED_1_WIDTH; i++) {
			ptp_reserved_1[i] = 0;
		}
		ptp_reserved_2 = new amiq_eth_ptp_reserved[AMIQ_ETH_PTP_RESERVED_2_WIDTH];
		for (int unsigned i = 0; i < AMIQ_ETH_PTP_RESERVED_2_WIDTH; i++) {
			ptp_reserved_2[i] = 0;
		}
		ptp_reserved_3 = new amiq_eth_ptp_reserved[AMIQ_ETH_PTP_RESERVED_3_WIDTH];
		for (int unsigned i = 0; i < AMIQ_ETH_PTP_RESERVED_3_WIDTH; i++) {
			ptp_reserved_3[i] = 0;
		}
		print_lists = false;
	}

	//destructor
	~amiq_eth_packet_ptp_header() {
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_ptp_transport_specific_w local_transport_specific;
		local_transport_specific = transport_specific;
		amiq_eth_do_pack(packer, local_transport_specific);

		amiq_eth_ptp_message_type_w local_message_type;
		local_message_type = message_type;
		amiq_eth_do_pack(packer, local_message_type);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_1_WIDTH; index++) {
			amiq_eth_do_pack(packer, ptp_reserved_1[index]);
		}

		amiq_eth_do_pack(packer, version);
		amiq_eth_do_pack(packer, message_length);
		amiq_eth_do_pack(packer, domain_number);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_2_WIDTH; index++) {
			amiq_eth_do_pack(packer, ptp_reserved_2[index]);
		}

		amiq_eth_do_pack(packer, flags);
		amiq_eth_do_pack(packer, correction_field);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_3_WIDTH; index++) {
			amiq_eth_do_pack(packer, ptp_reserved_3[index]);
		}

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_SIZE; index++) {
			amiq_eth_do_pack(packer, source_port_identity[index]);
		}

		amiq_eth_do_pack(packer, sequence_id);

		amiq_eth_ptp_control_field_w local_control_field;
		local_control_field = control_field;
		amiq_eth_do_pack(packer, local_control_field);

		amiq_eth_do_pack(packer, log_message);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_ptp_transport_specific_w local_transport_specific;
		amiq_eth_do_unpack(packer, local_transport_specific);
		transport_specific = (amiq_eth_ptp_transport_specific) local_transport_specific.to_int();

		amiq_eth_ptp_message_type_w local_message_type;
		amiq_eth_do_unpack(packer, local_message_type);
		message_type = (amiq_eth_ptp_message_type) local_message_type.to_uint();

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_1_WIDTH; index++) {
			amiq_eth_ptp_reserved rsvd;
			amiq_eth_do_unpack(packer, rsvd);
			ptp_reserved_1[index] = rsvd;
		}

		amiq_eth_do_unpack(packer, version);
		amiq_eth_do_unpack(packer, message_length);
		amiq_eth_do_unpack(packer, domain_number);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_2_WIDTH; index++) {
			amiq_eth_ptp_reserved rsvd;
			amiq_eth_do_unpack(packer, rsvd);
			ptp_reserved_2[index] = rsvd;
		}

		amiq_eth_do_unpack(packer, flags);
		amiq_eth_do_unpack(packer, correction_field);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_3_WIDTH; index++) {
			amiq_eth_ptp_reserved rsvd;
			amiq_eth_do_unpack(packer, rsvd);
			ptp_reserved_3[index] = rsvd;
		}

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_SIZE; index++) {
			amiq_eth_ptp_source_port_identity temp;
			amiq_eth_do_unpack(packer, temp);
			source_port_identity[index] = temp;
		}

		amiq_eth_do_unpack(packer, sequence_id);

		amiq_eth_ptp_control_field_w local_control_field;
		amiq_eth_do_unpack(packer, local_control_field);
		control_field = (amiq_eth_ptp_control_field) local_control_field.to_uint();

		amiq_eth_do_unpack(packer, log_message);
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		out << "TRANSPORT SPECIFIC: " << std::hex << transport_specific << AMIQ_ETH_FIELD_SEPARATOR;
		out << "MESSAGE_TYPE: " << std::dec << message_type << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_1_WIDTH; index++) {
				out << "RSVD_1 [" << index << "]" << std::hex << ptp_reserved_1[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "VERSION: " << std::hex << version.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "MESSAGE LENGTH: " << std::dec << message_length.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "DOMAIN NUMBER: " << std::hex << domain_number.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_2_WIDTH; index++) {
				out << "RSVD_2 [" << index << "]" << std::hex << ptp_reserved_2[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "FLAGS: " << std::hex << flags.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "CORRECTION FIELD: " << std::dec << correction_field.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_RESERVED_3_WIDTH; index++) {
				out << "RSVD_3 [" << index << "]" << std::hex << ptp_reserved_3[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		if (print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_SIZE; index++) {
				out << "SOURCE PORT IDENTITY [" << index << "]" << std::hex << source_port_identity[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "SEQUENCE ID: " << std::hex << sequence_id.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "CONTROL FIELD: " << std::hex << control_field << AMIQ_ETH_FIELD_SEPARATOR;
		out << "LOG MESSAGE: " << std::dec << log_message.to_uint();
	}

};


//Ethernet Precision Time Protocol packet
class amiq_eth_packet_ptp_body: public amiq_eth_object {
public:

	//constructor
	amiq_eth_packet_ptp_body() {
	}

	//destructor
	~amiq_eth_packet_ptp_body() {
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
	}

};


//PTP announce message class
class amiq_eth_packet_ptp_announce_message: public amiq_eth_packet_ptp_body {
public:

	amiq_eth_ptp_origin_timestamp *origin_timestamp;

	amiq_eth_ptp_announce_message_current_utc_offset current_utc_offset;

	amiq_eth_ptp_reserved *ptp_announce_message_reserved;

	amiq_eth_ptp_announce_message_grandmaster_priority_1 grandmaster_priority_1;

	amiq_eth_ptp_announce_message_grandmaster_clock_quality grandmaster_clock_quality;

	amiq_eth_ptp_announce_message_grandmaster_priority_2 grandmaster_priority_2;

	amiq_eth_ptp_announce_message_grandmaster_identity grandmaster_identity;

	amiq_eth_ptp_announce_message_steps_removed steps_removed;

	amiq_eth_ptp_announce_message_time_source time_source;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_ptp_announce_message() {
		origin_timestamp = new amiq_eth_ptp_origin_timestamp[AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
		ptp_announce_message_reserved = new amiq_eth_ptp_reserved[AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH];
		for (int unsigned i = 0; i < AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH; i++) {
			ptp_announce_message_reserved[i] = 0;
		}
		print_lists = false;
	}

	//destrucor
	~amiq_eth_packet_ptp_announce_message() {
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ptp_body::do_pack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_do_pack(packer, origin_timestamp[index]);
		}

		amiq_eth_do_pack(packer, current_utc_offset);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH; index++) {
			amiq_eth_do_pack(packer, ptp_announce_message_reserved[index]);
		}

		amiq_eth_do_pack(packer, grandmaster_priority_1);
		amiq_eth_do_pack(packer, grandmaster_clock_quality);
		amiq_eth_do_pack(packer, grandmaster_priority_2);
		amiq_eth_do_pack(packer, grandmaster_identity);
		amiq_eth_do_pack(packer, steps_removed);
		amiq_eth_do_pack(packer, time_source);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ptp_body::do_unpack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_ptp_origin_timestamp t;
			amiq_eth_do_unpack(packer, t);
			origin_timestamp[index] = t;
		}

		amiq_eth_do_unpack(packer, current_utc_offset);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH; index++) {
			amiq_eth_ptp_reserved rsvd;
			amiq_eth_do_unpack(packer, rsvd);
			ptp_announce_message_reserved[index] = rsvd;
		}

		amiq_eth_do_unpack(packer, grandmaster_priority_1);
		amiq_eth_do_unpack(packer, grandmaster_clock_quality);
		amiq_eth_do_unpack(packer, grandmaster_priority_2);
		amiq_eth_do_unpack(packer, grandmaster_identity);
		amiq_eth_do_unpack(packer, steps_removed);
		amiq_eth_do_unpack(packer, time_source);
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		if(print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
				out << "ORIGIN TIMESTAMP [" << index << "]" << std::hex << origin_timestamp[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "CURRENT UTC OFFSET: " << std::dec << current_utc_offset.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		if(print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH; index++) {
				out << "RSVD_ANNOUNCE_MESSAGE [" << index << "]" << std::hex << ptp_announce_message_reserved[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
		out << "GRANDMASTER PRIORITY 1: " << std::hex << grandmaster_priority_1.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "GRANDMASTER CLOCK QUALITY: " << std::dec << grandmaster_clock_quality.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "GRANDMASTER PRIORITY 2: " << std::hex << grandmaster_priority_2.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "GRANDMASTER ITENTITY: " << std::hex << grandmaster_identity.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "STEPS REMOVED: " << std::hex << steps_removed.to_uint() << AMIQ_ETH_FIELD_SEPARATOR;
		out << "TIME SOURCE: " << std::dec << time_source.to_uint();
	}

};


//PTP announce message class
class amiq_eth_packet_ptp_sync_message: public amiq_eth_packet_ptp_body {
public:

	amiq_eth_ptp_origin_timestamp *origin_timestamp;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_ptp_sync_message() {
		origin_timestamp = new amiq_eth_ptp_origin_timestamp[AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
		print_lists = false;
	}

	//destructor
	~amiq_eth_packet_ptp_sync_message() {
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ptp_body::do_pack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_do_pack(packer, origin_timestamp[index]);
		}
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ptp_body::do_unpack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_ptp_origin_timestamp t;
			amiq_eth_do_unpack(packer, t);
			origin_timestamp[index] = t;
		}
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		if(print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
				out << "ORIGIN TIMESTAMP [" << index << "]" << std::hex << origin_timestamp[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
	}

};


//PTP delay request message
class amiq_eth_packet_ptp_delay_req_message: public amiq_eth_packet_ptp_body {
public:

	amiq_eth_ptp_origin_timestamp *origin_timestamp;

	//switch to print lists
	bool print_lists;

	//constructor
	amiq_eth_packet_ptp_delay_req_message() {
		origin_timestamp = new amiq_eth_ptp_origin_timestamp[AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
		print_lists = false;
	}

	//destructor
	~amiq_eth_packet_ptp_delay_req_message() {
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ptp_body::do_pack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_do_pack(packer, origin_timestamp[index]);
		}
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ptp_body::do_unpack(packer);

		for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
			amiq_eth_ptp_origin_timestamp t;
			amiq_eth_do_unpack(packer, t);
			origin_timestamp[index] = t;
		}
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {
		if(print_lists) {
			for (unsigned int index = 0; index < AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE; index++) {
				out << "ORIGIN TIMESTAMP [" << index << "]" << std::hex << origin_timestamp[index].to_int() << AMIQ_ETH_FIELD_SEPARATOR;
			}
		}
	}

};


//PTP packet
class amiq_eth_packet_ptp: public amiq_eth_packet_ether_type {

public:

	//header
	amiq_eth_packet_ptp_header header;

	//body
	amiq_eth_packet_ptp_announce_message announce_message_body;
	amiq_eth_packet_ptp_sync_message sync_message_body;
	amiq_eth_packet_ptp_delay_req_message delay_req_message_body;

	//fcs
	amiq_eth_fcs fcs;

	//constructor
	amiq_eth_packet_ptp() {
		ether_type = SC_AMIQ_ETH_PTP;
		header = *(new amiq_eth_packet_ptp_header());
		sync_message_body = *(new amiq_eth_packet_ptp_sync_message());
		delay_req_message_body = *(new amiq_eth_packet_ptp_delay_req_message());
	}

	//destructor
	virtual ~amiq_eth_packet_ptp() {
		delete &header;
		delete &sync_message_body;
		delete &delay_req_message_body;
	}

	//pack FCS field
	//@param packer - the packer used by this function
	virtual void pack_fcs(amiq_eth_packer& packer) const {
		amiq_eth_do_pack(packer, fcs);
	}

	//pack body field
	//@param packer - the packer used by this function
	virtual void pack_body(amiq_eth_packer& packer) const {
		switch (header.message_type) {
		case PTP_AnnounceMessage:
			announce_message_body.do_pack(packer);
			break;
		case PTP_SyncMessage:
			sync_message_body.do_pack(packer);
			break;
		case PTP_Delay_ReqMessage:
			delay_req_message_body.do_pack(packer);
			break;
		default:
			stringstream ss;
			ss << "Could not determine message type: " << std::hex << header.message_type;
			string str = ss.str();
			SC_REPORT_ERROR("AMIQ_ETH", str.c_str());
			break;
		}
	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack(packer);
		header.do_pack(packer);
		pack_body(packer);
		pack_fcs(packer);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_packet_ether_type::do_unpack(packer);
		header.do_unpack(packer);

		switch (header.message_type) {
		case PTP_AnnounceMessage:
			announce_message_body.do_unpack(packer);
			break;
		case PTP_SyncMessage:
			sync_message_body.do_unpack(packer);
			break;
		case PTP_Delay_ReqMessage:
			delay_req_message_body.do_unpack(packer);
			break;
		default:
			stringstream ss;
			ss << "Could not determine message type: " << std::hex << header.message_type;
			string str = ss.str();
			SC_REPORT_ERROR("AMIQ_ETH", str.c_str());
			break;
		}

		amiq_eth_do_unpack(packer, fcs);
	}

	//function for packing the Ethernet packet using only the required information for computing the FCS
	//@param bitstream - the packed bit stream is placed in "bitstream" parameter
	virtual void do_pack_for_fcs(amiq_eth_packer& packer) const {
		amiq_eth_packet_ether_type::do_pack_for_fcs(packer);
		header.do_pack(packer);
		pack_body(packer);
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
		switch (header.message_type) {
		case PTP_AnnounceMessage:
			announce_message_body.do_print(out);
			break;
		case PTP_SyncMessage:
			sync_message_body.do_print(out);
			break;
		case PTP_Delay_ReqMessage:
			delay_req_message_body.do_print(out);
			break;
		default:
			stringstream ss;
			ss << "Could not determine message type: " << std::hex << header.message_type;
			string str = ss.str();
			SC_REPORT_ERROR("AMIQ_ETH", str.c_str());
			break;
		}
		out << "FCS: " << std::hex << fcs.to_uint() << ", " << fcs_info << endl;
	}

	//function for packing the Ethernet packet into an UVM generic payload class
	//@return an instance of the UVM generic payload containing the packed Ethernet packet
	virtual tlm_generic_payload * to_generic_payload() const {
		tlm_generic_payload * result = (amiq_eth_packet_ether_type::to_generic_payload());
		result->set_address(AMIQ_ETH_PACKET_PTP_CODE);

		return result;
	}
};


#endif
