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
 * NAME:        amiq_eth_packet_length.cpp
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration of the basic Ethernet frame
 * 				in which Length/Type field is interpreted as Length.
 * 				The definition of this packet is described in IEEE 802.3-2012.
 * 				For more details see file docs/ieee_802.3-2012/802.3-2012_section1.pdf,
 * 				chapter 3. Media Access Control (MAC) frame and packet specifications
 *******************************************************************************/

#ifndef __AMIQ_ETH_PACKET_LENGTH
//protection against multiple includes
#define __AMIQ_ETH_PACKET_LENGTH

using namespace std;

//Basic class for declaring the Ethernet packets in which Length/Type field is interpreted as Length.
class amiq_eth_packet_length: public amiq_eth_packet {

public:

	//Length
	amiq_eth_length_type length_type;

	//Payload
	amiq_eth_data *payload;

	//Frame Check Sequence
	amiq_eth_fcs fcs;

	//constructor
	amiq_eth_packet_length() {
		payload = NULL;
	}

	//destructor
	virtual ~amiq_eth_packet_length() {
		delete[] payload;
	}

	//prints the current class to a given output stream
	//@param out - output stream
	virtual void do_print(ostream& out) const {

	}

	//pack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_pack(amiq_eth_packer& packer) const {
		amiq_eth_data payload_item;
		amiq_eth_packet::do_pack(packer);
		amiq_eth_do_pack(packer, length_type);

		for (unsigned int index = 0; index < length_type.to_uint(); index++) {
			payload_item = payload[index];
			amiq_eth_do_pack(packer, payload_item);
		}
		amiq_eth_do_pack(packer, fcs);
	}

	//unpack the entire Ethernet packet
	//@param packer - the packer used by this function
	virtual void do_unpack(amiq_eth_packer& packer) {
		amiq_eth_data payload_item;
		amiq_eth_packet::do_unpack(packer);
		amiq_eth_do_unpack(packer, length_type);
		payload = new amiq_eth_data[length_type.to_int()];
		for (unsigned int index = 0; index < length_type.to_uint(); index++) {
			amiq_eth_do_unpack(packer, payload_item);
			payload[index] = payload_item;
		}
		amiq_eth_do_unpack(packer, fcs);
	}
};

#endif
