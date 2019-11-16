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
 * NAME:        amiq_eth_pcap_util.sv
 * PROJECT:     amiq_eth
 * Description: This file contains the necessary logic in order to write some
 *              information in pcap file format.
 *              The logic was implemented based on description from:
 *              http://wiki.wireshark.org/Development/LibpcapFileFormat
 *******************************************************************************/

`ifndef __AMIQ_ETH_PCAP_UTIL
	//protection against multiple includes
	`define __AMIQ_ETH_PCAP_UTIL

`define AMIQ_ETH_PACK_FOR_PCAP(DATA, ARRAY) \
begin \
    integer number_of_bits = $bits(DATA); \
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); \
    for(int i = 0; i < number_of_bytes; i++) begin \
        byte unsigned data = (DATA >> (i * 8)) & 8'hFF; \
        ARRAY.push_back(data); \
    end \
end \

//base class for implementing the headers
virtual class amiq_eth_pcap_hdr_base;
	//pack the header into a list of bytes
	//@param byte_data - destinations of the packed bytes
	pure virtual function void pack_to_bytes(ref byte unsigned byte_data [$]);
endclass

//global header class - http://wiki.wireshark.org/Development/LibpcapFileFormat#Global_Header
class amiq_eth_pcap_hdr_s extends amiq_eth_pcap_hdr_base;

	//magic number
	bit[31:0] magic_number;

	//major version number
	bit[15:0] version_major;

	//minor version number
	bit[15:0] version_minor;

	//GMT to local correction
	bit[31:0] thiszone;

	//accuracy of timestamps
	bit[31:0] sigfigs;

	//max length of captured packets, in octets
	bit[31:0] snaplen;

	//data link type
	bit[31:0] network;

	//constructor
	function new();
		super.new();
		magic_number = 32'ha1b2c3d4;
		version_major = 2;
		version_minor = 4;
		thiszone = 0;
		sigfigs = 0;
		snaplen = 32'h0000ffff;
		network = 1;
	endfunction

	//pack the global header into a list of bytes
	//@param byte_data - destinations of the packed bytes
	virtual function void pack_to_bytes(ref byte unsigned byte_data[$]);
		`AMIQ_ETH_PACK_FOR_PCAP(magic_number, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(version_major, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(version_minor, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(thiszone, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(sigfigs, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(snaplen, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(network, byte_data);
	endfunction

endclass

//packet header class - http://wiki.wireshark.org/Development/LibpcapFileFormat#Record_.28Packet.29_Header
class amiq_eth_pcaprec_hdr_s extends amiq_eth_pcap_hdr_base;

	//timestamp seconds
	bit[31:0] ts_sec;

	//timestamp microseconds
	bit[31:0] ts_usec;

	//number of octets of packet saved in file
	bit[31:0] incl_len;

	//actual length of packet
	bit[31:0] orig_len;

	//constructor
	function new();
		super.new();
		ts_sec = 0;
		ts_usec = 0;
		incl_len = 0;
		orig_len = 0;
	endfunction

	//pack the packet header into a list of bytes
	//@param byte_data - destinations of the packed bytes
	virtual function void pack_to_bytes(ref byte unsigned byte_data[$]);
		`AMIQ_ETH_PACK_FOR_PCAP(ts_sec, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(ts_usec, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(incl_len, byte_data);
		`AMIQ_ETH_PACK_FOR_PCAP(orig_len, byte_data);
	endfunction

endclass

//Class containing the necessary logic for building the PCAP file.
//All functions are static so it can be easily accessible from anywhere in the code
class amiq_eth_pcap_util;

	//write a byte to a binary file
	//@param file - handler to the file in which to write the byte
	//@param data - byte to write to file
	static function void write_byte(integer file, byte unsigned data);
		$fwrite(file, "%c", data);
	endfunction

	//write a queue of bytes to a binary file
	//@param file - handler to the file in which to write the byte
	//@param byte_data - bytes to write to file
	static function void write_bytes(integer file, byte unsigned byte_data[$]);
		for(int i = 0; i < byte_data.size(); i++) begin
			write_byte(file, byte_data[i]);
		end
	endfunction

	//write a header to a binary file
	//@param file - handler to the file in which to write the byte
	//@param header - header to write to file
	static function void write_header(integer file, amiq_eth_pcap_hdr_base header);
		byte unsigned byte_data[$];
		header.pack_to_bytes(byte_data);

		write_bytes(file, byte_data);
	endfunction

	//initialize a PCAP formatted file with a global header
	//@param file_name - the name of the file in which to write the global header
	//@param header - global header to write in the PCAP file
	//@return returns the handler to the open file
	static function integer init_pcap_file_with_global_header(string file_name, amiq_eth_pcap_hdr_s global_header);
		integer result = $fopen(file_name, "wb");
		write_header(result, global_header);
		return result;
	endfunction

	//initialize a PCAP formatted file with a default global header
	//@param file_name - the name of the file in which to write the global header
	//@return returns the handler to the open file
	static function integer init_pcap_file(string file_name);
		amiq_eth_pcap_hdr_s global_header = new();
		return init_pcap_file_with_global_header(file_name, global_header);
	endfunction

	//write to a PCAP formatted file a queue of bytes
	//@param file - the handler to the open file
	//@param information -  bytes to write to file
	static function void write_to_pcap(integer file, byte unsigned information[$]);
		amiq_eth_pcaprec_hdr_s header = new();
		header.incl_len = information.size();
		header.orig_len = information.size();

		write_header(file, header);
		for(int i = 0; i < information.size(); i++) begin
			write_byte(file, information[i]);
		end
	endfunction

endclass

//class for live-streamming information into a PCAP file.
class amiq_eth_pcap_livestream;
	
	//file handler
	local integer file_pcap;

	//constructor
	//@param file_name - the name of the PCAP file - .pcap extention will be automatically appended
	function new(string file_name);
		file_pcap = amiq_eth_pcap_util::init_pcap_file($sformatf("%s.pcap", file_name));
	endfunction

	//write to PCAP file the ethernet packet
	//@param packet - the ethernet packet to write to pcap file
	function void broadcast(amiq_eth_packet packet);
		byte unsigned info[$];
		packet.to_wireshark_array(info);
		amiq_eth_pcap_util::write_to_pcap(file_pcap, info);
	endfunction

	//stop the live streaming
	function void stop();
		$fclose(file_pcap);
	endfunction

endclass

`endif