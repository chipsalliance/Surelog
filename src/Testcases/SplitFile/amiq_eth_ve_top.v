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
 * NAME:        amiq_eth_ve_top.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the top module from which the UVM flow is run
 *******************************************************************************/

		
`timescale 10ns/10ns

/* SLline 1 "./ve/sv/amiq_eth_ve_pkg.sv" 1 */


            
/* SLline 1 "./sv/amiq_eth_pkg.sv" 1 */


		
package amiq_eth_pkg;

	
	import uvm_pkg::*;

			/* SLline 1 "./sv/amiq_eth_types.sv" 1 */


        

typedef bit[56 - 1:0] amiq_eth_preamble;

typedef bit[8 - 1:0] amiq_eth_sfd;

typedef bit[48 - 1:0] amiq_eth_address;

typedef bit[16 - 1:0] amiq_eth_length;

typedef bit[32 - 1:0] amiq_eth_fcs;

typedef bit[8 - 1:0] amiq_eth_data;

typedef bit[1 - 1:0] amiq_eth_extension;

typedef enum bit[16-1:0] {
    AMIQ_ETH_IPV4 = 16'h0800 ,
    AMIQ_ETH_ARP = 16'h0806 ,
    AMIQ_ETH_WAKE_ON_LAN = 16'h0842 ,
    AMIQ_ETH_IETF_TRILL = 16'h22F3 ,
    AMIQ_ETH_DECNET_PHASE_IV = 16'h6003 ,
    AMIQ_ETH_RARP = 16'h8035 ,
    AMIQ_ETH_APPLE_TALK = 16'h809B ,
    AMIQ_ETH_AARP = 16'h80F3 ,
    AMIQ_ETH_VLAN_TAGGED_FRAME_SHORT_PATH_BRIDGING = 16'h8100 ,
    AMIQ_ETH_IPX_1 = 16'h8137 ,
    AMIQ_ETH_IPX_2 = 16'h8138 ,
    AMIQ_ETH_QNX_QNET = 16'h8204,
    AMIQ_ETH_IPV6 = 16'h86DD,
    AMIQ_ETH_MAC_CONTROL = 16'h8808 ,
    AMIQ_ETH_SLOW_PROTOCOLS = 16'h8809 ,
    AMIQ_ETH_COBRANET = 16'h8819 ,
    AMIQ_ETH_MPLS_UNICAST = 16'h8847 ,
    AMIQ_ETH_MPLS_MULTICAST = 16'h8848 ,
    AMIQ_ETH_PPPOE_DISCOVERY = 16'h8863 ,
    AMIQ_ETH_PPPOE_SESSION = 16'h8864 ,
    AMIQ_ETH_JUMBO_FRAMES = 16'h8870 ,
    AMIQ_ETH_HOMEPLUG = 16'h887B ,
    AMIQ_ETH_EAP_OVER_LAN = 16'h888E ,
    AMIQ_ETH_PROFINET = 16'h8892 ,
    AMIQ_ETH_SCSI_OVER_ETHERNET = 16'h889A ,
    AMIQ_ETH_ATA_OVER_ETHERNET = 16'h88A2 ,
    AMIQ_ETH_ETHERCAT = 16'h88A4 ,
    AMIQ_ETH_PROVIDER_BRIDGING_SHORT_PATH_BRIDGING = 16'h88A8 ,
    AMIQ_ETH_POWERLINK = 16'h88AB ,
    AMIQ_ETH_LLDP = 16'h88CC ,
    AMIQ_ETH_SERCOS_III = 16'h88CD ,
    AMIQ_ETH_HOMEPLUG_AV_MME = 16'h88E1 ,
    AMIQ_ETH_MEDIA_REDUNDANCY = 16'h88E3 ,
    AMIQ_ETH_MAC_SECURITY = 16'h88E5 ,
    AMIQ_ETH_PTP = 16'h88F7 ,
    AMIQ_ETH_CFM_OAM = 16'h8902 ,
    AMIQ_ETH_FCOE = 16'h8906 ,
    AMIQ_ETH_FCOE_INIT = 16'h8914 ,
    AMIQ_ETH_ROCE = 16'h8915 ,
    AMIQ_ETH_HSR = 16'h892F ,
    AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL = 16'h9000 ,
    AMIQ_ETH_Q_IN_Q = 16'h9100 ,
    AMIQ_ETH_LLT_FOR_CLUSTER_SERVER = 16'hCAFE
} amiq_eth_ether_type;



typedef bit[40 - 1:0] amiq_eth_snap_protocol_identifier;



typedef bit[32 - 1:0] amiq_eth_jumbo_client_data_size;



typedef bit[16 - 1:0] amiq_eth_pfc_opcode;

typedef bit[16 - 1:0] amiq_eth_pfc_parameter;

typedef bit[16 - 1:0] amiq_eth_pfc_class_enable_vector;



typedef bit[16 - 1:0] amiq_eth_pause_parameter;

typedef bit[16 - 1:0] amiq_eth_pause_opcode;



typedef bit[16 - 1:0] amiq_eth_ethernet_configuration_testing_skipcount;

typedef enum bit[16 - 1:0] {
    REPLY = 1 ,
    FORWARD = 2
} amiq_eth_ethernet_configuration_testing_function;



typedef bit[4 - 1:0] amiq_eth_hsr_path;

typedef bit[12 - 1:0] amiq_eth_hsr_size;

typedef bit[16 - 1:0] amiq_eth_hsr_seq;



typedef bit[4 - 1:0] amiq_eth_ipv4_header_version;

typedef bit[4 - 1:0] amiq_eth_ipv4_header_ihl;

typedef bit[6 - 1:0] amiq_eth_ipv4_header_dscp;

typedef bit[2 - 1:0] amiq_eth_ipv4_header_ecn;

typedef bit[16 - 1:0] amiq_eth_ipv4_header_total_length;

typedef bit[16 - 1:0] amiq_eth_ipv4_header_identification;

typedef bit[3 - 1:0] amiq_eth_ipv4_header_flags;

typedef bit[13 - 1:0] amiq_eth_ipv4_header_fragment_offset;

typedef bit[8 - 1:0] amiq_eth_ipv4_header_ttl;

typedef bit[8 - 1:0] amiq_eth_ipv4_header_protocol;

typedef bit[16 - 1:0] amiq_eth_ipv4_header_checksum;

typedef bit[32 - 1:0] amiq_eth_ipv4_header_source_ip_address;

typedef bit[32 - 1:0] amiq_eth_ipv4_header_destination_ip_address;

typedef bit[32 - 1:0] amiq_eth_ipv4_header_option;



typedef bit[16 - 1:0] amiq_eth_arp_htype;

typedef bit[16 - 1:0] amiq_eth_arp_ptype;

typedef bit[8 - 1:0] amiq_eth_arp_hlen;

typedef bit[8 - 1:0] amiq_eth_arp_plen;

typedef bit[16 - 1:0] amiq_eth_arp_oper;

typedef bit[48 - 1:0] amiq_eth_arp_sha;

typedef bit[32 - 1:0] amiq_eth_arp_spa;

typedef bit[48 - 1:0] amiq_eth_arp_tha;

typedef bit[32 - 1:0] amiq_eth_arp_tpa;



typedef bit[4 - 1:0] amiq_eth_fcoe_version;

typedef enum bit[8 - 1:0] {
    AMIQ_ETH_FCOE_SOFf = 8'h28,
    AMIQ_ETH_FCOE_SOFi2 = 8'h2D,
    AMIQ_ETH_FCOE_SOFn2 = 8'h35,
    AMIQ_ETH_FCOE_SOFi3 = 8'h2E,
    AMIQ_ETH_FCOE_SOFn3 = 8'h36
} amiq_eth_fcoe_sof;

typedef enum bit[8 - 1:0] {
    AMIQ_ETH_FCOE_EOFn = 8'h41,
    AMIQ_ETH_FCOE_EOFt = 8'h42,
    AMIQ_ETH_FCOE_EOFni = 8'h49,
    AMIQ_ETH_FCOE_EOFa = 8'h50
} amiq_eth_fcoe_eof;



typedef enum bit[4 - 1:0] {
    PTP_in_IEEE1588 = 0,
    PTP_in_802_1_as = 1
} amiq_eth_ptp_transport_specific;

typedef enum bit[4 - 1:0] {
    PTP_SyncMessage = 0,
    PTP_Delay_ReqMessage = 1,
    PTP_Pdelay_ReqMessage = 2,
    PTP_Pdelay_RespMessage = 3,
    PTP_Follow_UpMessage = 8,
    PTP_Delay_RespMessage = 9,
    PTP_Pdelay_Resp_Follow_UpMessage = 10,
    PTP_AnnounceMessage = 11,
    PTP_SignallingMessage = 12,
    PTP_ManagementMessage = 13
} amiq_eth_ptp_message_type;

typedef bit[4 - 1:0] amiq_eth_ptp_version;

typedef bit[16 - 1:0] amiq_eth_ptp_message_length;

typedef bit[8 - 1:0] amiq_eth_ptp_domain_number;

typedef bit[16 - 1:0] amiq_eth_ptp_flags;

typedef bit[64 - 1:0] amiq_eth_ptp_correction_field;

typedef bit[16 - 1:0] amiq_eth_ptp_sequence_id;

typedef enum bit[8 - 1:0] {
    PTP_SyncMessage_ctrl = 0,
    PTP_Delay_ReqMessage_ctrl = 1,
    PTP_Follow_UpMessage_ctrl = 2,
    PTP_Delay_RespMessage_ctrl = 3,
    PTP_ManagementMessage_ctrl = 4
} amiq_eth_ptp_control_field_type;

typedef bit[8 - 1:0] amiq_eth_ptp_log_message;

typedef bit[16 - 1:0] amiq_eth_ptp_announce_message_current_utc_offset;

typedef bit[8 - 1:0] amiq_eth_ptp_announce_message_grandmaster_priority_1;

typedef bit[32 - 1:0] amiq_eth_ptp_announce_message_grandmaster_clock_quality;

typedef bit[8 - 1:0] amiq_eth_ptp_announce_message_grandmaster_priority_2;

typedef bit[64 - 1:0] amiq_eth_ptp_announce_message_grandmaster_identity;

typedef bit[16 - 1:0] amiq_eth_ptp_announce_message_steps_removed;

typedef bit[8 - 1:0] amiq_eth_ptp_announce_message_time_source;



/* SLline 35 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet.sv" 1 */


		
virtual class amiq_eth_packet extends uvm_object;

	rand int min_frame_size;

	constraint min_frame_size_c {
		min_frame_size == 64;
	}

		rand amiq_eth_preamble preamble;

		rand amiq_eth_sfd sfd;

		rand amiq_eth_address destination_address;

		rand amiq_eth_address source_address;

		local bit pack_preamble;

		local bit pack_sfd;

		local bit pack_destination_address;

		local bit pack_source_address;

			function new(string name = "");
		super.new(name);
		min_frame_size = 64;
		pack_preamble = 1;
		pack_sfd = 1;
		pack_destination_address = 1;
		pack_source_address = 1;
	endfunction

							virtual function void do_pack_with_options(uvm_packer packer, bit local_pack_preamble, bit local_pack_sfd, bit local_pack_destination_address, bit local_pack_source_address);
		if(local_pack_preamble) begin
			
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
		end

		if(local_pack_sfd) begin
			
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
		end

		if(local_pack_destination_address) begin
			
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
		end

		if(local_pack_source_address) begin
			
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
		end
	endfunction

							virtual function void do_unpack_with_options(uvm_packer packer, bit local_pack_preamble, bit local_pack_sfd, bit local_pack_destination_address, bit local_pack_source_address);
		if(local_pack_preamble) begin
			
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
		end

		if(local_pack_sfd) begin
			
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
		end

		if(local_pack_destination_address) begin
			
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
		end

		if(local_pack_source_address) begin
			
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
		end
	endfunction

			virtual function void do_pack(uvm_packer packer);
		do_pack_with_options(packer, pack_preamble, pack_sfd, pack_destination_address, pack_source_address);
	endfunction

			virtual function void do_unpack(uvm_packer packer);
		do_unpack_with_options(packer, pack_preamble, pack_sfd, pack_destination_address, pack_source_address);
	endfunction

			virtual function void set_pack_destination_address(bit new_val);
		pack_destination_address = new_val;
	endfunction

			virtual function bit get_pack_destination_address();
		return pack_destination_address;
	endfunction

			virtual function void set_pack_source_address(bit new_val);
		pack_source_address = new_val;
	endfunction

			virtual function bit get_pack_source_address();
		return pack_source_address;
	endfunction

			virtual function void set_pack_preamble(bit new_val);
		pack_preamble = new_val;
	endfunction

			virtual function bit get_pack_preamble();
		return pack_preamble;
	endfunction

			virtual function void set_pack_sfd(bit new_val);
		pack_sfd = new_val;
	endfunction

			virtual function bit get_pack_sfd();
		return pack_sfd;
	endfunction

			virtual function string convert2string();
		string what_to_return;
		$sformat(what_to_return, {what_to_return,"PREAMBLE: %014X ", ", "},preamble);
		$sformat(what_to_return, {what_to_return,"SDF: %02X ", ", "},sfd);
		$sformat(what_to_return, {what_to_return,"DA: %012X ", ", "},destination_address);
		$sformat(what_to_return, {what_to_return,"SA: %012X "},source_address);
		return what_to_return;
	endfunction

			virtual function uvm_tlm_generic_payload to_generic_payload();
		uvm_tlm_generic_payload result = uvm_tlm_generic_payload::type_id::create("result");
		bit bitstream[];
		byte unsigned gp_data [];

		void'(pack(bitstream));

		gp_data = {>> {bitstream}};

		result.set_data(gp_data);
		result.set_data_length(gp_data.size());
		result.set_response_status(UVM_TLM_OK_RESPONSE);

		return result;
	endfunction

					virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
		amiq_eth_packet casted_rhs;

		if($cast(casted_rhs, rhs) == 0) begin
			return 0;
		end

		if(preamble != casted_rhs.preamble) begin
			return 0;
		end

		if(sfd != casted_rhs.sfd) begin
			return 0;
		end

		if(destination_address != casted_rhs.destination_address) begin
			return 0;
		end

		if(source_address != casted_rhs.source_address) begin
			return 0;
		end

		return 1;
	endfunction

			virtual function void pack_for_fcs(ref bit bitstream[]);
		bit current_pack_preamble = pack_preamble;
		bit current_pack_sfd = pack_sfd;

		pack_preamble = 0;
		pack_sfd = 0;

		void'(pack(bitstream));

		pack_preamble = current_pack_preamble;
		pack_sfd = current_pack_sfd;
	endfunction

	static protected amiq_eth_fcs crc32_ccitt_table[] = {
		32'h00000000, 32'h77073096, 32'hee0e612c, 32'h990951ba, 32'h076dc419,
		32'h706af48f, 32'he963a535, 32'h9e6495a3, 32'h0edb8832, 32'h79dcb8a4,
		32'he0d5e91e, 32'h97d2d988, 32'h09b64c2b, 32'h7eb17cbd, 32'he7b82d07,
		32'h90bf1d91, 32'h1db71064, 32'h6ab020f2, 32'hf3b97148, 32'h84be41de,
		32'h1adad47d, 32'h6ddde4eb, 32'hf4d4b551, 32'h83d385c7, 32'h136c9856,
		32'h646ba8c0, 32'hfd62f97a, 32'h8a65c9ec, 32'h14015c4f, 32'h63066cd9,
		32'hfa0f3d63, 32'h8d080df5, 32'h3b6e20c8, 32'h4c69105e, 32'hd56041e4,
		32'ha2677172, 32'h3c03e4d1, 32'h4b04d447, 32'hd20d85fd, 32'ha50ab56b,
		32'h35b5a8fa, 32'h42b2986c, 32'hdbbbc9d6, 32'hacbcf940, 32'h32d86ce3,
		32'h45df5c75, 32'hdcd60dcf, 32'habd13d59, 32'h26d930ac, 32'h51de003a,
		32'hc8d75180, 32'hbfd06116, 32'h21b4f4b5, 32'h56b3c423, 32'hcfba9599,
		32'hb8bda50f, 32'h2802b89e, 32'h5f058808, 32'hc60cd9b2, 32'hb10be924,
		32'h2f6f7c87, 32'h58684c11, 32'hc1611dab, 32'hb6662d3d, 32'h76dc4190,
		32'h01db7106, 32'h98d220bc, 32'hefd5102a, 32'h71b18589, 32'h06b6b51f,
		32'h9fbfe4a5, 32'he8b8d433, 32'h7807c9a2, 32'h0f00f934, 32'h9609a88e,
		32'he10e9818, 32'h7f6a0dbb, 32'h086d3d2d, 32'h91646c97, 32'he6635c01,
		32'h6b6b51f4, 32'h1c6c6162, 32'h856530d8, 32'hf262004e, 32'h6c0695ed,
		32'h1b01a57b, 32'h8208f4c1, 32'hf50fc457, 32'h65b0d9c6, 32'h12b7e950,
		32'h8bbeb8ea, 32'hfcb9887c, 32'h62dd1ddf, 32'h15da2d49, 32'h8cd37cf3,
		32'hfbd44c65, 32'h4db26158, 32'h3ab551ce, 32'ha3bc0074, 32'hd4bb30e2,
		32'h4adfa541, 32'h3dd895d7, 32'ha4d1c46d, 32'hd3d6f4fb, 32'h4369e96a,
		32'h346ed9fc, 32'had678846, 32'hda60b8d0, 32'h44042d73, 32'h33031de5,
		32'haa0a4c5f, 32'hdd0d7cc9, 32'h5005713c, 32'h270241aa, 32'hbe0b1010,
		32'hc90c2086, 32'h5768b525, 32'h206f85b3, 32'hb966d409, 32'hce61e49f,
		32'h5edef90e, 32'h29d9c998, 32'hb0d09822, 32'hc7d7a8b4, 32'h59b33d17,
		32'h2eb40d81, 32'hb7bd5c3b, 32'hc0ba6cad, 32'hedb88320, 32'h9abfb3b6,
		32'h03b6e20c, 32'h74b1d29a, 32'head54739, 32'h9dd277af, 32'h04db2615,
		32'h73dc1683, 32'he3630b12, 32'h94643b84, 32'h0d6d6a3e, 32'h7a6a5aa8,
		32'he40ecf0b, 32'h9309ff9d, 32'h0a00ae27, 32'h7d079eb1, 32'hf00f9344,
		32'h8708a3d2, 32'h1e01f268, 32'h6906c2fe, 32'hf762575d, 32'h806567cb,
		32'h196c3671, 32'h6e6b06e7, 32'hfed41b76, 32'h89d32be0, 32'h10da7a5a,
		32'h67dd4acc, 32'hf9b9df6f, 32'h8ebeeff9, 32'h17b7be43, 32'h60b08ed5,
		32'hd6d6a3e8, 32'ha1d1937e, 32'h38d8c2c4, 32'h4fdff252, 32'hd1bb67f1,
		32'ha6bc5767, 32'h3fb506dd, 32'h48b2364b, 32'hd80d2bda, 32'haf0a1b4c,
		32'h36034af6, 32'h41047a60, 32'hdf60efc3, 32'ha867df55, 32'h316e8eef,
		32'h4669be79, 32'hcb61b38c, 32'hbc66831a, 32'h256fd2a0, 32'h5268e236,
		32'hcc0c7795, 32'hbb0b4703, 32'h220216b9, 32'h5505262f, 32'hc5ba3bbe,
		32'hb2bd0b28, 32'h2bb45a92, 32'h5cb36a04, 32'hc2d7ffa7, 32'hb5d0cf31,
		32'h2cd99e8b, 32'h5bdeae1d, 32'h9b64c2b0, 32'hec63f226, 32'h756aa39c,
		32'h026d930a, 32'h9c0906a9, 32'heb0e363f, 32'h72076785, 32'h05005713,
		32'h95bf4a82, 32'he2b87a14, 32'h7bb12bae, 32'h0cb61b38, 32'h92d28e9b,
		32'he5d5be0d, 32'h7cdcefb7, 32'h0bdbdf21, 32'h86d3d2d4, 32'hf1d4e242,
		32'h68ddb3f8, 32'h1fda836e, 32'h81be16cd, 32'hf6b9265b, 32'h6fb077e1,
		32'h18b74777, 32'h88085ae6, 32'hff0f6a70, 32'h66063bca, 32'h11010b5c,
		32'h8f659eff, 32'hf862ae69, 32'h616bffd3, 32'h166ccf45, 32'ha00ae278,
		32'hd70dd2ee, 32'h4e048354, 32'h3903b3c2, 32'ha7672661, 32'hd06016f7,
		32'h4969474d, 32'h3e6e77db, 32'haed16a4a, 32'hd9d65adc, 32'h40df0b66,
		32'h37d83bf0, 32'ha9bcae53, 32'hdebb9ec5, 32'h47b2cf7f, 32'h30b5ffe9,
		32'hbdbdf21c, 32'hcabac28a, 32'h53b39330, 32'h24b4a3a6, 32'hbad03605,
		32'hcdd70693, 32'h54de5729, 32'h23d967bf, 32'hb3667a2e, 32'hc4614ab8,
		32'h5d681b02, 32'h2a6f2b94, 32'hb40bbe37, 32'hc30c8ea1, 32'h5a05df1b,
		32'h2d02ef8d
	};

	static protected function int unsigned crc32_ccitt_seed(byte unsigned byte_data [], int unsigned seed);
		int unsigned crc32 = seed;

		for(int i = 0; i < byte_data.size(); i++) begin
			byte unsigned index = (crc32 ^ byte_data[i]) & 8'hff;
			crc32 = crc32_ccitt_table[index] ^ (crc32 >> 8);
		end

		return (~crc32);
	endfunction

	static protected function int unsigned get_crc32_ccitt(byte unsigned byte_data []);
		return (crc32_ccitt_seed(byte_data, 32'hFFFFFFFF));
	endfunction

	static protected function int unsigned swap_bytes(int unsigned data);
		byte unsigned byte_data [];

		byte_data = {>> {data}};
		byte_data.reverse();
		data = { >> {byte_data}};

		return data;
	endfunction

	static protected function int unsigned get_crc32_802(byte unsigned byte_data []);
		int unsigned c_crc;

		c_crc = get_crc32_ccitt(byte_data);

		c_crc = swap_bytes(c_crc);
		return c_crc;
	endfunction

        	virtual function amiq_eth_fcs get_correct_fcs();
		bit bitstream[];
		byte unsigned byte_data [];
		pack_for_fcs(bitstream);
		byte_data = {>> {bitstream}};

		get_correct_fcs = get_crc32_802(byte_data);
	endfunction

			virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
		bit bitstream[];
		bit current_pack_preamble = pack_preamble;
		bit current_pack_sfd = pack_sfd;

		pack_preamble = 0;
		pack_sfd = 0;

		void'(pack(bitstream));

		pack_preamble = current_pack_preamble;
		pack_sfd = current_pack_sfd;

		byte_data = {>> {bitstream}};
	endfunction

			virtual function string to_wireshark_string();
		string result = "";
		byte unsigned byte_data[$];
		to_wireshark_array(byte_data);

		for(int i = 0; i < byte_data.size(); i++) begin
			result = $sformatf("%s%06X %02X \n", result, i, byte_data[i]);
		end

		return result;
	endfunction

endclass


/* SLline 36 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_pcap_util.sv" 1 */


		
virtual class amiq_eth_pcap_hdr_base;
			pure virtual function void pack_to_bytes(ref byte unsigned byte_data [$]);
endclass

class amiq_eth_pcap_hdr_s extends amiq_eth_pcap_hdr_base;

		bit[31:0] magic_number;

		bit[15:0] version_major;

		bit[15:0] version_minor;

		bit[31:0] thiszone;

		bit[31:0] sigfigs;

		bit[31:0] snaplen;

		bit[31:0] network;

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

			virtual function void pack_to_bytes(ref byte unsigned byte_data[$]);
		
begin 
    integer number_of_bits = $bits(magic_number); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (magic_number >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(version_major); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (version_major >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(version_minor); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (version_minor >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(thiszone); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (thiszone >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(sigfigs); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (sigfigs >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(snaplen); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (snaplen >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(network); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (network >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
	endfunction

endclass

class amiq_eth_pcaprec_hdr_s extends amiq_eth_pcap_hdr_base;

		bit[31:0] ts_sec;

		bit[31:0] ts_usec;

		bit[31:0] incl_len;

		bit[31:0] orig_len;

		function new();
		super.new();
		ts_sec = 0;
		ts_usec = 0;
		incl_len = 0;
		orig_len = 0;
	endfunction

			virtual function void pack_to_bytes(ref byte unsigned byte_data[$]);
		
begin 
    integer number_of_bits = $bits(ts_sec); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (ts_sec >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(ts_usec); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (ts_usec >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(incl_len); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (incl_len >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
		
begin 
    integer number_of_bits = $bits(orig_len); 
    int unsigned number_of_bytes = $ceil(number_of_bits / 8); 
    for(int i = 0; i < number_of_bytes; i++) begin 
        byte unsigned data = (orig_len >> (i * 8)) & 8'hFF; 
        byte_data.push_back(data); 
    end 
end 
;
	endfunction

endclass

class amiq_eth_pcap_util;

				static function void write_byte(integer file, byte unsigned data);
		$fwrite(file, "%c", data);
	endfunction

				static function void write_bytes(integer file, byte unsigned byte_data[$]);
		for(int i = 0; i < byte_data.size(); i++) begin
			write_byte(file, byte_data[i]);
		end
	endfunction

				static function void write_header(integer file, amiq_eth_pcap_hdr_base header);
		byte unsigned byte_data[$];
		header.pack_to_bytes(byte_data);

		write_bytes(file, byte_data);
	endfunction

					static function integer init_pcap_file_with_global_header(string file_name, amiq_eth_pcap_hdr_s global_header);
		integer result = $fopen(file_name, "wb");
		write_header(result, global_header);
		return result;
	endfunction

				static function integer init_pcap_file(string file_name);
		amiq_eth_pcap_hdr_s global_header = new();
		return init_pcap_file_with_global_header(file_name, global_header);
	endfunction

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

class amiq_eth_pcap_livestream;
	
		local integer file_pcap;

			function new(string file_name);
		file_pcap = amiq_eth_pcap_util::init_pcap_file($sformatf("%s.pcap", file_name));
	endfunction

			function void broadcast(amiq_eth_packet packet);
		byte unsigned info[$];
		packet.to_wireshark_array(info);
		amiq_eth_pcap_util::write_to_pcap(file_pcap, info);
	endfunction

		function void stop();
		$fclose(file_pcap);
	endfunction

endclass


/* SLline 37 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_length.sv" 1 */


        
class amiq_eth_packet_length extends amiq_eth_packet;
    
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 


    
        rand amiq_eth_length length;
    
    constraint length_constraint {
        length >= 46 &&
        length <= 1500;
    }
    
        rand amiq_eth_data client_data[$];
    
    constraint client_data_constraint {
        client_data.size() == length;
    }
    
        rand amiq_eth_fcs fcs;
    
            function new(string name = "");
        super.new(name);
    endfunction
    
            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end


;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction
    
            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
    while (client_data.size() > sz__) 
      void'(client_data.pop_back()); 
    for (int i=0; i<sz__; i++) 
      
   begin 
      int __array[] = new[($bits(client_data[0])+31)/32]; 
      bit [((($bits(client_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(client_data[0])); 
      __var = { << int { __array }}; 
      client_data[i] = __var; 
   end
 
    end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction
    
            virtual function string convert2string();
        return $sformatf("%s, Length: %0d, Client DATA size: %0d, FCS: %08X",
            super.convert2string(), length, client_data.size(), fcs);
    endfunction
    
            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0005);
        
        return result;
    endfunction
    
endclass
    

/* SLline 38 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_ether_type.sv" 1 */


        
virtual class amiq_eth_packet_ether_type extends amiq_eth_packet;

        protected amiq_eth_ether_type ether_type;
    
    local bit pack_ether_type;

        function amiq_eth_ether_type get_ether_type();
        return ether_type;
    endfunction

            function new(string name = "");
        super.new(name);
        pack_ether_type = 1;
    endfunction

                virtual function void do_pack_ether_type(uvm_packer packer, bit local_pack_ether_type);
        if (local_pack_ether_type) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end 
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        do_pack_ether_type(packer,pack_ether_type);
    endfunction
 
            virtual function void set_pack_ether_type(bit new_val);
        pack_ether_type = new_val;
    endfunction
    
            virtual function bit get_pack_ether_type();
        return pack_ether_type;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        amiq_eth_length int_ether_type;
        super.do_unpack(packer);

        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;

        if(!$cast(ether_type, int_ether_type)) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ether_type.sv", 86); 
   end

        end
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf("%s%s",super.convert2string(), ", ");
        $sformat(what_to_return, {what_to_return,"Type: %s"},ether_type.name());
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ether_type casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(ether_type != casted_rhs.ether_type) begin
            return 0;
        end

        return 1;
    endfunction

endclass


/* SLline 39 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_snap.sv" 1 */


        
class amiq_eth_packet_snap extends amiq_eth_packet;

    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_length length;

    constraint length_constraint {
        length >= 46 &&
        length <= 1500;
    }

        rand amiq_eth_data dsap;

    constraint dsap_c {
        dsap == 8'hAA;
    }

        rand amiq_eth_data ssap;

    constraint ssap_c {
        ssap == 8'hAA;
    }

        rand amiq_eth_data ctl;

    constraint ctl_c {
        ctl == 8'h03;
    }

        rand amiq_eth_snap_protocol_identifier protocol_identifier;

        rand amiq_eth_data protocol_data[];

    constraint protocol_data_constraint {
        protocol_data.size() == length - 8;
    }

        rand amiq_eth_fcs fcs;

        rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

        local bit pack_fcs;

            function new(string name = "");
        super.new(name);
        pack_fcs = 1;
    endfunction

            virtual function void do_pack_fcs(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack_fcs(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;

        if(pack_fcs) begin
            do_pack_fcs(packer);
        end

    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;

		if(!(length >= 8)) begin
        	
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_snap.sv", 133); 
   end
;
		end

        protocol_data = new[length - 8];
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;

        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end

    endfunction

    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction

            virtual function string convert2string();
        string result = super.convert2string();

        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();

        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end

        result = $sformatf("%s%sLength: %0d", result, ", ", length);
        result = $sformatf("%s%sDSAP: %X", result, ", ", dsap);
        result = $sformatf("%s%sSSAP: %X", result, ", ", ssap);
        result = $sformatf("%s%sCTL: %X", result, ", ", ctl);
        result = $sformatf("%s%sPROTOCOL IDENTIFIER: %X", result, ", ", protocol_identifier);
        result = $sformatf("%s%sPROTOCOL DATA size: %0d", result, ", ", protocol_data.size());
        result = $sformatf("%s%sFCS: %X, %s", result, ", ", fcs, fcs_info);

        return result;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0002);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_snap casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(length != casted_rhs.length) begin
            return 0;
        end

        if(dsap != casted_rhs.dsap) begin
            return 0;
        end

        if(ssap != casted_rhs.ssap) begin
            return 0;
        end

        if(ctl != casted_rhs.ctl) begin
            return 0;
        end

        if(protocol_identifier != casted_rhs.protocol_identifier) begin
            return 0;
        end

        if(protocol_data.size() != casted_rhs.protocol_data.size()) begin
            return 0;
        end

        for(int i = 0; i < protocol_data.size(); i++) begin
            if(protocol_data[i] != casted_rhs.protocol_data[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;

        pack_fcs = 0;

        super.pack_for_fcs(bitstream);

        pack_fcs = current_pack_fcs;
    endfunction

endclass


/* SLline 40 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_jumbo.sv" 1 */


        
class amiq_eth_packet_jumbo extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 


    
        rand amiq_eth_jumbo_client_data_size client_data_size;
    
    constraint client_data_size_c {
        client_data_size >= 1501 &&
        client_data_size <= 9000;
    }
    
        rand amiq_eth_data client_data[];
    
    constraint client_data_c {
        solve client_data_size before client_data;
        client_data.size() == client_data_size;
    }
    
        rand amiq_eth_fcs fcs;
    
        rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }
    
        local bit pack_fcs;
    
        local bit pack_client_data_size;
    
            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_JUMBO_FRAMES;
        pack_fcs = 1;
        pack_client_data_size = 1;
    endfunction
    
            virtual function void do_pack_fcs(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;    
    endfunction
    
            virtual function void do_unpack_fcs(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction
    
            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
        if(pack_client_data_size) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end


        end
        
        for(int i = 0; i < client_data.size(); i++) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction
    
            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
        if(pack_client_data_size) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
        
        client_data = new[client_data_size];
        for(int i = 0; i < client_data.size(); i++) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
        
        if(ether_type != AMIQ_ETH_JUMBO_FRAMES) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_jumbo.sv", 125); 
   end
    
        end
        
    endfunction
    
    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction
    
            virtual function string convert2string();
        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();
        
        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end
        
        return $sformatf("%s%sData Size: %0d%sFCS: %X, %s",
            super.convert2string(), ", ", 
            client_data_size, ", ",
            fcs, fcs_info);
    endfunction
    
            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0001);
        
        return result;
    endfunction
    
                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_jumbo casted_rhs;
        
        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end
        
        if($cast(casted_rhs, rhs) == 0) begin
            return 0;    
        end
        
        if(client_data_size != casted_rhs.client_data_size) begin
            return 0;    
        end
        
        if(client_data.size() != casted_rhs.client_data.size()) begin
            return 0;    
        end
        
        for(int i = 0; i < client_data.size(); i++) begin
            if(client_data[i] != casted_rhs.client_data[i]) begin
                return 0;
            end
        end
        
        if(fcs != casted_rhs.fcs) begin
            return 0;    
        end
        
        return 1;
    endfunction
    
            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_fcs = 0;
        pack_client_data_size = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_fcs = current_pack_fcs;
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_client_data_size = 0;
        
        super.to_wireshark_array(byte_data);
        
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
endclass
    

/* SLline 41 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_magic.sv" 1 */


        
class amiq_eth_packet_magic extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_address target_mac;

        rand int unsigned password_size;

        rand amiq_eth_data password[];

        rand int unsigned client_data_size;

    constraint password_c {
        solve password_size before password;
        solve password_size before client_data_size;
        password.size() == password_size;
    }

    constraint client_data_size_c {
        solve password_size before client_data_size;
        solve target_mac before client_data_size;
        password_size inside {0, 4, 6};
                client_data_size >= (((48 + (6 * 48) + (password_size * 8)) / 8)) &&
        client_data_size >= 46 &&
        client_data_size <= 1500;
    }

        rand amiq_eth_data client_data[];

    constraint client_data_c {
        solve client_data_size before client_data;
        client_data.size() == client_data_size;
    }

        rand amiq_eth_fcs fcs;
    
        rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

        rand int unsigned synch_stream_starting_index;

    constraint synch_stream_starting_index_c {
        solve client_data_size before synch_stream_starting_index;
        solve password_size before synch_stream_starting_index;
        synch_stream_starting_index <= client_data_size - 1 - ((48 + (6 * 48) +
                (password_size * 8)) / 8);
    }

    function int unsigned get_useful_info_size();
        int unsigned result = ((48 + (6 * 48) +
                (password_size * 8)) / 8);
        return result;
    endfunction

        local bit pack_fcs;
    
        local bit pack_client_data_size;
    
            virtual function void do_pack_fcs(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;    
    endfunction
    
            virtual function void do_unpack_fcs(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction
    
            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_WAKE_ON_LAN;
        pack_fcs = 1;
        pack_client_data_size = 1;
    endfunction

        virtual function void set_useful_info_in_client_data();
        if(client_data.size() < get_useful_info_size()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 126); 
   end
;
        end

        begin
            amiq_eth_data temp_data[];
            temp_data = { >> {48'hFFFFFFFFFFFF} };

            for(int i = 0; i < (48 / 8); i++) begin
                int unsigned client_data_index = i + synch_stream_starting_index;
                client_data[client_data_index] = temp_data[i];
            end
        end

        begin
            int target_address_starting_index = synch_stream_starting_index + (48 / 8);
            int target_address_width_in_bytes = ($bits(target_mac) / 8);
            amiq_eth_data temp_data[];
            temp_data = { >> {target_mac} };

            for(int target_mac_index = 0; target_mac_index < 6; target_mac_index++) begin
                for(int byte_index = 0; byte_index < target_address_width_in_bytes; byte_index++) begin
                    int unsigned client_data_index = target_address_starting_index + (target_mac_index * target_address_width_in_bytes) + byte_index;
                    client_data[client_data_index] = temp_data[byte_index];
                end
            end
        end
    endfunction

        virtual function void get_useful_info_from_client_data();
        int unsigned local_synch_stream_starting_index;
        amiq_eth_data local_synch_stream[];
        amiq_eth_address local_target_mac;
        amiq_eth_data local_password[$];
        bit success = 0;

        local_synch_stream = { >> {48'hFFFFFFFFFFFF} };

        begin
            int unsigned client_data_index = 0;
            int synch_stream_index = 0;

            while(client_data_index < client_data.size()) begin
                if(synch_stream_index < (48 / 8)) begin
                    
                    int starting_index = client_data_index;

                    for(synch_stream_index = 0; synch_stream_index < (48 / 8); synch_stream_index++) begin
                        if(client_data[client_data_index] != local_synch_stream[synch_stream_index]) begin
                            client_data_index = starting_index + 1;

                            if(synch_stream_index > 0) begin
                                
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 180); 
   end

                            end

                            synch_stream_index = 0;

                            break;
                        end
                        else begin
                            if(synch_stream_index == 0) begin
                                local_synch_stream_starting_index = client_data_index;
                            end

                            client_data_index++;
                        end
                    end

                    if(synch_stream_index >= (48 / 8)) begin
                        amiq_eth_data target_mac_array[];
                        bit target_mac_byte_mismatch_detected = 0;
                        int unsigned target_mac_bytes_number = $bits(target_mac) / 8;

                        
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 201); 
   end


                        for(int target_mac_index = 0; target_mac_index < target_mac_bytes_number; target_mac_index++) begin
                            target_mac_array = new[target_mac_array.size() + 1] (target_mac_array);
                            target_mac_array[target_mac_array.size() - 1] = client_data[client_data_index];
                            for(int target_mac_repetition_index = 0; target_mac_repetition_index < 6; target_mac_repetition_index++) begin
                                int current_index = client_data_index + ((target_mac_repetition_index * target_mac_bytes_number));

                                if(target_mac_array[target_mac_array.size() - 1] != client_data[current_index]) begin
                                    
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 211); 
   end


                                    target_mac_byte_mismatch_detected = 1;
                                    synch_stream_index = 0;
                                    client_data_index = starting_index + 1;
                                    target_mac_array = new[0];

                                    
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 219); 
   end

                                    break;
                                end
                            end

                            if(target_mac_byte_mismatch_detected == 1) begin
                                break;
                            end
                            else begin
                                client_data_index++;
                            end
                        end

                        if(target_mac_byte_mismatch_detected == 1) begin
                            continue;
                        end
                        else begin
                            client_data_index = client_data_index + (target_mac_bytes_number * (6 - 1));
                            local_target_mac = { >> {target_mac_array}};
                            
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 238); 
   end


                            synch_stream_starting_index = local_synch_stream_starting_index;
                            target_mac = local_target_mac;
                            success = 1;

                            begin
                                int unsigned local_password_size = 0;
                                if(client_data_index < client_data.size() - 6) begin
                                    local_password_size = 6;
                                end
                                else if(client_data_index < client_data.size() - 4) begin
                                    local_password_size = 4;
                                end
                                else begin
                                    break;
                                end

                                begin
                                    password = new[local_password_size];

                                    for(int password_index = 0; password_index < local_password_size; password_index++) begin
                                        password[password_index] = client_data[client_data_index + password_index];
                                    end

                                    break;
                                end

                            end
                        end
                    end
                end
                else begin
                                        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 272); 
   end
;
                end

            end

        end

        if(success != 1) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 280); 
   end
;
        end

    endfunction

            virtual function void do_pack(uvm_packer packer);
        set_useful_info_in_client_data();
        super.do_pack(packer);
        
        if(pack_client_data_size) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end


        end
        
        for(int i = 0; i < client_data_size; i++) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
        if(pack_client_data_size) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
        
        client_data = new[client_data_size];
        for(int i = 0; i < client_data_size; i++) begin
            amiq_eth_data local_data;
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
            client_data[i] = local_data;
        end
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
        
        get_useful_info_from_client_data();

        if(ether_type != AMIQ_ETH_WAKE_ON_LAN) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_magic.sv", 328); 
   end

        end

    endfunction

    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction
    
            virtual function string convert2string();
        string result = super.convert2string();
        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();
        
        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end
        
        result = $sformatf("%s%sStarting Index: %0d", result, ", ", synch_stream_starting_index);
        result = $sformatf("%s%sTarget MAC: %012X", result, ", ", target_mac);
        result = $sformatf("%s%spassword.size(): %0d", result, ", ", password.size());
        result = $sformatf("%s%sclient_data.size(): %0d", result, ", ", client_data.size());
        result = $sformatf("%s%sFCS: %X, %s", result, ", ", fcs, fcs_info);

        return result;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0000);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_magic casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(client_data_size != casted_rhs.client_data_size) begin
            return 0;
        end

        for(int i = 0; i < client_data.size(); i++) begin
            if(client_data[i] != casted_rhs.client_data[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end
        
        if(synch_stream_starting_index != casted_rhs.synch_stream_starting_index) begin
            return 0;
        end

        if(target_mac != casted_rhs.target_mac) begin
            return 0;
        end

        for(int i = 0; i < password.size(); i++) begin
            if(i < casted_rhs.password.size()) begin
                if(client_data[i] != casted_rhs.client_data[i]) begin
                    return 0;
                end
            end
            else begin
                break;
            end
        end

        return 1;
    endfunction

            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_fcs = 0;
        pack_client_data_size = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_fcs = current_pack_fcs;
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_client_data_size = 0;
        
        super.to_wireshark_array(byte_data);
        
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
endclass


/* SLline 42 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_pause.sv" 1 */


        
class amiq_eth_packet_pause extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        protected amiq_eth_pause_opcode pause_opcode;
	
        rand amiq_eth_pause_parameter pause_parameter;
	
        protected amiq_eth_data pad[];
	
        rand amiq_eth_fcs fcs;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        destination_address = 48'h0180C2000001;
        ether_type = AMIQ_ETH_MAC_CONTROL;
        pause_opcode = 16'h0001;
        pad = new[46 - (16 + 16)/ 8];
        foreach (pad[i]) begin
            pad[i] = 0;
        end
        print_lists = 0;
    endfunction

    constraint destination_address_c {
        destination_address == 48'h0180C2000001;
    }

    constraint pause_parameter_c {
        pause_parameter >= 16'h0000;
        pause_parameter <= 16'hFFFF;
    }

    function void post_randomize();
        amiq_eth_address local_source_address;
        local_source_address=48'hFEFFFFFFFFFF;

                source_address = source_address & local_source_address;
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf("%s \n",super.convert2string());
        $sformat(what_to_return, {what_to_return,"pause_opcode: %0d \n"},pause_opcode);
        $sformat(what_to_return, {what_to_return,"pause_parameter: %0d \n"},pause_parameter);
        $sformat(what_to_return, {what_to_return,"pad.size(): %0d \n"},pad.size());
	    if(print_lists == 1) begin
	        foreach (pad[i]) begin
	            $sformat(what_to_return, {what_to_return,"pad[%0d] : %0d \n"},i,pad[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0d \n"},fcs);
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0003);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_pause casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(pause_opcode != casted_rhs.pause_opcode) begin
            return 0;
        end

        if(pause_parameter != casted_rhs.pause_parameter) begin
            return 0;
        end

        for(int i = 0; i < pad.size(); i++) begin
            if(pad[i] != casted_rhs.pad[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

endclass


/* SLline 43 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_pfc_pause.sv" 1 */


        
class amiq_eth_packet_pfc_pause extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        protected amiq_eth_pfc_opcode pfc_opcode;
	
        rand amiq_eth_pfc_class_enable_vector pfc_class_enable_vector;
	
        rand amiq_eth_pfc_parameter pfc_parameters[];
	
        protected amiq_eth_data pad[];
	
        rand amiq_eth_fcs fcs;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        destination_address = 48'h0180C2000001;
        ether_type = AMIQ_ETH_MAC_CONTROL;
        pfc_opcode = 16'h0101;
        pfc_parameters = new[8];
        pad = new[46-(16+16+16*8)/8];
        foreach (pad[i]) begin
            pad[i] = 0;
        end
        print_lists = 0;
    endfunction

    constraint destination_address_c {
        destination_address == 48'h0180C2000001;
    }

    constraint pfc_class_enable_vector_c {
        pfc_class_enable_vector >= 16'h0000;
        pfc_class_enable_vector <= 16'h00FF;
    }

    constraint pfc_parameters_c {
        pfc_parameters.size() == 8;
        foreach(pfc_parameters[i]) {
            pfc_parameters[i] >= 16'h0000;
            pfc_parameters[i] <= 16'hFFFF;
        }
    }
    
    function void post_randomize();
        amiq_eth_address local_source_address;
        local_source_address=48'hFEFFFFFFFFFF;

                source_address = source_address & local_source_address;
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf("%s \n",super.convert2string());
        $sformat(what_to_return, {what_to_return,"pfc_opcode: %0d \n"},pfc_opcode); 
        $sformat(what_to_return, {what_to_return,"pfc_class_enable_vector: %0d \n"},pfc_class_enable_vector); 
        $sformat(what_to_return, {what_to_return,"pfc_parameters.size(): %0d \n"},pfc_parameters.size()); 
	    if(print_lists == 1) begin
	        foreach (pfc_parameters[i]) begin
	            $sformat(what_to_return, {what_to_return,"pfc_parameters[%0d] : %0x \n"},i,pfc_parameters[i]); 
	        end 
	    end
        $sformat(what_to_return, {what_to_return,"pad.size(): %0d \n"},pad.size()); 
	    if(print_lists == 1) begin
	        foreach (pad[i]) begin
	            $sformat(what_to_return, {what_to_return,"pad[%0d] : %0d \n"},i,pad[i]); 
	        end 
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0d \n"},fcs); 
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0004);
        
        return result;
    endfunction
    
                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_pfc_pause casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(pfc_opcode != casted_rhs.pfc_opcode) begin
            return 0;
        end
        
        if(pfc_class_enable_vector != casted_rhs.pfc_class_enable_vector) begin
            return 0;
        end
        
        for(int i = 0; i < pfc_parameters.size(); i++) begin
            if(pfc_parameters[i] != casted_rhs.pfc_parameters[i]) begin
                return 0;
            end
        end

        for(int i = 0; i < pad.size(); i++) begin
            if(pad[i] != casted_rhs.pad[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction
    
endclass


/* SLline 44 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_ethernet_configuration_testing.sv" 1 */


        
class amiq_eth_packet_ethernet_configuration_testing extends amiq_eth_packet_ether_type;
    
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_ethernet_configuration_testing_skipcount skipcount;
    
        rand amiq_eth_ethernet_configuration_testing_function cfg_test_function;
    
        rand int data_size;
    
    rand amiq_eth_data data[];
    
        rand amiq_eth_fcs fcs;

    bit for_wireshark = 0;
	
		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
		print_lists = 0;
        ether_type = AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL;
    endfunction

    function void post_randomize();
        amiq_eth_address local_source_address;
        amiq_eth_ethernet_configuration_testing_skipcount local_skipcount=skipcount;
        amiq_eth_ethernet_configuration_testing_function local_cfg_test_function=cfg_test_function;
        local_source_address=48'hFEFFFFFFFFFF;

                source_address = source_address & local_source_address;

        for(int i = 1 ; i<= 16/8;i++) begin
            for(int j = 0 ; j< 8;j++) begin
                skipcount[16-8*i+j] = local_skipcount[8*(i-1)+j];
            end
        end
        for(int i = 1 ; i<= 16;i++) begin
            for(int j = 0 ; j< 8;j++) begin
                cfg_test_function[16-8*i+j] = local_cfg_test_function[8*(i-1)+j];
            end
        end
        
    endfunction

    constraint data_c {
        solve data_size before data;
        solve data_size before skipcount;
        data_size <= 1496;
        data_size >= 42;
        data.size() == data_size;
        skipcount <= data_size;
    }

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        if ((data_size > 1496) || (data_size < 42)) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ethernet_configuration_testing.sv", 95); 
   end
;
        end
        if (for_wireshark==0) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
            if (data.size() != data_size) begin
                
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ethernet_configuration_testing.sv", 100); 
   end
;
            end
        end
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        if (for_wireshark==0) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
        data = new[data_size];
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf({"%s",", "},super.convert2string());
        $sformat(what_to_return, {what_to_return,"skipcount: %x",", "},skipcount);
        $sformat(what_to_return, {what_to_return,"cfg_test_function: %s",", "},cfg_test_function);
        $sformat(what_to_return, {what_to_return,"data.size(): %0d",", "},data.size());
	    if(print_lists == 1) begin
	        foreach (data[i]) begin
	            $sformat(what_to_return, {what_to_return,"data[%0d] : %0x",", "},i,data[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0x",", "},fcs);
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0006);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ethernet_configuration_testing casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(skipcount != casted_rhs.skipcount) begin
            return 0;
        end

        if(cfg_test_function != casted_rhs.cfg_test_function) begin
            return 0;
        end

        for(int i = 0; i < data.size(); i++) begin
            if(data[i] != casted_rhs.data[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=1;
        super.to_wireshark_array(byte_data);
        for_wireshark=0;
    endfunction

endclass


/* SLline 45 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_hsr_base.sv" 1 */


        
class amiq_eth_packet_hsr_base extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_hsr_path path;
        rand amiq_eth_hsr_size size;
        rand amiq_eth_hsr_seq seq;
    
            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_HSR;        
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf({"%s",", "},super.convert2string());
        $sformat(what_to_return, {what_to_return,"path: %x",", "},path); 
        $sformat(what_to_return, {what_to_return,"size: %x",", "},size); 
        $sformat(what_to_return, {what_to_return,"seq: %x",", "},seq); 
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_hsr_base casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(path != casted_rhs.path) begin
            return 0;
        end
        
        if(size != casted_rhs.size) begin
            return 0;
        end

        if(seq != casted_rhs.seq) begin
            return 0;
        end

        return 1;
    endfunction
    
endclass


/* SLline 46 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_hsr_standard.sv" 1 */


        
class amiq_eth_packet_hsr_standard extends amiq_eth_packet_hsr_base;
    
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_ether_type protocol;
    rand amiq_eth_data lpdu[];
        rand amiq_eth_fcs fcs;

    bit for_wireshark = 0;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
	    print_lists = 0;
    endfunction

    constraint lpdu_c {
        solve lpdu before size;
        lpdu.size() <= 1500;
        lpdu.size() >= 40;
        size == lpdu.size() + (4+12+16+16)/8;
    }

    function void post_randomize();
        amiq_eth_address local_source_address;
        local_source_address=48'hFEFFFFFFFFFF;

                source_address = source_address & local_source_address;
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        amiq_eth_length int_protocol;
        super.do_unpack(packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        if(!$cast(protocol, int_protocol)) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_hsr_standard.sv", 79); 
   end

        end
        lpdu = new[size-(4+12+16+16)/8];
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf({"%s",", "},super.convert2string());
        $sformat(what_to_return, {what_to_return,"protocol: %s",", "},protocol.name());
        $sformat(what_to_return, {what_to_return,"lpdu.size(): %x",", "},lpdu.size());
	    if(print_lists == 1) begin
	        foreach (lpdu[i]) begin
	            $sformat(what_to_return, {what_to_return,"lpdu[%0d] : %0x",", "},i,lpdu[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0x",", "},fcs);
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0008);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_hsr_standard casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        for(int i = 0; i < lpdu.size(); i++) begin
            if(lpdu[i] != casted_rhs.lpdu[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=1;
        super.to_wireshark_array(byte_data);
        for_wireshark=0;
    endfunction

endclass


/* SLline 47 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_ipv4.sv" 1 */


        
class amiq_eth_packet_ipv4_header extends uvm_object;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_ipv4_header_version version;

    constraint version_c {
        version == 4;
    }

        rand amiq_eth_ipv4_header_ihl ihl;

    constraint ihl_c {
        ihl >= ((4 + 4 + 
            6 + 2 + 
            16 + 16 + 
            3 + 13 + 
            8 + 8 + 
            16 + 32 + 
32) 
 / 32) ;
    }

        rand amiq_eth_ipv4_header_dscp dscp;

        rand amiq_eth_ipv4_header_ecn ecn;

        rand amiq_eth_ipv4_header_total_length total_length;

    constraint total_length_c {
        total_length >= (ihl * 4) & total_length <= 576;
    }

        rand amiq_eth_ipv4_header_identification identification;

        rand amiq_eth_ipv4_header_flags flags;

        rand amiq_eth_ipv4_header_fragment_offset fragment_offset;

        rand amiq_eth_ipv4_header_ttl ttl;

        rand amiq_eth_ipv4_header_protocol protocol;

        rand amiq_eth_ipv4_header_checksum checksum;

        rand bit use_correct_checksum;

    constraint use_correct_checksum_c {
        use_correct_checksum == 1;
    }

        rand amiq_eth_ipv4_header_source_ip_address source_ip_address;

        rand amiq_eth_ipv4_header_destination_ip_address destination_ip_address;

        rand amiq_eth_ipv4_header_option options[];
    
    constraint options_c {
        solve  ihl before options;
        options.size() == (ihl - get_minimum_header_length_in_words());
    }

            function new(string name = "");
        super.new(name);
    endfunction

            virtual function int unsigned get_minimum_header_length_in_bits();
        return ((4 + 4 + 
            6 + 2 + 
            16 + 16 + 
            3 + 13 + 
            8 + 8 + 
            16 + 32 + 
32) 
);
    endfunction

            virtual function int unsigned get_minimum_header_length_in_bytes();
        return (get_minimum_header_length_in_bits() / 8);
    endfunction

            virtual function int unsigned get_minimum_header_length_in_words();
        return (get_minimum_header_length_in_bits() / 32);
    endfunction
    
            virtual function int unsigned get_header_length_in_bytes();
        return (ihl * 4);
    endfunction
    
                virtual function int unsigned get_options_size_in_words(amiq_eth_ipv4_header_ihl local_ihl);
        if(local_ihl < get_minimum_header_length_in_words()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 131); 
   end
;
            return 0;
        end
        
        return (local_ihl - get_minimum_header_length_in_words());
    endfunction
    
            virtual function int unsigned get_data_length_in_bytes();
        if(total_length < get_header_length_in_bytes()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 143); 
   end
;    
        end
        
        return (total_length - get_header_length_in_bytes());
    endfunction

            virtual function void do_pack(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
        for (int index = 0; index < options.size(); index++) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;

        begin
            int unsigned minimum_header_length = get_minimum_header_length_in_words();

            if(ihl < get_minimum_header_length_in_words()) begin
                
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 192); 
   end

            end

            options = new[ihl - minimum_header_length];

            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end
    endfunction
    
                local function string get_printable_ip(bit[31:0] address);
        string result = "";
        
        for(int i = 3; i >= 0; i--) begin
            byte unsigned data = (address >> (8 * i)) & 8'hFF;
            result = $sformatf("%s%0d%s", result, data, ((i > 0) ? "." : ""));
        end
        
        return result;
    endfunction

            virtual function string convert2string();
        string source_ip = get_printable_ip(source_ip_address);
        string destination_ip = get_printable_ip(destination_ip_address);
        
        return $sformatf("Version: %X%sIHL: %0d%sDSCP: %X%sECN: %X%sTotal Length: %0d%sIdentification: %X%sFlags: %X%sFragment Offset: %X%sTTL: %0d%sProtocol: %0d%sChecksum: %X%sSource IP: %s%sDestination IP: %s%sOptions size: %0d",
            version, ", ",
            ihl, ", ",
            dscp, ", ",
            ecn, ", ",
            total_length, ", ",
            identification, ", ",
            flags, ", ",
            fragment_offset, ", ",
            ttl, ", ",
            protocol, ", ",
            checksum, ", ",
            source_ip, ", ",
            destination_ip, ", ",
            options.size());
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ipv4_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(ihl != casted_rhs.ihl) begin
            return 0;
        end

        if(dscp != casted_rhs.dscp) begin
            return 0;
        end

        if(ecn != casted_rhs.ecn) begin
            return 0;
        end

        if(total_length != casted_rhs.total_length) begin
            return 0;
        end

        if(identification != casted_rhs.identification) begin
            return 0;
        end

        if(flags != casted_rhs.flags) begin
            return 0;
        end

        if(fragment_offset != casted_rhs.fragment_offset) begin
            return 0;
        end

        if(ttl != casted_rhs.ttl) begin
            return 0;
        end

        if(protocol != casted_rhs.protocol) begin
            return 0;
        end

        if(checksum != casted_rhs.checksum) begin
            return 0;
        end

        if(source_ip_address != casted_rhs.source_ip_address) begin
            return 0;
        end

        if(destination_ip_address != casted_rhs.destination_ip_address) begin
            return 0;
        end

        if(options.size() != casted_rhs.options.size()) begin
            return 0;
        end

        for(int i = 0; i < options.size(); i++) begin
            if(options[i] != casted_rhs.options[i]) begin
                return 0;
            end
        end

        return 1;
    endfunction

            function void copy(uvm_object rhs);
        amiq_eth_packet_ipv4_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 316); 
   end
;
        end

        version = casted_rhs.version;
        ihl = casted_rhs.ihl;
        dscp = casted_rhs.dscp;
        ecn = casted_rhs.ecn;
        total_length = casted_rhs.total_length;
        identification = casted_rhs.identification;
        flags = casted_rhs.flags;
        fragment_offset = casted_rhs.fragment_offset;
        ttl = casted_rhs.ttl;
        protocol = casted_rhs.protocol;
        checksum = casted_rhs.checksum;
        source_ip_address = casted_rhs.source_ip_address;
        destination_ip_address = casted_rhs.destination_ip_address;
        options = new[casted_rhs.options.size()];

        for(int i = 0; i < options.size(); i++) begin
            options[i] = casted_rhs.options[i];
        end

    endfunction

            virtual function amiq_eth_ipv4_header_checksum get_correct_checksum();
                amiq_eth_packet_ipv4_header header;
        bit unsigned bitstream[];
        bit[31:0] halfwords_sum = 0;
        bit[15:0] halfwords[];


        header = amiq_eth_packet_ipv4_header::type_id::create("header");
        header.copy(this);
        header.checksum = 0;

        void'(header.pack(bitstream));

        if(bitstream.size() != ihl * 32) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 357); 
   end
;
        end
        
        halfwords = { >> {bitstream}};

        if(halfwords.size() != (2 * ihl)) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 364); 
   end
;
        end

        for(int i = 0; i < halfwords.size(); i++) begin
            halfwords_sum += halfwords[i];
        end
        
        get_correct_checksum = halfwords_sum[31:16] + halfwords_sum[15:0];
        get_correct_checksum = ~get_correct_checksum;
    endfunction

    function void post_randomize();
        if(use_correct_checksum == 1) begin
            checksum = get_correct_checksum();
        end
    endfunction

endclass

class amiq_eth_packet_ipv4 extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_packet_ipv4_header header;

        rand amiq_eth_data data[];
    
        rand amiq_eth_data pad[];
    
        rand amiq_eth_fcs fcs;
    
        rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

        local bit pack_pad;
    
        local bit pack_fcs;
    
                    virtual function int unsigned get_pad_size_by_fields(int min_frame_size, amiq_eth_packet_ipv4_header header);
        int unsigned value = ((header.total_length + (2 * (48 / 8)) + 6));
        
        if(min_frame_size >= value) begin
            return (min_frame_size - value);    
        end
        else begin
            return 0;
        end
    endfunction
    
            virtual function int unsigned get_pad_size();
        return get_pad_size_by_fields(min_frame_size, header);
    endfunction
    
    constraint pad_c {
        solve header.total_length before pad;
        foreach (pad[i]) { 
            pad[i] == 8'hFF; 
        }
        pad.size() == (min_frame_size - ((header.total_length + (2 * (48 / 8)) + 6)));
    }
    
                virtual function int unsigned get_data_length_in_bytes(amiq_eth_packet_ipv4_header local_header);
        if(local_header.total_length < local_header.get_header_length_in_bytes()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ipv4.sv", 447); 
   end
;    
        end
        
        return (local_header.total_length - local_header.get_header_length_in_bytes());
    endfunction
    
    constraint data_c {
        data.size() == (header.total_length - (header.ihl * 4));
    }

            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_IPV4;
        header = amiq_eth_packet_ipv4_header::type_id::create("header");
        pack_pad = 1;
        pack_fcs = 1;
    endfunction
    
            virtual function void do_pack_data(uvm_packer packer);
        for (int index = 0; index < data.size(); index++) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction
    
            virtual function void do_unpack_data(uvm_packer packer);
        data = new[header.get_data_length_in_bytes()];        
        for (int index = 0; index < data.size(); index++) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
    endfunction
    
            virtual function void do_pack_pad(uvm_packer packer);
        for (int index = 0; index < pad.size(); index++) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction
    
            virtual function void do_unpack_pad(uvm_packer packer);
        int pad_size = get_pad_size();
        
        pad = new[pad_size];        
        for (int index = 0; index < pad_size; index++) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
    endfunction
    
            virtual function void do_pack_fcs(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;    
    endfunction
    
            virtual function void do_unpack_fcs(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction
    
            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        header.do_pack(packer);
        do_pack_data(packer);
        
        if(pack_pad) begin
            do_pack_pad(packer);
        end
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        header.do_unpack(packer);
        do_unpack_data(packer);
        
        if(pack_pad) begin
            do_unpack_pad(packer);
        end
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
    endfunction

            virtual function string convert2string();
        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();
        
        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end
        
        return $sformatf("%s%s%s%sdata size: %0d%spad.size(): %0d%sFCS: %0X - %s",
            super.convert2string(), ", ",
            header.convert2string(), ", ",
            data.size(), ", ",
            pad.size(), ", ",
            fcs, fcs_info);
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ipv4 casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if(header.compare(casted_rhs.header, comparer) == 0) begin
            return 0;
        end

        if(data.size() != casted_rhs.data.size()) begin
            return 0;
        end

        for(int i = 0; i < data.size(); i++) begin
            if(data[i] != casted_rhs.data[i]) begin
                return 0;
            end
        end

        if(pad.size() != casted_rhs.pad.size()) begin
            return 0;
        end

        for(int i = 0; i < pad.size(); i++) begin
            if(pad[i] != casted_rhs.pad[i]) begin
                return 0;
            end
        end

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end
        
        return 1;
    endfunction
    
            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0007);
        
        return result;
    endfunction
    
    function void post_randomize();
                        header.post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction
    
            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_pad = pack_pad;
        bit current_pack_fcs = pack_fcs;
        
        pack_pad = 0;
        pack_fcs = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_pad = current_pack_pad;
        pack_fcs = current_pack_fcs;
    endfunction
    
endclass


/* SLline 48 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_fcoe.sv" 1 */


        
class amiq_eth_packet_fcoe extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_fcoe_version version;
        protected bit fcoe_reserved_before_sof[];
        rand amiq_eth_fcoe_sof sof;
        rand int unsigned fc_frame_size;
    rand amiq_eth_data fc_frame[];
        rand amiq_eth_fcoe_eof eof;
        protected bit fcoe_reserved_after_eof[];
        rand amiq_eth_fcs fcs;

    local bit pack_version;

    local bit pack_rsvd_b_sof;

    local bit pack_sof;

    local bit pack_frame;

    local bit pack_eof;

    local bit pack_rsvd_a_eof;

    local bit pack_fcs;

    bit for_wireshark = 0;
    
    local bit to_compute_crc = 0;

        rand bit use_correct_fcs;
    
    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_FCOE;
        fcoe_reserved_before_sof = new[100];
        foreach (fcoe_reserved_before_sof[i]) begin
            fcoe_reserved_before_sof[i] = 0;
        end
        fcoe_reserved_after_eof = new[24];
        foreach (fcoe_reserved_after_eof[i]) begin
            fcoe_reserved_after_eof[i] = 0;
        end
        pack_version = 1;
        pack_rsvd_b_sof = 1;
        pack_sof = 1;
        pack_frame = 1;
        pack_eof = 1;
        pack_rsvd_a_eof = 1;
        pack_fcs = 0;
        print_lists = 0;
    endfunction

    function void post_randomize();
        byte unsigned byte_data [];
        
        amiq_eth_address local_source_address;
        local_source_address=48'hFEFFFFFFFFFF;
        
                source_address = source_address & local_source_address;

        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
        
        byte_data = {>> {get_correct_crc()}};
        byte_data.reverse();
        for(int i = 0;i<byte_data.size();i++) begin
            fc_frame[fc_frame.size()-1-i] = byte_data[i];
        end 
    endfunction

    constraint fc_frame_c {
        solve fc_frame_size before fc_frame;
        fc_frame_size >= 28;
        fc_frame_size <= 2180;
        fc_frame_size%4 == 0;
        fc_frame.size() == fc_frame_size;
    }
    
	                                    virtual function void pack_fcoe_with_options(uvm_packer packer, bit local_pack_version, bit local_pack_rsvd_b_sof, bit local_pack_sof, bit local_pack_frame, bit local_pack_eof, bit local_pack_rsvd_a_eof, bit local_pack_fcs);
        if (local_pack_version) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_rsvd_b_sof) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_sof) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end

        if (local_pack_frame) begin
            if (for_wireshark==0) begin
                
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
            end
            if (to_compute_crc) begin
                amiq_eth_data fc_frame_l[];
                fc_frame_l = new[fc_frame.size()-4];
                foreach (fc_frame_l[i]) begin
                    fc_frame_l[i] = fc_frame[i];
                end
                
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
            end else begin
                
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
            end
        end

        if (local_pack_eof) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end

        if (local_pack_rsvd_a_eof) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_fcs) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction


            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_fcoe_with_options(packer, pack_version, pack_rsvd_b_sof, pack_sof, pack_frame, pack_eof, pack_rsvd_a_eof, pack_fcs);
    endfunction

	                                    virtual function void unpack_fcoe_with_options(uvm_packer packer, bit local_pack_version, bit local_pack_rsvd_b_sof, bit local_pack_sof, bit local_pack_frame, bit local_pack_eof, bit local_pack_rsvd_a_eof, bit local_pack_fcs);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        if (for_wireshark==0) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
        fc_frame = new[fc_frame_size];
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        if (local_pack_fcs) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end 
    endfunction
    
            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_fcoe_with_options(packer, pack_version, pack_rsvd_b_sof, pack_sof, pack_frame, pack_eof, pack_rsvd_a_eof, pack_fcs);
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf({"%s",", "},super.convert2string());
        $sformat(what_to_return, {what_to_return,"version: %x",", "},version);
        $sformat(what_to_return, {what_to_return,"fcoe_reserved_before_sof.size(): %x",", "},fcoe_reserved_before_sof.size());
	    if(print_lists == 1) begin
	        foreach (fcoe_reserved_before_sof[i]) begin
	            $sformat(what_to_return, {what_to_return,"fcoe_reserved_before_sof[%0d] : %x  "},i,fcoe_reserved_before_sof[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"sof: %s",", "},sof.name());
        $sformat(what_to_return, {what_to_return,"fc_frame_size: %x",", "},fc_frame_size);
	    if(print_lists == 1) begin
	        foreach (fc_frame[i]) begin
	            $sformat(what_to_return, {what_to_return,"fc_frame[%0d] : %x ",", "},i,fc_frame[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"eof: %s",", "},eof.name());
        $sformat(what_to_return, {what_to_return,"fcoe_reserved_after_eof.size(): %x",", "},fcoe_reserved_after_eof.size());
	    if(print_lists == 1) begin
	        foreach (fcoe_reserved_after_eof[i]) begin
	            $sformat(what_to_return, {what_to_return,"fcoe_reserved_after_eof[%0d] : %x  "},i,fcoe_reserved_after_eof[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"fcs: %0x",", "},fcs);
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_000A);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_fcoe casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(version != casted_rhs.version) begin
            return 0;
        end

        for(int i = 0; i < fcoe_reserved_before_sof.size(); i++) begin
            if(fcoe_reserved_before_sof[i] != casted_rhs.fcoe_reserved_before_sof[i]) begin
                return 0;
            end
        end

        if(sof != casted_rhs.sof) begin
            return 0;
        end

        for(int i = 0; i < fc_frame.size(); i++) begin
            if(fc_frame[i] != casted_rhs.fc_frame[i]) begin
                return 0;
            end
        end

        if(eof != casted_rhs.eof) begin
            return 0;
        end

        for(int i = 0; i < fcoe_reserved_after_eof.size(); i++) begin
            if(fcoe_reserved_after_eof[i] != casted_rhs.fcoe_reserved_after_eof[i]) begin
                return 0;
            end
        end

        if((fcs != casted_rhs.fcs) & (pack_fcs)) begin
            return 0;
        end

        return 1;
    endfunction

            virtual function int unsigned get_correct_crc();
        bit bitstream[];
        byte unsigned byte_data [];
        bit curent_to_compute_crc = to_compute_crc;
        to_compute_crc=1;
        pack_for_crc(bitstream);
        to_compute_crc=curent_to_compute_crc;
        byte_data = {>> {bitstream}};
        
        get_correct_crc = get_crc32_802(byte_data);
    endfunction

            virtual function void pack_for_crc(ref bit bitstream[]);
        bit current_pack_preamble = get_pack_preamble();
        bit current_pack_sfd = get_pack_sfd();
        bit current_pack_destination_address = get_pack_destination_address();
        bit current_pack_source_address = get_pack_source_address();
        bit curent_pack_ether_type = get_pack_ether_type();
        bit curent_pack_version = pack_version;
        bit curent_pack_rsvd_b_sof = pack_rsvd_b_sof;
        bit curent_pack_sof = pack_sof;
        bit curent_pack_eof = pack_eof;
        bit curent_pack_rsvd_a_eof = pack_rsvd_a_eof;
        bit curent_pack_fcs = pack_fcs;

        set_pack_preamble(0);
        set_pack_sfd(0);
        set_pack_destination_address(0);
        set_pack_source_address(0);
        set_pack_ether_type(0);
        pack_version = 0;
        pack_rsvd_b_sof = 0;
        pack_sof = 0;
        for_wireshark=1;
        pack_eof = 0;
        pack_rsvd_a_eof = 0;
        pack_fcs = 0;

        void'(pack(bitstream));

        set_pack_preamble(current_pack_preamble);
        set_pack_sfd(current_pack_sfd);
        set_pack_ether_type(curent_pack_ether_type);
        set_pack_destination_address(current_pack_destination_address);
        set_pack_source_address(current_pack_source_address);
        pack_version = curent_pack_version;
        pack_rsvd_b_sof = curent_pack_rsvd_b_sof;
        pack_sof = curent_pack_sof;
        pack_eof = curent_pack_eof;
        pack_rsvd_a_eof = curent_pack_rsvd_a_eof;
        pack_fcs = curent_pack_fcs;
        for_wireshark=0;
    endfunction

            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;

        pack_fcs = 0;

        super.pack_for_fcs(bitstream);

        pack_fcs = current_pack_fcs;
    endfunction

            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=1;
        super.to_wireshark_array(byte_data);
        for_wireshark=0;
    endfunction

endclass


/* SLline 49 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_arp.sv" 1 */


        
class amiq_eth_packet_arp extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_arp_htype htype;
    
        rand amiq_eth_arp_ptype ptype;
    
        rand amiq_eth_arp_hlen hlen;
    
        rand amiq_eth_arp_plen plen;
    
        rand amiq_eth_arp_oper oper;
    
    constraint oper_c {
        oper inside {1, 2};
    }
    
                    rand amiq_eth_arp_sha sha;
    
        rand amiq_eth_arp_spa spa;
    
                rand amiq_eth_arp_tha tha;
    
        rand amiq_eth_arp_tpa tpa;
    
        rand amiq_eth_fcs fcs;
    
        rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }
    
    constraint ethernet_ipv4_c {
        htype == 1;
        ptype == 16'h0800;
        hlen == 6;
        plen == 4;
    }

        local bit pack_fcs;
    
            function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_ARP;
        pack_fcs = 1;
    endfunction
    
            virtual function void do_pack_fcs(uvm_packer packer);
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;    
    endfunction
    
            virtual function void do_unpack_fcs(uvm_packer packer);
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
    endfunction
    
            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;    
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;    
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
    endfunction

            virtual function string convert2string();
        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();
        
        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end
        
        return $sformatf("%s%sHTYPE: %X%sPTYPE: %X%sHLEN: %X%sPLEN: %X%sOPER: %X%sSHA: %X%sSPA: %X%sTHA: %X%sTPA: %X%sFCS: %0X - %s",
            super.convert2string(), ", ",
            htype, ", ",
            ptype, ", ",
            hlen, ", ",
            plen, ", ",
            oper, ", ",
            sha, ", ",
            spa, ", ",
            tha, ", ",
            tpa, ", ",
            fcs, fcs_info);
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_arp casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end
        
        if(htype != casted_rhs.htype) begin
            return 0;
        end
        
        if(ptype != casted_rhs.ptype) begin
            return 0;
        end
        
        if(hlen != casted_rhs.hlen) begin
            return 0;
        end
        
        if(plen != casted_rhs.plen) begin
            return 0;
        end
        
        if(oper != casted_rhs.oper) begin
            return 0;
        end
        
        if(sha != casted_rhs.sha) begin
            return 0;
        end
        
        if(spa != casted_rhs.spa) begin
            return 0;
        end
        
        if(tha != casted_rhs.tha) begin
            return 0;
        end
        
        if(tpa != casted_rhs.tpa) begin
            return 0;
        end
        
        if(fcs != casted_rhs.fcs) begin
            return 0;
        end
        
        return 1;
    endfunction
    
            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_0009);
        
        return result;
    endfunction
    
    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction
    
            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;
        
        pack_fcs = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_fcs = current_pack_fcs;
    endfunction
    
endclass


/* SLline 50 "./sv/amiq_eth_pkg.sv" 2 */
	/* SLline 1 "./sv/amiq_eth_packet_ptp.sv" 1 */


        
class amiq_eth_packet_ptp_header extends uvm_object;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



        rand amiq_eth_ptp_transport_specific transport_specific;
    local bit pack_transport_specific;

    rand amiq_eth_ptp_message_type message_type;
    local bit pack_message_type;

    protected bit ptp_reserved_1[];
    local bit pack_ptp_reserved_1;

    rand amiq_eth_ptp_version version;
    local bit pack_version;

    rand amiq_eth_ptp_message_length message_length;
    local bit pack_message_length;

    rand amiq_eth_ptp_domain_number domain_number;
    local bit pack_domain_number;

    protected bit ptp_reserved_2[];
    local bit pack_ptp_reserved_2;

    rand amiq_eth_ptp_flags flags;
    local bit pack_flags;

    rand amiq_eth_ptp_correction_field correction_field;
    local bit pack_correction_field;

    protected bit ptp_reserved_3[];
    local bit pack_ptp_reserved_3;

    rand byte source_port_identity[];
    local bit pack_source_port_identity;

    rand amiq_eth_ptp_sequence_id sequence_id;
    local bit pack_sequence_id;

    rand amiq_eth_ptp_control_field_type control_field;
    local bit pack_control_field;

    rand amiq_eth_ptp_log_message log_message;
    local bit pack_log_message;
    
    constraint message_type_c {
        message_type == PTP_Delay_ReqMessage;
    }

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        pack_transport_specific = 1;
        pack_message_type = 1;
        pack_ptp_reserved_1 = 1;
        pack_version = 1;
        pack_message_length = 1;
        pack_domain_number = 1;
        pack_ptp_reserved_2 = 1;
        pack_flags = 1;
        pack_correction_field = 1;
        pack_ptp_reserved_3 = 1;
        pack_source_port_identity = 1;
        pack_sequence_id = 1;
        pack_control_field = 1;
        pack_log_message = 1;
        source_port_identity = new[10];
        ptp_reserved_1 = new[4];
        foreach (ptp_reserved_1[i]) begin
            ptp_reserved_1[i] = 0;
        end
        ptp_reserved_2 = new[8];
        foreach (ptp_reserved_2[i]) begin
            ptp_reserved_2[i] = 0;
        end
        ptp_reserved_3 = new[32];
        foreach (ptp_reserved_3[i]) begin
            ptp_reserved_3[i] = 0;
        end
        print_lists = 0;
    endfunction

	                                                                virtual function void pack_ptp_header_with_options(uvm_packer packer,
            bit local_pack_transport_specific,
            bit local_pack_message_type,
            bit local_pack_ptp_reserved_1,
            bit local_pack_version,
            bit local_pack_message_length,
            bit local_pack_domain_number,
            bit local_pack_ptp_reserved_2,
            bit local_pack_flags,
            bit local_pack_correction_field,
            bit local_pack_ptp_reserved_3,
            bit local_pack_source_port_identity,
            bit local_pack_sequence_id,
            bit local_pack_control_field,
            bit local_pack_log_message);

        if (local_pack_transport_specific) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end

        if (local_pack_message_type) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end

        if (local_pack_ptp_reserved_1) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_version) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_message_length) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_domain_number) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_ptp_reserved_2) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_flags) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_correction_field) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_ptp_reserved_3) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_source_port_identity) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_sequence_id) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_control_field) begin
            
   
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(ether_type)-1:0] __vector = ether_type; 
     { << int { __array }} = {{($bits(int) - ($bits(ether_type) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(ether_type)); 
  end


;
        end

        if (local_pack_log_message) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_header_with_options(packer, pack_transport_specific, pack_message_type, pack_ptp_reserved_1, pack_version, pack_message_length, pack_domain_number, pack_ptp_reserved_2, pack_flags, pack_correction_field, pack_ptp_reserved_3, pack_source_port_identity, pack_sequence_id, pack_control_field, pack_log_message);
    endfunction

	                                                                virtual function void  unpack_ptp_header_with_options(uvm_packer packer,
            bit local_pack_transport_specific,
            bit local_pack_message_type,
            bit local_pack_ptp_reserved_1,
            bit local_pack_version,
            bit local_pack_message_length,
            bit local_pack_domain_number,
            bit local_pack_ptp_reserved_2,
            bit local_pack_flags,
            bit local_pack_correction_field,
            bit local_pack_ptp_reserved_3,
            bit local_pack_source_port_identity,
            bit local_pack_sequence_id,
            bit local_pack_control_field,
            bit local_pack_log_message);

        if (local_pack_transport_specific) begin
            
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        end

        if (local_pack_message_type) begin
            
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        end

        if (local_pack_ptp_reserved_1) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_version) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_message_length) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_domain_number) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_ptp_reserved_2) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_flags) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_correction_field) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_ptp_reserved_3) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_source_port_identity) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_sequence_id) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_control_field) begin
            
   
   begin 
   if (packer.big_endian) 
     { << { cfg_test_function }} = packer.m_bits[packer.count +: $bits(cfg_test_function)];  
   else 
     cfg_test_function = amiq_eth_ethernet_configuration_testing_function'(packer.m_bits[packer.count +: $bits(cfg_test_function)]); 
   
   packer.count += $bits(cfg_test_function); 
   end

;
        end

        if (local_pack_log_message) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_header_with_options(packer, pack_transport_specific, pack_message_type, pack_ptp_reserved_1, pack_version, pack_message_length, pack_domain_number, pack_ptp_reserved_2, pack_flags, pack_correction_field, pack_ptp_reserved_3, pack_source_port_identity, pack_sequence_id, pack_control_field, pack_log_message);
    endfunction

            virtual function string convert2string();
        string what_to_return = " HEADER : \n";
        $sformat(what_to_return, {what_to_return,"transport_specific: %s",", "},transport_specific.name());
        $sformat(what_to_return, {what_to_return,"message_type: %s",", "},message_type.name());
        $sformat(what_to_return, {what_to_return,"ptp_reserved_1.size(): %x",", "},ptp_reserved_1.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_1[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_1[%0d] : %x  "},i,ptp_reserved_1[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"version: %x",", "},version);
        $sformat(what_to_return, {what_to_return,"message_length: %x",", "},message_length);
        $sformat(what_to_return, {what_to_return,"domain_number: %x",", "},domain_number);
        $sformat(what_to_return, {what_to_return,"ptp_reserved_2.size(): %x",", "},ptp_reserved_2.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_2[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_2[%0d] : %x  "},i,ptp_reserved_2[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"flags: %x",", "},flags);
        $sformat(what_to_return, {what_to_return,"correction_field: %x",", "},correction_field);
        $sformat(what_to_return, {what_to_return,"ptp_reserved_3.size(): %x",", "},ptp_reserved_3.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_3[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_3[%0d] : %x  "},i,ptp_reserved_3[i]);
	        end        
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"source_port_identity.size(): %x",", "},source_port_identity.size());
        foreach (source_port_identity[i]) begin
            $sformat(what_to_return, {what_to_return,"source_port_identity[%0d] : %x  "},i,source_port_identity[i]);
        end 
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"sequence_id: %0x",", "},sequence_id);
        $sformat(what_to_return, {what_to_return,"control_field: %s",", "},control_field.name());
        $sformat(what_to_return, {what_to_return,"log_message: %0x",", "},log_message);
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(transport_specific != casted_rhs.transport_specific) begin
            return 0;
        end

        if(message_type != casted_rhs.message_type) begin
            return 0;
        end

        for(int i = 0; i < ptp_reserved_1.size(); i++) begin
            if(ptp_reserved_1[i] != casted_rhs.ptp_reserved_1[i]) begin
                return 0;
            end
        end

        if(version != casted_rhs.version) begin
            return 0;
        end

        if(message_length != casted_rhs.message_length) begin
            return 0;
        end

        if(domain_number != casted_rhs.domain_number) begin
            return 0;
        end

        for(int i = 0; i < ptp_reserved_2.size(); i++) begin
            if(ptp_reserved_2[i] != casted_rhs.ptp_reserved_2[i]) begin
                return 0;
            end
        end

        if(flags != casted_rhs.flags) begin
            return 0;
        end

        if(correction_field != casted_rhs.correction_field) begin
            return 0;
        end

        for(int i = 0; i < ptp_reserved_3.size(); i++) begin
            if(ptp_reserved_3[i] != casted_rhs.ptp_reserved_3[i]) begin
                return 0;
            end
        end
        
        for(int i = 0; i < source_port_identity.size(); i++) begin
            if(source_port_identity[i] != casted_rhs.source_port_identity[i]) begin
                return 0;
            end
        end

        if(sequence_id != casted_rhs.sequence_id) begin
            return 0;
        end

        if(control_field != casted_rhs.control_field) begin
            return 0;
        end

        if(log_message != casted_rhs.log_message) begin
            return 0;
        end

        return 1;
    endfunction

            function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 432); 
   end
;
        end

        transport_specific = casted_rhs.transport_specific;
        message_type = casted_rhs.message_type;

        for(int i = 0; i < ptp_reserved_1.size(); i++) begin
            ptp_reserved_1[i] = casted_rhs.ptp_reserved_1[i];
        end

        version = casted_rhs.version;
        message_length = casted_rhs.message_length;
        domain_number = casted_rhs.domain_number;

        for(int i = 0; i < ptp_reserved_2.size(); i++) begin
            ptp_reserved_2[i] = casted_rhs.ptp_reserved_2[i];
        end

        flags = casted_rhs.flags;
        correction_field = casted_rhs.correction_field;

        for(int i = 0; i < ptp_reserved_3.size(); i++) begin
            ptp_reserved_3[i] = casted_rhs.ptp_reserved_3[i];
        end

        for(int i = 0; i < source_port_identity.size(); i++) begin
            source_port_identity[i] = casted_rhs.source_port_identity[i];
        end
        
        sequence_id = casted_rhs.sequence_id;
        control_field = casted_rhs.control_field;
        log_message = casted_rhs.log_message;

    endfunction

    virtual function int header_size_in_bytes();
        bit bitstream[];
        byte unsigned byte_data [];

        void'(pack(bitstream));

        byte_data = {>> {bitstream}};

        return byte_data.size();
    endfunction

endclass

class amiq_eth_packet_ptp_body extends uvm_object;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



            function new(string name = "");
        super.new(name);
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
    endfunction

            virtual function string convert2string();
        string what_to_return = " BODY : \n";
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        return 1;
    endfunction

            function void copy(uvm_object rhs);
    endfunction

            virtual function int body_size_in_bytes();
        bit bitstream[];
        byte unsigned byte_data [];

        void'(pack(bitstream));

        byte_data = {>> {bitstream}};

        return byte_data.size();
    endfunction

endclass

class amiq_eth_packet_ptp_announce_message extends amiq_eth_packet_ptp_body;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



    rand byte origin_timestamp[];
    local bit pack_origin_timestamp;

    rand amiq_eth_ptp_announce_message_current_utc_offset current_utc_offset;
    local bit pack_current_utc_offset;

    protected bit ptp_announce_message_reserved[];
    local bit pack_reserved;

    rand amiq_eth_ptp_announce_message_grandmaster_priority_1 grandmaster_priority_1;
    local bit pack_grandmaster_priority_1;

    rand amiq_eth_ptp_announce_message_grandmaster_clock_quality grandmaster_clock_quality;
    local bit pack_grandmaster_clock_quality;

    rand amiq_eth_ptp_announce_message_grandmaster_priority_2 grandmaster_priority_2;
    local bit pack_grandmaster_priority_2;

    rand amiq_eth_ptp_announce_message_grandmaster_identity grandmaster_identity;
    local bit pack_grandmaster_identity;

    rand amiq_eth_ptp_announce_message_steps_removed steps_removed;
    local bit pack_steps_removed;

    rand amiq_eth_ptp_announce_message_time_source time_source;
    local bit pack_time_source;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        ptp_announce_message_reserved = new[8];
        origin_timestamp = new[10];
        foreach (ptp_announce_message_reserved[i]) begin
            ptp_announce_message_reserved[i] = 0;
        end
        pack_origin_timestamp = 1;
        pack_current_utc_offset = 1;
        pack_reserved = 1;
        pack_grandmaster_priority_1 = 1;
        pack_grandmaster_clock_quality = 1;
        pack_grandmaster_priority_2 = 1;
        pack_grandmaster_identity = 1;
        pack_steps_removed = 1;
        pack_time_source = 1;
		print_lists = 0;
    endfunction

	                                            virtual function void pack_ptp_announce_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp,
            bit local_pack_current_utc_offset,
            bit local_pack_reserved,
            bit local_pack_grandmaster_priority_1,
            bit local_pack_grandmaster_clock_quality,
            bit local_pack_grandmaster_priority_2,
            bit local_pack_grandmaster_identity,
            bit local_pack_steps_removed,
            bit local_pack_time_source);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_current_utc_offset) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_reserved) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end

        if (local_pack_grandmaster_priority_1) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_grandmaster_clock_quality) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_grandmaster_priority_2) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_grandmaster_identity) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_steps_removed) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end

        if (local_pack_time_source) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_announce_message_with_options(packer,pack_origin_timestamp,pack_current_utc_offset,pack_reserved,pack_grandmaster_priority_1,pack_grandmaster_clock_quality,pack_grandmaster_priority_2,pack_grandmaster_identity,pack_steps_removed,pack_time_source);
    endfunction

	                                            virtual function void  unpack_ptp_announce_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp,
            bit local_pack_current_utc_offset,
            bit local_pack_reserved,
            bit local_pack_grandmaster_priority_1,
            bit local_pack_grandmaster_clock_quality,
            bit local_pack_grandmaster_priority_2,
            bit local_pack_grandmaster_identity,
            bit local_pack_steps_removed,
            bit local_pack_time_source);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_current_utc_offset) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_reserved) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end

        if (local_pack_grandmaster_priority_1) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_grandmaster_clock_quality) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_grandmaster_priority_2) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_grandmaster_identity) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_steps_removed) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end

        if (local_pack_time_source) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_announce_message_with_options(packer,pack_origin_timestamp,pack_current_utc_offset,pack_reserved,pack_grandmaster_priority_1,pack_grandmaster_clock_quality,pack_grandmaster_priority_2,pack_grandmaster_identity,pack_steps_removed,pack_time_source);
    endfunction

            virtual function string convert2string();
        string what_to_return = " ANNOUNCE MESSAGE : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",", "},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"current_utc_offset: %x",", "},current_utc_offset);
        $sformat(what_to_return, {what_to_return,"ptp_announce_message_reserved.size(): %x",", "},ptp_announce_message_reserved.size());
	    if(print_lists == 1) begin
	        foreach (ptp_announce_message_reserved[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_announce_message_reserved[%0d] : %x  "},i,ptp_announce_message_reserved[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,", "});
        $sformat(what_to_return, {what_to_return,"grandmaster_priority_1: %x",", "},grandmaster_priority_1);
        $sformat(what_to_return, {what_to_return,"grandmaster_clock_quality: %x",", "},grandmaster_clock_quality);
        $sformat(what_to_return, {what_to_return,"grandmaster_priority_2: %x",", "},grandmaster_priority_2);
        $sformat(what_to_return, {what_to_return,"grandmaster_identity: %x",", "},grandmaster_identity);
        $sformat(what_to_return, {what_to_return,"steps_removed: %x",", "},steps_removed);
        $sformat(what_to_return, {what_to_return,"time_source: %0x",", "},time_source);
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_announce_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 760); 
   end
;
        end
       
        for(int i = 0; i < origin_timestamp.size(); i++) begin
            if(origin_timestamp[i] != casted_rhs.origin_timestamp[i]) begin
                return 0;
            end
        end
        
        if(current_utc_offset != casted_rhs.current_utc_offset) begin
            return 0;
        end

        for(int i = 0; i < ptp_announce_message_reserved.size(); i++) begin
            if(ptp_announce_message_reserved[i] != casted_rhs.ptp_announce_message_reserved[i]) begin
                return 0;
            end
        end

        if(grandmaster_priority_1 != casted_rhs.grandmaster_priority_1) begin
            return 0;
        end

        if(grandmaster_clock_quality != casted_rhs.grandmaster_clock_quality) begin
            return 0;
        end

        if(grandmaster_priority_2 != casted_rhs.grandmaster_priority_2) begin
            return 0;
        end

        if(grandmaster_identity != casted_rhs.grandmaster_identity) begin
            return 0;
        end

        if(steps_removed != casted_rhs.steps_removed) begin
            return 0;
        end

        if(time_source != casted_rhs.time_source) begin
            return 0;
        end

        return 1;
    endfunction

            function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_announce_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 812); 
   end
;
        end

        for(int i = 0; i < origin_timestamp.size(); i++) begin
            origin_timestamp[i] = casted_rhs.origin_timestamp[i];
        end
        
        current_utc_offset = casted_rhs.current_utc_offset;

        for(int i = 0; i < ptp_announce_message_reserved.size(); i++) begin
            ptp_announce_message_reserved[i] = casted_rhs.ptp_announce_message_reserved[i];
        end

        grandmaster_priority_1 = casted_rhs.grandmaster_priority_1;
        grandmaster_clock_quality = casted_rhs.grandmaster_clock_quality;
        grandmaster_priority_2 = casted_rhs.grandmaster_priority_2;
        grandmaster_identity = casted_rhs.grandmaster_identity;
        steps_removed = casted_rhs.steps_removed;
        time_source = casted_rhs.time_source;
    endfunction
endclass

class amiq_eth_packet_ptp_sync_message extends amiq_eth_packet_ptp_body;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



    rand byte origin_timestamp[];
    local bit pack_origin_timestamp;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        origin_timestamp = new[10];
        pack_origin_timestamp = 1;
	    print_lists = 0;   
    endfunction

	            virtual function void pack_ptp_sync_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end
        
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_sync_message_with_options(packer,pack_origin_timestamp);
    endfunction

	            virtual function void  unpack_ptp_sync_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end
        
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_sync_message_with_options(packer,pack_origin_timestamp);
    endfunction

            virtual function string convert2string();
        string what_to_return = " SYNC MESSAGE : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",", "},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,", "});
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_sync_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 913); 
   end
;
        end
       
        for(int i = 0; i < origin_timestamp.size(); i++) begin
            if(origin_timestamp[i] != casted_rhs.origin_timestamp[i]) begin
                return 0;
            end
        end
        
        return 1;
    endfunction

            function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_sync_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 931); 
   end
;
        end

        for(int i = 0; i < origin_timestamp.size(); i++) begin
            origin_timestamp[i] = casted_rhs.origin_timestamp[i];
        end        
        
    endfunction

endclass

class amiq_eth_packet_ptp_delay_req_message extends amiq_eth_packet_ptp_body;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



    rand byte origin_timestamp[];
    local bit pack_origin_timestamp;

		bit print_lists = 0;

            function new(string name = "");
        super.new(name);
        origin_timestamp = new[10];
        pack_origin_timestamp = 1;
	    print_lists = 0;      
    endfunction

	            virtual function void   pack_ptp_delay_req_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    if (packer.use_metadata) 
      
  begin 
   int __array[]; 
   begin 
     bit [32-1:0] __vector = client_data.size(); 
     { << int { __array }} = {{($bits(int) - (32 % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, 32); 
  end
 
    
    begin 
    foreach (client_data [index]) 
      
  begin 
   int __array[]; 
   begin 
     bit [$bits(client_data[0])-1:0] __vector = client_data[index]; 
     { << int { __array }} = {{($bits(int) - ($bits(client_data[0]) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(client_data[0])); 
  end
 
    end
 
    end

;
        end
        
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_delay_req_message_with_options(packer,pack_origin_timestamp);
    endfunction

	            virtual function void  unpack_ptp_delay_req_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            
   
    begin 
    int sz__; 
    if (packer.use_metadata) begin 
      
   begin 
      int __array[] = new[(32+31)/32]; 
      bit [(((32 + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, 32); 
      __var = { << int { __array }}; 
      sz__ = __var; 
   end
 
      protocol_data = new[sz__]; 
    end 
    
    begin 
    foreach (protocol_data [i]) 
      
   begin 
      int __array[] = new[($bits(protocol_data[0])+31)/32]; 
      bit [((($bits(protocol_data[0]) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(protocol_data[0])); 
      __var = { << int { __array }}; 
      protocol_data[i] = __var; 
   end
 
    end
 
    end

;
        end
        
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_delay_req_message_with_options(packer,pack_origin_timestamp);
    endfunction

            virtual function string convert2string();
        string what_to_return = " DELAY REQ : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",", "},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,", "});
        return what_to_return;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_delay_req_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1021); 
   end
;
        end
       
        for(int i = 0; i < origin_timestamp.size(); i++) begin
            if(origin_timestamp[i] != casted_rhs.origin_timestamp[i]) begin
                return 0;
            end
        end
        
        return 1;
    endfunction

            function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_delay_req_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1039); 
   end
;
        end

        for(int i = 0; i < origin_timestamp.size(); i++) begin
            origin_timestamp[i] = casted_rhs.origin_timestamp[i];
        end        
        
    endfunction

endclass

class amiq_eth_packet_ptp extends amiq_eth_packet_ether_type;
    
  
   
   typedef uvm_object_registry#(amiq_eth_packet_length,"amiq_eth_packet_length") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     amiq_eth_packet_length tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "amiq_eth_packet_length"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     amiq_eth_packet_length local_data__; /* Used for copy and compare */ 
     typedef amiq_eth_packet_length ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



    rand amiq_eth_packet_ptp_header header;
    local bit pack_header;

    rand amiq_eth_packet_ptp_announce_message announce_message_body;
    rand amiq_eth_packet_ptp_sync_message sync_message_body;
    rand amiq_eth_packet_ptp_delay_req_message delay_req_message_body;
    local bit pack_body;

    rand amiq_eth_fcs fcs;
    local bit pack_fcs;

    rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }
    
    local bit for_wireshark;

            function new(string name = "");
        super.new(name);
        header = amiq_eth_packet_ptp_header::type_id::create("header");
        announce_message_body = amiq_eth_packet_ptp_announce_message::type_id::create("announce_message_body");
        sync_message_body = amiq_eth_packet_ptp_sync_message::type_id::create("sync_message_body");
        delay_req_message_body = amiq_eth_packet_ptp_delay_req_message::type_id::create("delay_req_message_body");
        ether_type = AMIQ_ETH_PTP;
        pack_header = 1;
        pack_body = 1;
        pack_fcs = 1;
        for_wireshark = 1;
    endfunction

    function void post_randomize();
        amiq_eth_address local_source_address;
        local_source_address=48'hFEFFFFFFFFFF;

                source_address = source_address & local_source_address;

        case (header.message_type)
            PTP_AnnounceMessage  : begin
                header.message_length = header.header_size_in_bytes() + announce_message_body.body_size_in_bytes();
            end
            PTP_SyncMessage  : begin
                header.message_length = header.header_size_in_bytes() + sync_message_body.body_size_in_bytes();
            end
            PTP_Delay_ReqMessage  : begin
                header.message_length = header.header_size_in_bytes() + delay_req_message_body.body_size_in_bytes();
            end
            default     : 
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1105); 
   end

        endcase
        
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction

	                    virtual function void pack_ptp_with_options(uvm_packer packer, bit local_pack_header, bit local_pack_body, bit local_pack_fcs);
        if (local_pack_header) begin
            header.do_pack(packer);
        end
        if (local_pack_body) begin
            case (header.message_type)
                PTP_AnnounceMessage  : begin
                    announce_message_body.do_pack(packer);
                end
                PTP_SyncMessage  : begin
                    sync_message_body.do_pack(packer);
                end
                PTP_Delay_ReqMessage  : begin
                    delay_req_message_body.do_pack(packer);
                end
                default     : 
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1133); 
   end

            endcase
        end

        if ((local_pack_fcs) & (for_wireshark)) begin
            
   
  begin 
   int __array[]; 
   begin 
     bit [$bits(preamble)-1:0] __vector = preamble; 
     { << int { __array }} = {{($bits(int) - ($bits(preamble) % $bits(int))) {1'b0}}, __vector}; 
   end 
   packer.pack_ints(__array, $bits(preamble)); 
  end

;
        end
    endfunction

            virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_with_options(packer, pack_header, pack_body, pack_fcs);
    endfunction

	                    virtual function void unpack_ptp_with_options(uvm_packer packer, bit local_pack_header, bit local_pack_body, bit local_pack_fcs);
        if (local_pack_header) begin
            header.do_unpack(packer);
        end

        if (local_pack_body) begin
            case (header.message_type)
                PTP_AnnounceMessage  : begin
                    announce_message_body.do_unpack(packer);
                end
                PTP_SyncMessage  : begin
                    sync_message_body.do_unpack(packer);
                end
                PTP_Delay_ReqMessage  : begin
                    delay_req_message_body.do_unpack(packer);
                end
                default     : 
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1170); 
   end

            endcase
        end

        if ((local_pack_fcs) & (for_wireshark)) begin
            
   
   begin 
      int __array[] = new[($bits(preamble)+31)/32]; 
      bit [((($bits(preamble) + 31) / 32) * 32) - 1:0] __var; 
      packer.unpack_ints(__array, $bits(preamble)); 
      __var = { << int { __array }}; 
      preamble = __var; 
   end

;
        end
    endfunction

            virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_with_options(packer, pack_header, pack_body, pack_fcs);
    endfunction

            virtual function string convert2string();
        string what_to_return = $sformatf({"%s",", "},super.convert2string());
        $sformat(what_to_return, {what_to_return,header.convert2string(),", "});
        case (header.message_type)
            PTP_AnnounceMessage  : begin
                $sformat(what_to_return, {what_to_return,announce_message_body.convert2string(),", "});
            end
            PTP_SyncMessage  : begin
                $sformat(what_to_return, {what_to_return,sync_message_body.convert2string(),", "});
            end
            PTP_Delay_ReqMessage  : begin
                $sformat(what_to_return, {what_to_return,delay_req_message_body.convert2string(),", "});
            end
            default     : 
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1201); 
   end

        endcase
        $sformat(what_to_return, {what_to_return,"fcs: %0x",", "},fcs);
        return what_to_return;
    endfunction

            virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(32'h0000_000C);

        return result;
    endfunction

                    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(header.compare(casted_rhs.header, comparer) == 0) begin
            return 0;
        end

        case (header.message_type)
            PTP_AnnounceMessage  : begin
                if(announce_message_body.compare(casted_rhs.announce_message_body, comparer) == 0) begin
                    return 0;
                end
            end
            PTP_SyncMessage  : begin
                if(sync_message_body.compare(casted_rhs.sync_message_body, comparer) == 0) begin
                    return 0;
                end
            end
            PTP_Delay_ReqMessage  : begin
                if(delay_req_message_body.compare(casted_rhs.delay_req_message_body, comparer) == 0) begin
                    return 0;
                end
            end
            default     : 
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/sv/amiq_eth_packet_ptp.sv", 1251); 
   end

        endcase

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

            virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;

        pack_fcs = 0;

        super.pack_for_fcs(bitstream);

        pack_fcs = current_pack_fcs;
    endfunction
    
            virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=0;
        super.to_wireshark_array(byte_data);
        for_wireshark=1;
    endfunction

endclass


/* SLline 51 "./sv/amiq_eth_pkg.sv" 2 */

endpackage


/* SLline 27 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */

	/* SLline 1 "uvmc-2.2/src/connect/sv/uvmc_pkg.sv" 1 */


`timescale 1ps / 1ps






package uvmc_pkg;

import uvm_pkg::*;

parameter string uvmc_mgc_copyright  = "(C) 2009-2012 Mentor Graphics Corporation";
parameter string uvmc_revision = "UVMC-2.2";

bit x_banner_printed;

function void print_x_banner();
  if (x_banner_printed == 1)
    return;
  x_banner_printed = 1;
  $display("----------------------------------------------------------------");
  $display(uvmc_revision);
  $display(uvmc_mgc_copyright);
  $display("----------------------------------------------------------------");
endfunction

typedef int unsigned bits_t[9200];
typedef longint unsigned uint64;
typedef int unsigned uint32;


/* SLline 1 "uvmc-2.2/src/connect/sv/uvmc_common.sv" 1 */

import "DPI-C"  context function bit SV2C_blocking_req_done(int m_x_id);
import "DPI-C"  context function bit SV2C_blocking_rsp_done(int m_x_id,
                                                            bits_t bits,
                                                            uint64 delay);
export "DPI-C"  function C2SV_blocking_req_done;
export "DPI-C"  function C2SV_blocking_rsp_done;


import "DPI-C"  context function int SV2C_resolve_binding
            (
            string sv_port_name,              string sv_target,                 string sv_trans_type,             int    dummy,
            int    sv_proxy_type,             int    sv_mask,                   int    sv_id,                     output int sc_id                  );



class uvmc_converter #(type T=int);

  
  static uvm_object obj;

    
            
  static function void m_pre_pack (T t,
                                   uvm_packer packer);
    if ($cast(obj,t)) begin
          ovm_auto_options_object.packer=packer;
      packer.scope.down(obj.get_name(),t);
        end
    packer.reset();
  endfunction

        static function void m_post_pack (ref bits_t bits,
                                    input T t,
                                    uvm_packer packer);
    int cnt, sz;
    packer.set_packed_size();
    sz = (packer.m_packed_size+31) / 32;
                if (packer.big_endian) begin
      int unsigned raw;
      int unsigned val;
      for (int i=0; i<sz; i++) begin
        raw = packer.m_bits[cnt +: 32];
        for (int j=0; j<32; j++)
          val[j] = raw[31-j];
        bits[i] = val;
        cnt += 32;
      end
    end
    else begin
      for (int i=0; i<sz; i++) begin
        bits[i] = packer.m_bits[cnt +: 32];
        cnt += 32;
      end
    end
    if (obj != null)
          packer.scope.up(t);
        obj=null;
  endfunction

        static function void m_pre_unpack (ref bits_t bits,
                                     input T t,
                                     uvm_packer packer);
    static int cnt;
            int index;
    if (t != null && $cast(obj,t)) begin
                    ovm_auto_options_object.packer=packer;
        packer.scope.down(obj.get_name(),t);
          end
    packer.reset();
                if (packer.big_endian) begin
      int unsigned raw, val;
      foreach (bits[i]) begin
        raw = bits[i];
        for (int j=0; j<32; j++)
          val[j] = raw[31-j];
        packer.m_bits[index +: 32] = val;
        index += 32;
      end
    end
    else begin
      foreach (bits[i]) begin
        packer.m_bits[index +: 32] = bits[i];
        index += 32;
      end
    end
    packer.m_packed_size = index;
    packer.count = 0;
  endfunction

  static function void m_post_unpack (T t,
                                      uvm_packer packer);
        if (obj != null)
      packer.scope.up(t);
        obj=null;
  endfunction

endclass




parameter int UVM_PACK = OVM_PACK;
parameter int UVM_UNPACK = OVM_UNPACK;

class uvmc_default_converter #(type T=int) extends uvmc_converter #(T);

          
  static function void do_pack(T t, uvm_packer packer);
    if (t == null)
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 218); 
   end


          t.m_field_automation(null, UVM_PACK, "");
        t.do_pack(packer);
  endfunction


            
  static function void do_unpack(T t, uvm_packer packer);
    if (t == null)
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 238); 
   end


          t.m_field_automation(null, UVM_UNPACK, "");
        t.do_unpack(packer);
  endfunction

endclass



virtual class uvmc_base;

  
    virtual function void x_put      (ref bits_t bits);           endfunction
  virtual function bit  x_try_put  (ref bits_t bits); return 0; endfunction
  virtual function bit  x_can_put  ();                return 0; endfunction
  virtual function void x_get      ();                          endfunction
  virtual function bit  x_try_get  (ref bits_t bits); return 0; endfunction
  virtual function bit  x_can_get  ();                return 0; endfunction
  virtual function void x_peek     ();                          endfunction
  virtual function bit  x_try_peek (ref bits_t bits); return 0; endfunction
  virtual function bit  x_can_peek ();                return 0; endfunction
  virtual function void x_write    (ref bits_t bits); return;   endfunction
  virtual function void x_transport(ref bits_t bits);           endfunction
  virtual function bit  x_try_transport(ref bits_t bits); return 0; endfunction

    virtual function int x_nb_transport_fw (ref bits_t bits,
                                           inout uint32 phase,
                                           inout uint64 delay);
    return 0;
  endfunction

  virtual function int x_nb_transport_bw (ref bits_t bits,
                                           inout uint32 phase,
                                           inout uint64 delay);
    return 0;
  endfunction

  virtual function void x_b_transport (ref bits_t bits,
                                        inout uint64 delay);
  endfunction

              
  virtual function void blocking_rsp_done(ref bits_t bits, input uint64 delay);
  endfunction

  virtual function void blocking_req_done();
  endfunction

  uvm_packer packer;

  static uvmc_base x_ports[$];
  static int x_port_names[string];

    local     string m_lookup_name;          bit    m_locally_connected;   local     bit    m_x_connected;        protected int    m_id;          int    m_x_id = 0;           string m_port_name;
  
    

  pure virtual function string get_full_name();


                                
  function new(string port_name, string lookup_name="", uvm_packer packer=null);

    int id;

    m_port_name = port_name;
    m_lookup_name = lookup_name;

    assert(port_name != "");

    $write("Registering SV-side '",port_name,"'");
    if (lookup_name != "")
      $write(" and lookup string '",lookup_name,"'");
    $display(" for later connection with SC");
    
        if (x_port_names.exists(port_name)) begin
      int local_id = x_port_names[port_name];
      uvmc_base exist_port = x_ports[local_id];
      if (exist_port.m_x_id != 0) begin
        uvmc_base bound_port = x_ports[exist_port.m_x_id];
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 381); 
   end


        return;
      end
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_WARNING,"UVMC")) 
       ovm_report_warning ("UVMC", {"Making local SV connection between '",
                   exist_port.m_port_name,"' and '", port_name}, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 385); 
   end


      m_locally_connected = 1;
      m_x_id = local_id;
      id = x_ports.size();
      x_ports.push_back(this);
      x_port_names[port_name] = id;
      exist_port.m_x_id = id;
      exist_port.m_locally_connected = 1;
      return;
    end

        if (lookup_name != "" && x_port_names.exists(lookup_name)) begin
      int local_id = x_port_names[lookup_name];
      uvmc_base exist_port = x_ports[local_id];
      if (exist_port.m_x_id != 0) begin
        uvmc_base bound_port = x_ports[exist_port.m_x_id];
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 403); 
   end


        return;
      end
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_WARNING,"UVMC")) 
       ovm_report_warning ("UVMC", {"Making local SV connection between '",
                   exist_port.m_port_name,"' and '", port_name}, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 407); 
   end


      m_locally_connected = 1;
      m_x_id = local_id;
      id = x_ports.size();
      x_ports.push_back(this);
      x_port_names[port_name] = id;
      exist_port.m_x_id = id;
      exist_port.m_locally_connected = 1;
      return;
    end

    if (x_ports.size()==0)
      x_ports.push_back(null);

    id = x_ports.size();

    x_ports.push_back(this);
    x_port_names[port_name] = id;

    if (lookup_name != "")
      x_port_names[lookup_name] = id;

    if (packer == null) begin
      packer = new();
      packer.use_metadata = 1;
      packer.big_endian = 0;
    end

    this.packer = packer;

  endfunction


            virtual function void resolve_bindings(uvm_port_type_e proxy_kind, int if_mask);

   string unknown = "unknown";
   int kind = proxy_kind;
   int dummy = 0;

    if (m_x_connected)
      return;


    m_x_connected = 1; 
    
    m_id = this.x_port_names[m_port_name];

    if (m_x_id == 0 && !SV2C_resolve_binding(m_port_name,m_lookup_name,unknown, dummy, kind,
                              if_mask, m_id, m_x_id)) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 464); 
   end


      return;
    end
  endfunction
 

endclass: uvmc_base





function void C2SV_blocking_rsp_done(int x_id, bits_t bits, uint64 delay);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 501); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 501); 
   end

 
      $finish; 
    end 
            
  port.blocking_rsp_done(bits,delay);
endfunction

function void C2SV_blocking_req_done(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 506); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_common.sv", 506); 
   end

 
      $finish; 
    end 
            
  port.blocking_req_done();
endfunction




/* SLline 71 "uvmc-2.2/src/connect/sv/uvmc_pkg.sv" 2 */
/* SLline 1 "uvmc-2.2/src/connect/sv/uvmc_tlm1.sv" 1 */






import "DPI-C" context function bit  SV2C_put      (int x_id, bits_t bits);
import "DPI-C" context function bit  SV2C_try_put  (int x_id, bits_t bits);
import "DPI-C" context function bit  SV2C_can_put  (int x_id);
import "DPI-C" context function bit  SV2C_get      (int x_id);
import "DPI-C" context function bit  SV2C_try_get  (int x_id, output bits_t bits);
import "DPI-C" context function bit  SV2C_can_get  (int x_id);
import "DPI-C" context function bit  SV2C_peek     (int x_id);
import "DPI-C" context function bit  SV2C_try_peek (int x_id, output bits_t bits);
import "DPI-C" context function bit  SV2C_can_peek (int x_id);
import "DPI-C" context function bit  SV2C_write    (int x_id, bits_t bits);
import "DPI-C" context function bit  SV2C_transport(int x_id, inout bits_t bits);
import "DPI-C" context function bit  SV2C_try_transport(int x_id, inout bits_t bits);



export "DPI-C"  function C2SV_put;
export "DPI-C"  function C2SV_try_put;
export "DPI-C"  function C2SV_can_put;
export "DPI-C"  function C2SV_get;
export "DPI-C"  function C2SV_try_get;
export "DPI-C"  function C2SV_can_get;
export "DPI-C"  function C2SV_peek;
export "DPI-C"  function C2SV_try_peek;
export "DPI-C"  function C2SV_can_peek;
export "DPI-C"  function C2SV_write;
export "DPI-C"  function C2SV_transport;
export "DPI-C"  function C2SV_try_transport;



function void C2SV_put(int x_id, bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 85); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 85); 
   end

 
      $finish; 
    end 
            
  port.x_put(bits);
endfunction

function bit C2SV_try_put(int x_id, bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 90); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 90); 
   end

 
      $finish; 
    end 
            
  return port.x_try_put(bits);
endfunction

function bit C2SV_can_put(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 95); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 95); 
   end

 
      $finish; 
    end 
            
  return port.x_can_put();
endfunction



function void C2SV_get(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 103); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 103); 
   end

 
      $finish; 
    end 
            
  port.x_get();
endfunction

function bit C2SV_try_get(int x_id, output bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 108); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 108); 
   end

 
      $finish; 
    end 
            
  return port.x_try_get(bits);
endfunction

function bit C2SV_can_get(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 113); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 113); 
   end

 
      $finish; 
    end 
            
  return port.x_can_get();
endfunction



function void C2SV_peek(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 121); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 121); 
   end

 
      $finish; 
    end 
            
  port.x_peek();
endfunction

function bit C2SV_try_peek(int x_id, output bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 126); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 126); 
   end

 
      $finish; 
    end 
            
  return port.x_try_peek(bits);
endfunction

function bit C2SV_can_peek(int x_id);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 131); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 131); 
   end

 
      $finish; 
    end 
            
  return port.x_can_peek();
endfunction



function void C2SV_write(int x_id, bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 139); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 139); 
   end

 
      $finish; 
    end 
            
  port.x_write(bits);
endfunction



function void C2SV_transport(int x_id, inout bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 147); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 147); 
   end

 
      $finish; 
    end 
            
  port.x_transport(bits);
endfunction

function bit C2SV_try_transport(int x_id, inout bits_t bits);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 152); 
   end

 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 152); 
   end

 
      $finish; 
    end 
            
  return port.x_try_transport(bits);
endfunction




class uvmc_tlm1_dispatch #(type T1=int,
                           T2=T1,
                           CVRT_T1=int,                            CVRT_T2=CVRT_T1                            ) extends uvmc_base;
  
      typedef ovm_port_base #(tlm_if_base #(T1,T2)) imp_t;
  
  typedef enum {NONE,PUT,GET,PEEK,TRANSPORT} op_e;

   imp_t m_imp;

  local bits_t  m_bits;   local semaphore      m_sem = new(1);
  local T1             t1;
  local op_e           m_blocking_op;
  local event          m_blocking_op_done;
  local process        m_blocking_sync_proc;
  local uint64         m_delay;


            
  function new (string port_name,
                string lookup_name="",
                uvm_packer packer,
                imp_t imp);
    super.new(port_name, lookup_name, packer);
    this.m_imp = imp;
    if (m_blocking_sync_proc == null)
      fork begin
        m_blocking_sync_proc = process::self();
        blocking_sync_process();
      end
      join_none
  endfunction

  virtual function string get_full_name();
    return m_imp.get_full_name();
  endfunction


                          

        
  function void notify_blocking_sync_op(op_e op);
    m_blocking_op = op;
  endfunction



            
  virtual function void blocking_rsp_done(ref bits_t bits, input uint64 delay);
            m_bits = bits;
    ->m_blocking_op_done;
  endfunction


        
  virtual function void blocking_req_done();
    ->m_blocking_op_done;
  endfunction


                
  task blocking_sync_process();
    forever begin
      @(m_blocking_op != NONE);
      case (m_blocking_op)
        PUT: begin
               m_imp.put(t1);
               void'(SV2C_blocking_req_done(m_x_id));
             end
        GET: begin
               T2 t2;
               m_imp.get(t2);
               CVRT_T2::m_pre_pack(t2,packer);
               CVRT_T2::do_pack(t2,packer);
               CVRT_T2::m_post_pack(m_bits,t2,packer);
               void'(SV2C_blocking_rsp_done(m_x_id,m_bits,0));
             end
        PEEK: begin
               T2 t2;
               m_imp.peek(t2);
               CVRT_T2::m_pre_pack(t2,packer);
               CVRT_T2::do_pack(t2,packer);
               CVRT_T2::m_post_pack(m_bits,t2,packer);
               void'(SV2C_blocking_rsp_done(m_x_id,m_bits,0));
             end
        TRANSPORT: begin
               T2 t2;
               m_imp.transport(t1,t2);
               CVRT_T2::m_pre_pack(t2,packer);
               CVRT_T2::do_pack(t2,packer);
               CVRT_T2::m_post_pack(m_bits,t2,packer);
               void'(SV2C_blocking_rsp_done(m_x_id,m_bits,0));
             end
        default: begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 314); 
   end


             end
      endcase
      m_blocking_op = NONE;
    end
  endtask


                        
  function void x_put(ref bits_t bits);
    t1 = new();
    CVRT_T1::m_pre_unpack(bits,t1,packer);
    CVRT_T1::do_unpack(t1,packer);
    CVRT_T1::m_post_unpack(t1,packer);
    notify_blocking_sync_op(PUT);
  endfunction

  function bit x_try_put(ref bits_t bits);
    T1 t;
            t = new();
    CVRT_T1::m_pre_unpack(bits,t,packer);
    CVRT_T1::do_unpack(t,packer);
    CVRT_T1::m_post_unpack(t,packer);
    return m_imp.try_put(t);
  endfunction

  function bit x_can_put();
    return m_imp.can_put();
  endfunction

  function void x_get();
    notify_blocking_sync_op(GET);
  endfunction

  function bit x_try_get(ref bits_t bits);
    T2 t;
    if (m_imp.try_get(t)) begin
      CVRT_T2::m_pre_pack(t,packer);
      CVRT_T2::do_pack(t,packer);
      CVRT_T2::m_post_pack(bits,t,packer);
      return 1;
    end
    return 0;
  endfunction

  function bit x_can_get();
    return m_imp.can_get();
  endfunction

  function void x_peek();
    notify_blocking_sync_op(PEEK);
  endfunction 

  function bit x_try_peek(ref bits_t bits);
    T2 t;
    if (m_imp.try_peek(t)) begin
      CVRT_T2::m_pre_pack(t,packer);
      CVRT_T2::do_pack(t,packer);
      CVRT_T2::m_post_pack(bits,t,packer);
      return 1;
    end
    return 0;
  endfunction

  function bit x_can_peek();
    return m_imp.can_peek();
  endfunction 

  function void x_write(ref bits_t bits);
    T1 t;
    t = new();
    CVRT_T1::m_pre_unpack(bits,t,packer);
    CVRT_T1::do_unpack(t,packer);
    CVRT_T1::m_post_unpack(t,packer);
    m_imp.write(t);
  endfunction

  function void x_transport(ref bits_t bits);
    t1 = null;
    t1 = new();
    CVRT_T1::m_pre_unpack(bits,t1,packer);
    CVRT_T1::do_unpack(t1,packer);
    CVRT_T1::m_post_unpack(t1,packer);
    notify_blocking_sync_op(TRANSPORT);
  endfunction

  function bit x_try_transport(ref bits_t bits);
    T1 req;
    T2 rsp;
    req = new();
    CVRT_T1::m_pre_unpack(bits,req,packer);
    CVRT_T1::do_unpack(req,packer);
    CVRT_T1::m_post_unpack(req,packer);
    x_try_transport = m_imp.nb_transport(req,rsp);
    if (x_try_transport) begin
      CVRT_T2::m_pre_pack(rsp,packer);
      CVRT_T2::do_pack(rsp,packer);
      CVRT_T2::m_post_pack(bits,rsp,packer);
    end
  endfunction



                            
 
  function bit can_put();
    can_put = SV2C_can_put(m_x_id);
  endfunction

  function bit try_put(T1 t);
    if (!m_sem.try_get())
      return 0;
    if (!can_put()) begin
      m_sem.put();
      return 0;
    end  
    CVRT_T1::m_pre_pack(t,packer);
    CVRT_T1::do_pack(t,packer);
    CVRT_T1::m_post_pack(m_bits,t,packer);
    try_put = SV2C_try_put(m_x_id,m_bits);
    if (!try_put) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 466); 
   end


    end
    m_sem.put();
  endfunction

  virtual task put(T1 t);
    m_sem.get();
    CVRT_T1::m_pre_pack(t,packer);
    CVRT_T1::do_pack(t,packer);
    CVRT_T1::m_post_pack(m_bits,t,packer);
    void'(SV2C_put(m_x_id,m_bits));
    @m_blocking_op_done;
    m_sem.put();
  endtask


  
  function bit can_get();
    return SV2C_can_get(m_x_id);
  endfunction

  function bit try_get(output T2 t);
    if (!m_sem.try_get())
      return 0;
    if (!can_get()) begin
      m_sem.put();
      return 0;
    end
    try_get = SV2C_try_get(m_x_id,m_bits);
    if (!try_get) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 497); 
   end


      return 0;
    end
    t=new();
    CVRT_T2::m_pre_unpack(m_bits,t,packer);
    CVRT_T2::do_unpack(t,packer);
    CVRT_T2::m_post_unpack(t,packer);
    m_sem.put();
  endfunction

  task get(output T2 t);
    m_sem.get();
    void'(SV2C_get(m_x_id));
    @m_blocking_op_done;
    t=new();
    CVRT_T2::m_pre_unpack(m_bits,t,packer);
    CVRT_T2::do_unpack(t,packer);
    CVRT_T2::m_post_unpack(t,packer);
    m_sem.put();
  endtask


  
  function bit can_peek();
    return SV2C_can_peek(m_x_id);
  endfunction

  function bit try_peek(output T2 t);
    if (!m_sem.try_get())
      return 0;
    if (!can_peek()) begin
      m_sem.put();
      return 0;
    end
    try_peek = SV2C_try_peek(m_x_id,m_bits);
    if (!try_peek) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 534); 
   end


      return 0;
    end
    t=new();
    CVRT_T2::m_pre_unpack(m_bits,t,packer);
    CVRT_T2::do_unpack(t,packer);
    CVRT_T2::m_post_unpack(t,packer);
    m_sem.put();
  endfunction

  task peek(output T2 t);
    m_sem.get();
    void'(SV2C_peek(m_x_id));
    @m_blocking_op_done;
    t=new();
    CVRT_T2::m_pre_unpack(m_bits,t,packer);
    CVRT_T2::do_unpack(t,packer);
    CVRT_T2::m_post_unpack(t,packer);
    m_sem.put();
  endtask


  
  function void write(T1 t);
    CVRT_T1::m_pre_pack(t,packer);
    CVRT_T1::do_pack(t,packer);
    CVRT_T1::m_post_pack(m_bits,t,packer);
    void'(SV2C_write(m_x_id,m_bits));
  endfunction


  
  task transport(T1 req, output T2 rsp);
    m_sem.get();
    CVRT_T1::m_pre_pack(req,packer);
    CVRT_T1::do_pack(req,packer);
    CVRT_T1::m_post_pack(m_bits,req,packer);
    void'(SV2C_transport(m_x_id,m_bits));
    @m_blocking_op_done;
    rsp=new();
    CVRT_T2::m_pre_unpack(m_bits,rsp,packer);
    CVRT_T2::do_unpack(rsp,packer);
    CVRT_T2::m_post_unpack(rsp,packer);
    m_sem.put();
  endtask

  function bit nb_transport(T1 req, output T2 rsp);
    CVRT_T1::m_pre_pack(req,packer);
    CVRT_T1::do_pack(req,packer);
    CVRT_T1::m_post_pack(m_bits,req,packer);
                rsp=new();
    CVRT_T2::m_pre_unpack(m_bits,rsp,packer);
    CVRT_T2::do_unpack(rsp,packer);
    CVRT_T2::m_post_unpack(rsp,packer);
    return 1;
  endfunction


endclass




class uvmc_tlm1_port_proxy #(type T1=int, T2=T1,
                               CVRT_T1=uvmc_default_converter #(uvm_object),
                               CVRT_T2=CVRT_T1)
                             extends ovm_port_base #(tlm_if_base #(T1,T2));
  typedef ovm_port_base #(tlm_if_base #(T1,T2)) port_type;
  
  typedef uvmc_tlm1_dispatch #(T1,T2,CVRT_T1,CVRT_T2) x_dispatch_type;
  typedef uvmc_tlm1_port_proxy #(T1,T2,CVRT_T1,CVRT_T2) this_type;

  static this_type m_proxys[string];

  local x_dispatch_type m_x_dispatch;
  this_type m_local_proxy;

  const string m_type_name;

            
  function new(port_type port, string lookup_name,uvm_port_type_e proxy_kind,
               uvm_packer packer);
                  super.new({"UVMC_PROXY.",port.get_full_name()},ovm_top,proxy_kind,1,1);
                        if (proxy_kind == UVM_PORT)
          m_if_mask = 'h0;
        else
          m_if_mask = 'h7FFFFFFF;
              m_type_name = {"UVMC_PROXY_FOR_",port.get_type_name()};
    m_x_dispatch = new(port.get_full_name(), lookup_name, packer, this);
    m_proxys[port.get_full_name()] = this;
  endfunction


      
  virtual function string get_type_name();
    return m_type_name;
  endfunction


          
  virtual function void resolve_bindings();
                  int mask;
                                if (is_port())
          mask = 'h7FFFFFFF;
        else
          mask = 'h0;
        m_x_dispatch.resolve_bindings(
               uvm_port_type_e'(is_port()?UVM_PORT:UVM_IMPLEMENTATION), mask);
              super.resolve_bindings();
    m_x_dispatch.m_imp = m_if;

            if (m_x_dispatch.m_locally_connected && m_local_proxy == null && !is_port())
      m_local_proxy=m_proxys[uvmc_base::x_ports[m_x_dispatch.m_x_id].m_port_name];
  endfunction

        
   task put (T1 t); 
    if (m_local_proxy != null)
      m_local_proxy.m_if.put(t);
    else
      m_x_dispatch.put(t);
  endtask

  function bit try_put (T1 t); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.try_put(t);
    else
      return m_x_dispatch.try_put(t); 
  endfunction 
  function bit can_put(); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.can_put();
    else
      return m_x_dispatch.can_put(); 
  endfunction

  task get (output T2 t); 
    if (m_local_proxy != null)
      m_local_proxy.m_if.get(t);
    else
      m_x_dispatch.get(t); 
  endtask

  function bit try_get (output T2 t); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.try_get(t);
    else
      return m_x_dispatch.try_get(t); 
  endfunction 
  function bit can_get(); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.can_get();
    else
      return m_x_dispatch.can_get(); 
  endfunction

  task peek (output T2 t); 
    if (m_local_proxy != null)
      m_local_proxy.m_if.peek(t);
    else
      m_x_dispatch.peek(t); 
  endtask

  function bit try_peek (output T2 t); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.try_peek(t);
    else
      return m_x_dispatch.try_peek(t); 
  endfunction 
  function bit can_peek(); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.can_peek();
    else
      return m_x_dispatch.can_peek(); 
  endfunction

  task transport (T1 req, output T2 rsp); 
    if (m_local_proxy != null)
      m_local_proxy.m_if.transport(req,rsp);
    else
      m_x_dispatch.transport(req, rsp); 
  endtask

  function bit nb_transport (T1 req, output T2 rsp); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.nb_transport(req,rsp);
    else
      return m_x_dispatch.nb_transport(req, rsp); 
  endfunction


  function void write (input T1 t);
    if (m_local_proxy != null)
      m_local_proxy.m_if.write(t);
    else
      m_x_dispatch.write(t);
  endfunction

endclass




class uvmc_tlm1 #(type T1=int, T2=T1,
                    CVRT_T1=uvmc_default_converter #(uvm_object),
                    CVRT_T2=CVRT_T1); 
  typedef uvmc_tlm1_port_proxy #(T1,T2,CVRT_T1,CVRT_T2) port_proxy_type;
    typedef ovm_port_base #(tlm_if_base #(T1,T2)) port_type;
  
                            
  static function void connect(port_type port,
                               string lookup_name="",
                               uvm_packer packer=null);
    port_proxy_type proxy; 

    
    print_x_banner();

    if (port == null)
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 842); 
   end



    
    if (port.is_port()) begin
      proxy = new(port, lookup_name, UVM_IMPLEMENTATION, packer);
      port.connect(proxy);
    end
    else begin
      proxy = new(port, lookup_name, UVM_PORT, packer);
      proxy.connect(port);
    end
  endfunction


                                  
  static function void connect_hier(port_type port,
                                    string lookup_name="",
                                    uvm_packer packer=null);
    port_proxy_type proxy; 
    
    print_x_banner();

    if (port == null)
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 893); 
   end



    
    if (port.is_port()) begin
      proxy = new(port, lookup_name, UVM_PORT, packer);
      proxy.connect(port);
    end
    else if (port.is_export()) begin
      proxy = new(port, lookup_name, UVM_IMPLEMENTATION, packer);
      port.connect(proxy);
    end
    else begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"UVMC")) 
       ovm_report_fatal ("UVMC", 
         "Null transaction handle passed to uvmc_default_converter::do_pack", OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm1.sv", 913); 
   end

;
    end
  endfunction


endclass



/* SLline 72 "uvmc-2.2/src/connect/sv/uvmc_pkg.sv" 2 */
/* SLline 1 "uvmc-2.2/src/connect/sv/uvmc_tlm2.sv" 1 */





import "DPI-C" context function int  SV2C_nb_transport_fw (int x_id,
                                                           inout bits_t bits,
                                                           inout uint32 phase,
                                                           inout uint64 delay);

import "DPI-C" context function int  SV2C_nb_transport_bw (int x_id,
                                                           inout bits_t bits,
                                                           inout uint32 phase,
                                                           inout uint64 delay);

import "DPI-C" context function bit  SV2C_b_transport     (int x_id,
                                                           inout bits_t bits,
                                                           input uint64 delay);



export "DPI-C"  function C2SV_nb_transport_fw;
export "DPI-C"  function C2SV_nb_transport_bw;
export "DPI-C"  function C2SV_b_transport;

function int C2SV_nb_transport_fw(int x_id,
                                  inout bits_t bits,
                                  inout uint32 phase,
                                  inout uint64 delay);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 91); 
   end
 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 91); 
   end
 
      $finish; 
    end 
            
  C2SV_nb_transport_fw = port.x_nb_transport_fw(bits,phase,delay);
endfunction

function int C2SV_nb_transport_bw(int x_id,
                                  inout bits_t bits,
                                  inout uint32 phase,
                                  inout uint64 delay);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 99); 
   end
 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 99); 
   end
 
      $finish; 
    end 
            
  return port.x_nb_transport_bw(bits,phase,delay);
endfunction

function void C2SV_b_transport (int x_id,
                                inout bits_t bits,
                                input uint64 delay);
  
    uvmc_base port; 
    if (x_id < 0 || x_id >= uvmc_base::x_ports.size()) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 106); 
   end
 
      $finish; 
    end 
    port = uvmc_base::x_ports[x_id]; 
    if (port == null) begin 
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 106); 
   end
 
      $finish; 
    end 
            
  port.x_b_transport(bits, delay);
endfunction





class uvmc_tlm2_dispatch #(type T=uvm_tlm_generic_payload,
                                PH=uvm_tlm_phase_e,
                                CVRT=int)
                          extends uvmc_base;
  typedef uvm_port_base #(uvm_tlm_if #(T,PH)) imp_t;

  typedef enum {NONE,B_TRANSPORT} op_e;

   imp_t m_imp;
   imp_t m_local_imp;
   bit   m_trans_is_gp;

  local bits_t          m_bits;   local semaphore       m_sem = new(1);
  local T               m_t;
  local op_e            m_blocking_op;
  local event           m_blocking_op_done;
  local uvm_tlm_time    m_delay;
  local uint64          m_delay_bits;
  local uvm_tlm_phase_e m_phase;
  local process         m_blocking_sync_proc;


      
  function new(string port_name,
               string lookup_name="",
               uvm_packer packer,
               imp_t imp=null);
    uvm_tlm_generic_payload gp;
    super.new(port_name, lookup_name, packer);
    m_t = new();
    if ($cast(gp,m_t))
      m_trans_is_gp = 1;
    m_t = null;
    this.m_imp = imp;
    if (m_blocking_sync_proc == null)
      fork begin
        m_blocking_sync_proc = process::self();
        blocking_sync_proc();
      end
      join_none
  endfunction


  virtual function string get_full_name();
    return m_imp.get_full_name();
  endfunction


         
  virtual function void blocking_rsp_done(ref bits_t bits,
                                          input uint64 delay);
            m_bits = bits;
    m_delay_bits = delay;
    ->m_blocking_op_done;
  endfunction


            virtual function void blocking_req_done();
    ->m_blocking_op_done;
  endfunction


        task blocking_sync_proc();
    forever begin
      @(m_blocking_op != NONE);
      case (m_blocking_op)
        B_TRANSPORT: begin
               uint64 del;
               m_imp.b_transport(m_t,m_delay);
               CVRT::m_pre_pack(m_t,packer);
               CVRT::do_pack(m_t,packer);
               CVRT::m_post_pack(m_bits,m_t,packer);
               del = $realtobits(m_delay.get_abstime(1.0e-12));
               void'(SV2C_blocking_rsp_done(m_x_id,m_bits,del));
                                           end
        default:
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 215); 
   end

      endcase
      m_blocking_op = NONE;
    end
  endtask


    
  function void x_b_transport (ref bits_t bits,
                               inout uint64 delay);
    T t;
    m_delay = new("x_b_transport_delay", 1.0e-12);
    t = new();
                            CVRT::m_pre_unpack(bits,t,packer);
    CVRT::do_unpack(t,packer);
    CVRT::m_post_unpack(t,packer);
    m_t = t;
    m_delay.set_abstime($bitstoreal(delay),1.0e-12);
    m_blocking_op = B_TRANSPORT;
  endfunction

  function int x_nb_transport_fw (ref bits_t bits,
                                  inout uint32 phase,
                                  inout uint64 delay);
    uvm_tlm_time del = new("x_nb_transport_fw_delay", 1.0e-12);
    uvm_tlm_phase_e ph = uvm_tlm_phase_e'(phase);
    if (m_t == null)
      m_t = new();
    del.set_abstime($bitstoreal(delay),1.0e-12);
    CVRT::m_pre_unpack(bits,m_t,packer);
    CVRT::do_unpack(m_t,packer);
    CVRT::m_post_unpack(m_t,packer);
    x_nb_transport_fw = m_imp.nb_transport_fw(m_t, ph, del);
    CVRT::m_pre_pack(m_t,packer);
    CVRT::do_pack(m_t,packer);
    CVRT::m_post_pack(bits,m_t,packer);
    delay = $realtobits(del.get_abstime(1.0e-12));
    phase = ph;
    if (phase == UVM_TLM_COMPLETED)
      m_t = null;
  endfunction

  function int x_nb_transport_bw (ref bits_t bits,
                                  inout uint32 phase,
                                  inout uint64 delay);
    uvm_tlm_time del = new("x_nb_transport_bw_delay", 1.0e-12);
    uvm_tlm_phase_e ph = uvm_tlm_phase_e'(phase);
    if (m_t == null)
      m_t = new();
    del.set_abstime($bitstoreal(delay),1.0e-12);
    CVRT::m_pre_unpack(bits,m_t,packer);
    CVRT::do_unpack(m_t,packer);
    CVRT::m_post_unpack(m_t,packer);
    x_nb_transport_bw = m_imp.nb_transport_bw(m_t, ph, del);
    CVRT::m_pre_pack(m_t,packer);
    CVRT::do_pack(m_t,packer);
    CVRT::m_post_pack(bits,m_t,packer);
    delay = $realtobits(del.get_abstime(1.0e-12));
    phase = ph;
    if (phase == UVM_TLM_COMPLETED)
      m_t = null;
  endfunction


            
  task b_transport (T t, uvm_tlm_time delay); 
    uint64 del;
    if (delay == null) begin
       
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 296); 
   end

       return;
    end
    del = $realtobits(delay.get_abstime(1.0e-12));
    m_sem.get();
    if (m_local_imp != null) begin
      m_local_imp.b_transport(t,delay);
      m_sem.put();
      return;
    end
    CVRT::m_pre_pack(t,packer);
    CVRT::do_pack(t,packer);
    CVRT::m_post_pack(m_bits,t,packer);
        void'(SV2C_b_transport(m_x_id,m_bits,del));
    @m_blocking_op_done;
    CVRT::m_pre_unpack(m_bits,t,packer);
    CVRT::do_unpack(t,packer);
    CVRT::m_post_unpack(t,packer);
    delay.set_abstime($bitstoreal(m_delay_bits),1.0e-12);
    m_sem.put();
  endtask


  function uvm_tlm_sync_e nb_transport_fw (T t,
                                           ref uvm_tlm_phase_e p,
                                           input uvm_tlm_time delay); 
    uint64 del;
    uint32 ph = p;
    int result;
    if (delay == null) begin
       
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 328); 
   end

       return UVM_TLM_COMPLETED;
    end
    del = $realtobits(delay.get_abstime(1.0e-12));
    if (!m_sem.try_get())
      return UVM_TLM_COMPLETED;
    CVRT::m_pre_pack(t,packer);
    CVRT::do_pack(t,packer);
    CVRT::m_post_pack(m_bits,t,packer);
    result = SV2C_nb_transport_fw(m_x_id,m_bits,ph,del);
    CVRT::m_pre_unpack(m_bits,t,packer);
    CVRT::do_unpack(t,packer);
    CVRT::m_post_unpack(t,packer);
    nb_transport_fw = uvm_tlm_sync_e'(result);
    delay.set_abstime($bitstoreal(del),1.0e-12);
    p = PH'(ph);
    m_sem.put();
  endfunction


  function uvm_tlm_sync_e nb_transport_bw (T t,
                                           ref uvm_tlm_phase_e p,
                                           input uvm_tlm_time delay); 
    uint64 del;
    uint32 ph = p;
    int result;
    if (delay == null) begin
       
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 356); 
   end

       return UVM_TLM_COMPLETED;
    end
    del = $realtobits(delay.get_abstime(1.0e-12));
    if (!m_sem.try_get())
      return UVM_TLM_COMPLETED;
    CVRT::m_pre_pack(t,packer);
    CVRT::do_pack(t,packer);
    CVRT::m_post_pack(m_bits,t,packer);
    result = SV2C_nb_transport_bw(m_x_id,m_bits,ph,del);
    CVRT::m_pre_unpack(m_bits,t,packer);
    CVRT::do_unpack(t,packer);
    CVRT::m_post_unpack(t,packer);
    delay.set_abstime($bitstoreal(del),1.0e-12);
    nb_transport_bw = uvm_tlm_sync_e'(result);
    p = PH'(ph);
    m_sem.put();
  endfunction

endclass



class uvmc_tlm2_port_proxy #(type T=uvm_tlm_generic_payload,
                                  P=uvm_tlm_phase_e,
                                  CVRT=uvmc_default_converter#(uvm_object)
                                  )
                           extends uvm_port_base #(uvm_tlm_if #(T,P));

  typedef uvm_port_base #(uvm_tlm_if #(T,P)) port_type;
  typedef uvmc_tlm2_dispatch #(T,P,CVRT) x_dispatch_type;
  typedef uvmc_tlm2_port_proxy #(T,P,CVRT) this_type;

  static this_type m_proxys[string];

  local x_dispatch_type m_x_dispatch;
  this_type m_local_proxy;

  const string m_type_name;


      
  function new(port_type port, string lookup_name, uvm_port_type_e proxy_type,
               uvm_packer packer); 
    super.new({"UVMC_PROXY.",port.get_full_name()},uvm_top,proxy_type,1,1);
    m_if_mask = port.m_get_if_mask();
    m_type_name = {"UVMC_PROXY_FOR_",port.get_type_name()};
    m_x_dispatch = new(port.get_full_name(), lookup_name, packer, this);
    m_proxys[port.get_full_name()] = this;
  endfunction


  virtual function string get_type_name();
    return m_type_name;
  endfunction


          
  virtual function void resolve_bindings();
    m_x_dispatch.resolve_bindings(is_port()?UVM_PORT:UVM_IMPLEMENTATION, m_if_mask);
    super.resolve_bindings();
    m_x_dispatch.m_imp = m_if;

            if (m_x_dispatch.m_locally_connected && m_local_proxy == null && !is_port())
      m_local_proxy = m_proxys[uvmc_base::x_ports[m_x_dispatch.m_x_id].m_port_name];

  endfunction


            
  task b_transport (T t, uvm_tlm_time delay);
    if (m_local_proxy != null)
      m_local_proxy.m_if.b_transport(t, delay);
    else
      m_x_dispatch.b_transport(t, delay);
  endtask

  function uvm_tlm_sync_e nb_transport_fw (T t,
                                           ref P p,
                                           input uvm_tlm_time delay); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.nb_transport_fw(t, p, delay);
    else
      return m_x_dispatch.nb_transport_fw(t, p, delay);
  endfunction

  function uvm_tlm_sync_e nb_transport_bw (T t,
                                           ref P p,
                                           input uvm_tlm_time delay); 
    if (m_local_proxy != null)
      return m_local_proxy.m_if.nb_transport_bw(t, p, delay);
    else
      return m_x_dispatch.nb_transport_bw(t, p, delay);
  endfunction

endclass




class uvmc_tlm_b_target_comp #(type T=uvm_tlm_generic_payload,
                                    CVRT=uvmc_default_converter#(uvm_object)
                                    )
                           extends uvm_component;
  typedef uvmc_tlm2_dispatch #(T,uvm_tlm_phase_e,CVRT) imp_t;
  typedef uvmc_tlm_b_target_comp #(T,CVRT) this_type;
  uvm_tlm_b_target_socket #(this_type,T) target_skt;
  imp_t m_imp;
  uvm_port_base #(uvm_tlm_if #(T,uvm_tlm_phase_e)) m_local_proxy;

  function new(string name, uvm_component parent=null, imp_t imp=null);
    super.new(name, parent);
    target_skt = new(name, this);
    m_imp = imp;
  endfunction

  virtual function void resolve_bindings();
    m_imp.resolve_bindings(UVM_IMPLEMENTATION,(1<<2)+
                                              (1<<0)+
                                              (1<<1));
    super.resolve_bindings();
    if (m_imp.m_locally_connected && m_local_proxy == null)
      m_local_proxy = m_imp.m_imp;
  endfunction

  task b_transport(T t, uvm_tlm_time delay); 
    if (m_local_proxy != null)
      m_local_proxy.b_transport(t,delay);
    else
      m_imp.b_transport(t,delay);
  endtask
endclass


class uvmc_tlm_nb_target_comp #(type T=uvm_tlm_generic_payload,
                                     P=uvm_tlm_phase_e,
                                     CVRT=uvmc_default_converter#(uvm_object)
                                     )
                            extends uvm_component;
  typedef uvmc_tlm2_dispatch #(T,P,CVRT) imp_t;
  typedef uvmc_tlm_nb_target_comp #(T,P,CVRT) this_type;
  uvm_tlm_nb_target_socket #(this_type,T,P) target_skt;
  imp_t m_imp;
  
  function new(string name, uvm_component parent=null, imp_t imp=null);
    super.new(name, parent);
    target_skt = new(name, this);
    m_imp = imp;
  endfunction

  virtual function void resolve_bindings();
    m_imp.resolve_bindings(UVM_IMPLEMENTATION,(1<<2)+
                                              (1<<0)+
                                              (1<<1));
    super.resolve_bindings();
          endfunction

  task b_transport(T t, uvm_tlm_time delay); 
    m_imp.b_transport(t,delay);
  endtask
  function uvm_tlm_sync_e nb_transport_fw (T t,
                                           ref uvm_tlm_phase_e p,
                                           input uvm_tlm_time delay); 
            return m_imp.nb_transport_fw(t,p,delay);
  endfunction
endclass


class uvmc_tlm_b_initiator_comp #(type T=uvm_tlm_generic_payload,
                                       CVRT=uvmc_default_converter#(uvm_object)
                                       )
                              extends uvm_component;
  typedef uvmc_tlm2_dispatch #(T,uvm_tlm_phase_e,CVRT) imp_t;
  typedef uvmc_tlm_b_initiator_comp #(T,CVRT) this_type;
  uvm_tlm_b_initiator_socket #(T) init_skt;
  imp_t m_imp;
    function new(string name, uvm_component parent=null, imp_t imp=null);
    super.new(name, parent);
    init_skt = new(name, this);
    m_imp = imp;
  endfunction
  virtual function void resolve_bindings();
    m_imp.resolve_bindings(UVM_PORT,(1<<2)+
                                    (1<<0)+
                                    (1<<1));
    super.resolve_bindings();
          endfunction
endclass


class uvmc_tlm_nb_initiator_comp #(type T=uvm_tlm_generic_payload,
                                        P=uvm_tlm_phase_e,
                                        CVRT=uvmc_default_converter#(uvm_object)
                                        )
                               extends uvm_component;
  typedef uvmc_tlm2_dispatch #(T,P,CVRT) imp_t;
  typedef uvmc_tlm_nb_initiator_comp #(T,P,CVRT) this_type;
  uvm_tlm_nb_initiator_socket #(this_type,T,P) init_skt;
  imp_t m_imp;
  
  function new(string name, uvm_component parent=null, imp_t imp=null);
    super.new(name, parent);     init_skt = new(name, this);     m_imp = imp;
  endfunction

  virtual function void resolve_bindings();
    m_imp.resolve_bindings(UVM_PORT,(1<<2)+
                                    (1<<0)+
                                    (1<<1));
    super.resolve_bindings();
          endfunction
  function uvm_tlm_sync_e nb_transport_bw (T t,
                                           ref uvm_tlm_phase_e p,
                                           input uvm_tlm_time delay); 
            return m_imp.nb_transport_bw(t,p,delay);
  endfunction

endclass









class uvmc_tlm #(type T=uvm_tlm_generic_payload, P=uvm_tlm_phase_e,
                      CVRT=uvmc_default_converter#(uvm_object));
                      
  typedef uvm_port_base #(uvm_tlm_if #(T,P)) port_type;
  typedef uvmc_tlm2_port_proxy #(T,P,CVRT) proxy_type;
  typedef uvmc_tlm2_dispatch #(T,P,CVRT) x_dispatch_type;


                          
  static function void connect (port_type port,
                                string lookup_name="",
                                uvm_packer packer=null);

                        uvm_tlm_b_target_socket_base #(T) bt;
    uvm_tlm_b_initiator_socket_base #(T) bi;
    uvm_tlm_nb_target_socket_base #(T,P) nbt; 
    uvm_tlm_nb_initiator_socket_base #(T,P) nbi;
    uvm_tlm_nb_passthrough_initiator_socket_base #(T,P) nbpi;
    uvm_tlm_nb_passthrough_target_socket_base #(T,P) nbpt;
    uvm_tlm_b_passthrough_initiator_socket_base #(T) bpi;
    uvm_tlm_b_passthrough_target_socket_base #(T) bpt;


    x_dispatch_type m_x_dispatch;
    uvmc_report_catcher catcher;

    print_x_banner();

    if (!uvm_disable_ILLCRT) begin
      catcher = new();
      uvm_report_cb::add(null,catcher);
      uvm_disable_ILLCRT = 1;
    end

    if ($cast(bt,port) || $cast(bpt,port)) begin
        uvmc_tlm_b_initiator_comp #(T, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_B_INITIATOR_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.init_skt;
        comp.init_skt.connect(port);
        return;
    end
    else if ($cast(nbt,port) || $cast(nbpt,port)) begin
        uvmc_tlm_nb_initiator_comp #(T, P, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_NB_INITIATOR_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.init_skt;
        comp.init_skt.connect(port);
        return;
    end
    else if ($cast(bi,port) || $cast(bpi,port)) begin
        uvmc_tlm_b_target_comp #(T, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_B_TARGET_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.target_skt;
        port.connect(comp.target_skt);
        return;
    end
    else if ($cast(nbi,port) || $cast(nbpi,port)) begin
        uvmc_tlm_nb_target_comp #(T, P, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_NB_TARGET_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.target_skt;
        port.connect(comp.target_skt);
        return;
    end

                    
    if (port.is_port()) begin
      proxy_type proxy = new(port, lookup_name, UVM_IMPLEMENTATION, packer);
      port.connect(proxy);
    end
    else begin
      proxy_type proxy = new(port, lookup_name, UVM_PORT, packer);
      proxy.connect(port);
    end
  endfunction


                          
  static function void connect_hier (port_type port,
                                     string lookup_name="",
                                     uvm_packer packer=null);

            uvm_tlm_b_target_socket_base #(T) bt;
    uvm_tlm_b_initiator_socket_base #(T) bi;
    uvm_tlm_nb_target_socket_base #(T,P) nbt; 
    uvm_tlm_nb_initiator_socket_base #(T,P) nbi;

    uvm_tlm_nb_passthrough_initiator_socket_base #(T,P) nbpi;
    uvm_tlm_nb_passthrough_target_socket_base #(T,P) nbpt;
    uvm_tlm_b_passthrough_initiator_socket_base #(T) bpi;
    uvm_tlm_b_passthrough_target_socket_base #(T) bpt;


    x_dispatch_type m_x_dispatch;
    uvmc_report_catcher catcher;

    print_x_banner();

    if (!uvm_disable_ILLCRT) begin
      catcher = new();
      uvm_report_cb::add(null,catcher);
      uvm_disable_ILLCRT = 1;
    end


    if ($cast(bpt,port)) begin
        uvmc_tlm_b_target_comp #(T, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_B_TARGET_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.target_skt;
        port.connect(comp.target_skt);
        return;
    end
    else if ($cast(nbpt,port)) begin
        uvmc_tlm_nb_target_comp #(T, P, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_NB_TARGET_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.target_skt;
        port.connect(comp.target_skt);
        return;
    end
    else if ($cast(bpi,port)) begin
        uvmc_tlm_b_initiator_comp #(T, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_B_INITIATOR_SOCKET_FOR_",
                   port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.init_skt;
        comp.init_skt.connect(port);
        return;
    end
    else if ($cast(nbpi,port)) begin
        uvmc_tlm_nb_initiator_comp #(T, P, CVRT) comp;
        m_x_dispatch = new(port.get_full_name(), lookup_name, packer, null);
        comp = new({"UVMC_COMP_WITH_NB_INITIATOR_SOCKET_FOR_",
               port.get_full_name()},null,m_x_dispatch);
        m_x_dispatch.m_imp = comp.init_skt;
        comp.init_skt.connect(port);
        return;
    end

    if ($cast(nbpi,port) || $cast(bpt,port) ||
        $cast(nbpt,port) || $cast(bpi,port)) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 892); 
   end
;
    end

            if (port.is_port()) begin
      proxy_type proxy = new(port, lookup_name, UVM_PORT, packer);
      proxy.connect(port);
    end
    else if (port.is_export()) begin
      proxy_type proxy = new(port, lookup_name, UVM_IMPLEMENTATION, packer);
      port.connect(proxy);
    end
    else begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_tlm2.sv", 908); 
   end
;
    end

  endfunction


endclass



/* SLline 73 "uvmc-2.2/src/connect/sv/uvmc_pkg.sv" 2 */
/* SLline 1 "uvmc-2.2/src/connect/sv/uvmc_commands.sv" 1 */



export "DPI-C" function UVMC_wait_for_phase_request;
export "DPI-C" function UVMC_raise_objection;
export "DPI-C" function UVMC_drop_objection;

export "DPI-C" function UVMC_print_topology;

export "DPI-C" function UVMC_set_report_verbosity;
export "DPI-C" function UVMC_report_enabled;
export "DPI-C" function UVMC_report;

export "DPI-C" function UVMC_set_config_int;
export "DPI-C" function UVMC_set_config_object;
export "DPI-C" function UVMC_set_config_string;

export "DPI-C" function UVMC_get_config_int;
export "DPI-C" function UVMC_get_config_object;
export "DPI-C" function UVMC_get_config_string;

export "DPI-C" function UVMC_print_factory;
export "DPI-C" function UVMC_set_factory_inst_override;
export "DPI-C" function UVMC_set_factory_type_override;
export "DPI-C" function UVMC_debug_factory_create;
export "DPI-C" function UVMC_find_factory_override;

import "DPI-C" context function bit SV2C_phase_notification(int id);
import "DPI-C" context function bit SV2C_sv_ready();


export "DPI-C" function UVMC_get_uvm_version;

export "DPI-C" function UVMC_global_stop_request; 

bit sv_is_ready = SV2C_sv_ready();




function automatic uvm_component get_context (string contxt,
                                              string cmd,
                                              int err=0);
  uvm_root top = uvm_root::get();
  if (contxt == "")
    get_context = top;
  else begin
    uvm_component comps[$];
    int sz;
    top.find_all(contxt,comps);
    sz=comps.size();
    if (sz == 0) begin
      if (err == 2)
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 80); 
   end


      else if (err == 1)
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_WARNING,"UVMC")) 
       ovm_report_warning ("UVMC", {"Making local SV connection between '",
                   exist_port.m_port_name,"' and '", port_name}, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 82); 
   end


      return null;
    end
    if (sz > 1) begin
      if (err == 2)
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 87); 
   end


      else if (err == 1)
        
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_WARNING,"UVMC")) 
       ovm_report_warning ("UVMC", {"Making local SV connection between '",
                   exist_port.m_port_name,"' and '", port_name}, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 89); 
   end


    end
    get_context = comps[0];
  end
endfunction



class uvm_domain;
  function uvm_phase find_by_name(string ph_name, bit stay_in_domain);
    ovm_root top;
    top = ovm_root::get();     case (ph_name)
      "build"               : return build_ph;
      "connect"             : return connect_ph;
      "end_of_elaboration"  : return end_of_elaboration_ph;
      "start_of_simulation" : return start_of_simulation_ph;
      "run"                 : return run_ph;
      "extract"             : return extract_ph;
      "check"               : return check_ph;
      "report"              : return report_ph;
      default               : return null;
    endcase
  endfunction
endclass



class uvmc_wait_for_phase_info;
  uvm_phase phase;
  uvm_phase_state state;
  uvm_wait_op op;
  int id;
endclass

uvmc_wait_for_phase_info uvmc_wait_for_phase_q[$];


class uvmc_drop_objection_info;
  uvm_objection objection;
  string description;
  int count;
  uvm_component comp;
endclass

uvmc_drop_objection_info uvmc_drop_objection_q[$];




function automatic int UVMC_wait_for_phase_request(string ph_name,
                                                   int state,
                                                   int op);
    uvm_phase_state state_e;
  uvm_phase_state curr_state_e;
  uvm_wait_op op_e;
  uvm_domain dom;
  uvm_phase ph;
  static int id;
  uvmc_wait_for_phase_info info;
  info = new();
    dom = new;
    ph = dom.find_by_name(ph_name,0);
  state_e = uvm_phase_state'(state);
  op_e = uvm_wait_op'(op);
  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 169); 
   end


  if (ph == null) begin
    
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 175); 
   end


    return -1;
  end
  else begin
    
    if (ph.is_done())
      curr_state_e = UVM_PHASE_DONE;
    else if (ph.is_in_progress())
      curr_state_e = UVM_PHASE_EXECUTING;
    else
      curr_state_e = UVM_PHASE_DORMANT;

    if ((curr_state_e > state_e) && (op <= UVM_EQ)) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 192); 
   end


    end

    if (state_e != UVM_PHASE_DORMANT &&
        state_e != UVM_PHASE_STARTED &&
        state_e != UVM_PHASE_EXECUTING &&
        state_e != UVM_PHASE_ENDED &&
        state_e != UVM_PHASE_DONE) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 202); 
   end


      return -1;
    end
        
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 208); 
   end


  end
  info.phase = ph;
  info.state = state_e;
  info.op = op_e;
  info.id = ++id;
  uvmc_wait_for_phase_q.push_back(info);
  return info.id;
endfunction





task uvmc_init();
  fork
    m_uvmc_wait_for_phase_proc();
    m_uvmc_drop_objection_proc();
  join_none
endtask


function void UVMC_get_uvm_version (output int unsigned major,
                                    output int unsigned minor,
                                    output string fix);
  major = 2;;
  minor = 1;;
  fix   = "`UVM_FIX_REV";
  endfunction





task automatic m_uvmc_wait_for_phase_proc();
  bit never_trig;
  forever begin
    uvmc_wait_for_phase_info info;
    if (uvmc_wait_for_phase_q.size()==0)
      @(uvmc_wait_for_phase_q.size()!=0);
    info = uvmc_wait_for_phase_q.pop_front();
    assert(info != null);
    fork begin
              if ((info.state == UVM_PHASE_DONE && info.op == UVM_GT) ||
            (info.state == UVM_PHASE_DORMANT && info.op == UVM_LT) ||
            (
              info.phase.is_done() &&
                (
                 (info.state != UVM_PHASE_DONE && (info.op == UVM_LT || info.op == UVM_LTE || info.op == UVM_EQ)) ||
                 (info.state == UVM_PHASE_DONE && (info.op == UVM_LT || info.op == UVM_NE))
                )
            ) ||
            (
              info.phase.is_in_progress() &&
                (
                  (info.state == UVM_PHASE_DORMANT   && (info.op == UVM_LT || info.op == UVM_LTE || info.op == UVM_EQ)) ||
                  (info.state == UVM_PHASE_STARTED   && (info.op == UVM_LT || info.op == UVM_LTE || info.op == UVM_EQ)) ||
                  (info.state == UVM_PHASE_EXECUTING && (info.op == UVM_LT))
                )
            )
           )
           never_trig = 1;

        if (info.phase.is_in_progress()) begin
          if (
              (info.state == UVM_PHASE_EXECUTING && (info.op == UVM_NE || info.op == UVM_GT)) ||
              (info.state == UVM_PHASE_ENDED     && (info.op == UVM_EQ || info.op == UVM_GTE || info.op == UVM_GT)) ||
              (info.state == UVM_PHASE_DONE      && (info.op == UVM_EQ || info.op == UVM_GTE))
             )
            info.phase.wait_done();
        end
  
        if ((!info.phase.is_in_progress() && !info.phase.is_done())) begin
          if (
              (info.state == UVM_PHASE_DORMANT   && (info.op == UVM_NE || info.op == UVM_GT )) ||
              (info.state == UVM_PHASE_STARTED   && (info.op == UVM_EQ || info.op == UVM_GTE || info.op == UVM_GT)) ||
              (info.state == UVM_PHASE_EXECUTING && (info.op == UVM_EQ || info.op == UVM_GTE))
             )
            info.phase.wait_start();
          if (
              (info.state == UVM_PHASE_EXECUTING && info.op == UVM_GT) ||
              (info.state == UVM_PHASE_ENDED     && (info.op == UVM_EQ || info.op == UVM_GTE)) ||
              (info.state == UVM_PHASE_DONE      && (info.op == UVM_EQ || info.op == UVM_GTE))
             )
            info.phase.wait_done();
        end
            if (!never_trig)
        void'(SV2C_phase_notification(info.id));
    end
    join_none
  end
endtask





function automatic void m_uvmc_objection_op (string op,
                                      string name,
                                      string contxt,
                                      string description,
                                      int unsigned count);
  uvm_component comp = get_context(contxt,{"UVMC_",op,"_OBJECTION"},0); 
  string nm;
      ovm_objection ph;
    if (comp == null)
    comp = uvm_root::get();
  nm = comp.get_full_name();
  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 371); 
   end


      if (name != "run") begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 376); 
   end


      return;
    end
    ph = ovm_test_done;

    description = {contxt,": ",description};
          if (op == "DROP") begin
    uvmc_drop_objection_info info = new;
      info.objection = ph;
                info.description = description;
    info.count = count;
    info.comp = comp;
    uvmc_drop_objection_q.push_back(info);
  end
  else begin     ph.raise_objection(comp,count);
  end
  endfunction


function automatic void UVMC_raise_objection (string name,
                                      string contxt,
                                      string description,
                                      int unsigned count);
   m_uvmc_objection_op("RAISE",name,contxt,description,count); 
endfunction

function automatic void UVMC_drop_objection (string name,
                                     string contxt,
                                     string description,
                                     int unsigned count);
   m_uvmc_objection_op("DROP",name,contxt,description,count); 
endfunction



task automatic m_uvmc_drop_objection_proc();
  forever begin
    uvmc_drop_objection_info info;
    if (uvmc_drop_objection_q.size()==0)
      @(uvmc_drop_objection_q.size()!=0);
    info = uvmc_drop_objection_q.pop_front();
    assert(info != null);
        info.objection.drop_objection(info.comp,info.count);
      end
endtask



function void UVMC_global_stop_request();
  global_stop_request();
endfunction





function automatic void UVMC_print_topology(string contxt, int depth);
  uvm_root top = uvm_root::get();
  uvm_component comps[$];
  uvm_printer printer;
  int depth_save;
      printer = ovm_default_printer;
    if (contxt == "")
    comps.push_back(top);
  else begin
    top.find_all(contxt,comps);
    
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 481); 
   end


    return;
  end
    depth_save = printer.knobs.depth;
    printer.knobs.depth = depth;
  foreach (comps[i]) begin
    string name = comps[i].get_full_name();
    if (name == "")
      name = "uvm_top";
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 491); 
   end


    comps[i].print(printer);
    $display();
  end
endfunction





function automatic bit UVMC_report_enabled (string contxt,
                                            int verbosity,
                                            int severity,
                                            string id);
  uvm_root top = uvm_root::get();
  uvm_component comp = get_context(contxt, "UVMC_REPORT_ENABLED");
  if (comp == null)
    comp = top;
      UVMC_report_enabled = comp.ovm_report_enabled(verbosity,UVM_INFO,id);
    if ($test$plusargs("UVMC_COMMAND_TRACE")) begin
    uvm_severity_type sev = uvm_severity_type'(severity);
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 526); 
   end


  end
endfunction


function automatic void UVMC_report(int severity,
			            string id,
                                    string message,
                                    int verbosity,
                                    string contxt,
			            string filename,
			            int line);
  uvm_root top = uvm_root::get();
    if ($test$plusargs("UVMC_COMMAND_TRACE")) begin
    uvm_severity_type sev = uvm_severity_type'(severity);
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 545); 
   end


  end
  top.m_rh.report(severity, contxt, id, message, verbosity, filename, line, top);
endfunction



function automatic void UVMC_set_report_verbosity (int level,
                                                   string contxt,
                                                   bit recurse);
  uvm_component comp = get_context(contxt, "UVMC_SET_VERB");
  if (comp == null) begin
    return;
  end
  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 564); 
   end


  if (recurse)
    comp.set_report_verbosity_level_hier(level);
  else
    comp.set_report_verbosity_level(level);
  
endfunction








function void UVMC_set_config_int (string contxt,
                                   string inst_name,
                                   string field_name,
                                   longint unsigned value);
  uvm_component comp;
  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 613); 
   end


  
      if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
    set_config_int (inst_name, field_name, value);
  
     
endfunction

static uvm_packer uvmc_default_packer = new();


function void UVMC_set_config_string (string contxt,
                                      string inst_name,  
                                      string field_name,
                                      string value);
  uvm_component comp;

  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 655); 
   end



    
      if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
    set_config_string (inst_name, field_name, value);
  
  
endfunction

function void UVMC_set_config_object (string type_name,
                                      string contxt,
                                      string inst_name,
                                      string field_name,
                                      bits_t value);
  typedef uvmc_default_converter #(uvm_object) converter;
  uvm_object obj;
  uvm_component comp;

  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 699); 
   end



  
  if (comp == null) begin
    if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
  end

  obj = factory.create_object_by_name(type_name,contxt);
  if (obj == null) begin
    
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 716); 
   end


    return;
  end
  uvmc_default_packer.use_metadata = 1;
  uvmc_default_packer.big_endian = 0;
  converter::m_pre_unpack(value,obj,uvmc_default_packer);
  converter::do_unpack(obj,uvmc_default_packer);
  converter::m_post_unpack(obj,uvmc_default_packer);

  
      set_config_object (inst_name, field_name, obj, 0);
  
  endfunction




function bit  UVMC_get_config_int  (string contxt,
                                    string inst_name,
                                    string field_name,
                                    output longint unsigned value);
  uvm_component comp;

  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 755); 
   end



          if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
    comp = get_context(inst_name, "UVMC_GET_CFG_INT", 2);
    $display("comp=%p",comp);
    if (comp != null)
      return comp.get_config_int (field_name, value);
    return 0;
  
endfunction


function bit UVMC_get_config_string (string contxt,
                                     string inst_name,  
                                     string field_name,
                                     output string value);
  uvm_component comp;

  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 793); 
   end



          if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
    comp = get_context(inst_name, "UVMC_GET_CFG_STR", 2);
    if (comp != null)
      return comp.get_config_string (field_name, value);
    return 0;
  
endfunction


function bit UVMC_get_config_object (string type_name,
                                     string contxt,
                                     string inst_name,
                                     string field_name,
                                     output bits_t value);
  typedef uvmc_default_converter #(uvm_object) converter;
  uvm_object obj;
  uvm_component comp;

  if ($test$plusargs("UVMC_COMMAND_TRACE"))
    
   begin 
     if (ovm_report_enabled(UVM_NONE,OVM_INFO,"TRACE/UVMC_CMD/WAIT_FOR_PHASE")) 
       ovm_report_info ("TRACE/UVMC_CMD/WAIT_FOR_PHASE", 
        $sformatf("ph_name=%s state=%s op=%s %s",
          ph_name,state_e.name(),
          op_e.name(),
          (ph==null?"(unknown phase)":"")), UVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 833); 
   end



          if (inst_name == "")
      inst_name = contxt;
    else if (contxt != "")
      inst_name = {contxt, ".", inst_name};
    comp = get_context(inst_name, "UVMC_GET_CFG_OBJ", 2);
    if (comp == null || !comp.get_config_object (field_name, obj, 0)) begin
      
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 859); 
   end


      return 0;
    end
  
  if (type_name != obj.get_type_name()) begin
    
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"UVMC")) 
       ovm_report_error ("UVMC", {"Cannot bind SV-side UVMC proxy with name '",
                           m_port_name,"'", m_lookup_name==""?"":
                           {" or its alternative lookup name, '",
                           m_lookup_name,"' (mask=",$sformatf("%0h",if_mask)} }, OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/uvmc-2.2/src/connect/sv/uvmc_commands.sv", 866); 
   end


    return 0;
  end
  uvmc_default_packer.use_metadata = 1;
  uvmc_default_packer.big_endian = 0;
  converter::m_pre_pack(obj,uvmc_default_packer);
  converter::do_pack(obj,uvmc_default_packer);
  converter::m_post_pack(value,obj,uvmc_default_packer);
  return 1;
endfunction




function automatic void UVMC_print_factory (int all_types=1);
  uvm_factory factory = uvm_factory::get();
  factory.print(all_types);
endfunction


function automatic void UVMC_set_factory_inst_override (string requested_type,
                                                        string override_type,
                                                        string contxt);
  uvm_factory factory = uvm_factory::get();
  factory.set_inst_override_by_name(requested_type,override_type,contxt);
endfunction


function automatic void UVMC_set_factory_type_override (string requested_type,
                                                        string override_type,
                                                        bit replace=1);
  uvm_factory factory = uvm_factory::get();
  factory.set_type_override_by_name(requested_type,override_type,replace);
endfunction


function automatic void UVMC_debug_factory_create (string requested_type,
                                                   string contxt="");
  uvm_factory factory = uvm_factory::get();
  factory.debug_create_by_name(requested_type,contxt,"");
endfunction


function automatic void UVMC_find_factory_override (string requested_type,
                                                    string contxt,
                                                    output string override_type);
  uvm_object_wrapper wrapper;
  uvm_factory factory = uvm_factory::get();
  wrapper = factory.find_override_by_name(requested_type, contxt);
  if (wrapper == null)
    override_type = requested_type;
  else
    override_type = wrapper.get_type_name();
endfunction





/* SLline 74 "uvmc-2.2/src/connect/sv/uvmc_pkg.sv" 2 */

endpackage : uvmc_pkg



/* SLline 30 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */

    
package amiq_eth_ve_pkg;
    import uvm_pkg::*;
    import uvmc_pkg::*;
    import amiq_eth_pkg::*;
    
    /* SLline 1 "./ve/sv/amiq_eth_ve_producer.sv" 1 */


		
class amiq_eth_ve_producer extends uvm_component;
	
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


		uvm_tlm_b_initiator_socket #() out_sv2sc;

	    uvm_analysis_port#(amiq_eth_packet) out_sv2sv;

        	virtual function string get_id();
		return "AMIQ_ETH";
	endfunction

				function new(string name = "", uvm_component parent);
		super.new(name, parent);
		out_sv2sc = new("out_sv2sc", this);
		out_sv2sv = new("out_sv2sv", this);
	endfunction
	
			virtual task send_to_sc(amiq_eth_packet packet);
		uvm_tlm_gp gp;
		uvm_tlm_time delay = new("delay",0);

		
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_producer.sv", 57); 
   end
;

		gp = packet.to_generic_payload();


		out_sv2sv.write(packet);

		out_sv2sc.b_transport(gp,delay);
	endtask
endclass


/* SLline 42 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./ve/sv/amiq_eth_ve_consumer.sv" 1 */


        
class amiq_eth_ve_consumer extends uvm_component;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


            virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction

        uvm_tlm_b_target_socket #(amiq_eth_ve_consumer) in_sc2sv;

        uvm_analysis_port#(amiq_eth_packet) out_sv2sv;

                function new(string name = "", uvm_component parent);
        super.new(name, parent);
        in_sc2sv = new("in_sc2sv", this);
        out_sv2sv = new("out_sv2sv", this);
    endfunction

                virtual function amiq_eth_packet get_packet_by_code(bit[63:0] code);
        if(code == 32'h0000_0002) begin
            amiq_eth_packet_snap packet = amiq_eth_packet_snap::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0001) begin
            amiq_eth_packet_jumbo packet = amiq_eth_packet_jumbo::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0000) begin
            amiq_eth_packet_magic packet = amiq_eth_packet_magic::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0003) begin
            amiq_eth_packet_pause packet = amiq_eth_packet_pause::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0004) begin
            amiq_eth_packet_pfc_pause packet = amiq_eth_packet_pfc_pause::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0006) begin
            amiq_eth_packet_ethernet_configuration_testing packet = amiq_eth_packet_ethernet_configuration_testing::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0007) begin
            amiq_eth_packet_ipv4 packet = amiq_eth_packet_ipv4::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0008) begin
            amiq_eth_packet_hsr_standard packet= amiq_eth_packet_hsr_standard::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_000A) begin
            amiq_eth_packet_fcoe packet= amiq_eth_packet_fcoe::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_0009) begin
            amiq_eth_packet_arp packet= amiq_eth_packet_arp::type_id::create("packet");
            return packet;
        end
        else if(code == 32'h0000_000C) begin
            amiq_eth_packet_ptp packet= amiq_eth_packet_ptp::type_id::create("packet");
            return packet;
        end
        else begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_consumer.sv", 100); 
   end

        end
    endfunction

                virtual function void unpack_gp_to_eth(ref uvm_tlm_gp gp, ref amiq_eth_packet packet);
        byte unsigned bytestream[];
        gp.get_data(bytestream);
        
        void'(packet.unpack_bytes(bytestream));
    endfunction
    
            virtual function void handle_incomming_gp(uvm_tlm_gp gp);
        amiq_eth_packet packet = get_packet_by_code(gp.get_address());
        unpack_gp_to_eth(gp, packet);
        out_sv2sv.write(packet);
    endfunction
    
                virtual task b_transport (uvm_tlm_gp t, uvm_tlm_time delay);
        handle_incomming_gp(t);
    endtask

endclass


/* SLline 43 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./ve/sv/amiq_eth_ve_scoreboard.sv" 1 */


        
/* SLline 491 "../../../UVM/uvm-1.2/src/macros/uvm_tlm_defines.svh" 0 */
class uvm_analysis_imp_from_producer #(type T=int, type IMP=int) 
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); 
  
  local IMP m_imp; 
  function new (string name, IMP imp); 
    super.new (name, imp, UVM_IMPLEMENTATION, 1, 1); 
    m_imp = imp; 
    m_if_mask = (1<<8); 
  endfunction 
  
  virtual function string get_type_name(); 
    return "uvm_analysis_imp_from_producer"; 
  endfunction

 
  function void write( input T t); 
    m_imp.write_from_producer( t); 
  endfunction 
  
endclass
/* SLline 28 "./ve/sv/amiq_eth_ve_scoreboard.sv" 0 */
/* SLline 491 "../../../UVM/uvm-1.2/src/macros/uvm_tlm_defines.svh" 0 */
class uvm_analysis_imp_from_producer #(type T=int, type IMP=int) 
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); 
  
  local IMP m_imp; 
  function new (string name, IMP imp); 
    super.new (name, imp, UVM_IMPLEMENTATION, 1, 1); 
    m_imp = imp; 
    m_if_mask = (1<<8); 
  endfunction 
  
  virtual function string get_type_name(); 
    return "uvm_analysis_imp_from_producer"; 
  endfunction

 
  function void write( input T t); 
    m_imp.write_from_producer( t); 
  endfunction 
  
endclass
/* SLline 29 "./ve/sv/amiq_eth_ve_scoreboard.sv" 0 */

class amiq_eth_ve_scoreboard extends uvm_component;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 

    
    virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction
    
    bit has_checks = 1;
    
    amiq_eth_packet producer_packets[$];
    
    amiq_eth_packet received_packet;

    uvm_analysis_imp_from_producer#(amiq_eth_packet, amiq_eth_ve_scoreboard) input_port_from_producer;
    uvm_analysis_imp_from_consumer#(amiq_eth_packet, amiq_eth_ve_scoreboard) input_port_from_consumer;
    
                function new(string name = "", uvm_component parent);
        super.new(name, parent);
        input_port_from_producer = new("input_port_from_producer", this);
        input_port_from_consumer = new("input_port_from_consumer", this);
    endfunction
    
            virtual function void write_from_producer(amiq_eth_packet packet);
        if(has_checks == 1) begin
            producer_packets.push_back(packet);
        end
    endfunction
    
            virtual function void write_from_consumer(amiq_eth_packet local_received_packet);
        received_packet = local_received_packet;
        if(has_checks == 1) begin
            if(producer_packets.size() == 0) begin
                
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,"AMIQ_ETH")) 
       ovm_report_fatal ("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_scoreboard.sv", 70); 
   end
    
            end
            
            begin
                amiq_eth_packet expected_packet = producer_packets.pop_front();
                
                if(expected_packet.compare(local_received_packet) == 0) begin
                    
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_scoreboard.sv", 77); 
   end
;
                end
                else begin
                    
   begin 
     if (ovm_report_enabled(UVM_HIGH,OVM_INFO,"AMIQ_ETH")) 
       ovm_report_info ("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_scoreboard.sv", 81); 
   end

                end
            end
        end
    endfunction
    
            virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
    
        if(producer_packets.size() != 0) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/ve/sv/amiq_eth_ve_scoreboard.sv", 93); 
   end
    
        end
    endfunction
    
endclass


/* SLline 44 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./ve/sv/amiq_eth_ve_env.sv" 1 */


        
class amiq_eth_ve_env extends uvm_component;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 

    
        amiq_eth_ve_producer producer;
    
        amiq_eth_ve_consumer consumer;
    
        amiq_eth_ve_scoreboard scoreboard;
    
            task set(amiq_eth_packet packet);
        producer.send_to_sc(packet);
    endtask
    
            function amiq_eth_packet get();
        return scoreboard.received_packet;
    endfunction
    
            virtual function string get_id();
        return "AMIQ_ETH_VE";
    endfunction
    
                function new(string name = "", uvm_component parent);
        super.new(name, parent);    
    endfunction
    
            function void build_phase(uvm_phase phase);
        super.build();
        producer = amiq_eth_ve_producer::type_id::create("producer", this);
        consumer = amiq_eth_ve_consumer::type_id::create("consumer", this);
        scoreboard = amiq_eth_ve_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
            function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        uvmc_tlm #()::connect(producer.out_sv2sc, "sv2sc_connection");
        uvmc_tlm #()::connect(consumer.in_sc2sv, "sc2sv_connection");
        
        producer.out_sv2sv.connect(scoreboard.input_port_from_producer);
        consumer.out_sv2sv.connect(scoreboard.input_port_from_consumer);
    endfunction
endclass


/* SLline 45 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_basic.sv" 1 */


           
class amiq_eth_ve_test_basic extends uvm_test;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 

    
        amiq_eth_ve_env env;
    
                function new(string name = "", uvm_component parent);
        super.new(name, parent);    
    endfunction
    
            function void build_phase(uvm_phase phase);
        env = amiq_eth_ve_env::type_id::create("env", this);
    endfunction
endclass

    
/* SLline 46 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_packets.sv" 1 */


        
virtual class amiq_eth_ve_test_packets extends amiq_eth_ve_test_basic;
    
    int unsigned number_of_packets = 1000;

                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction
    
            pure virtual function amiq_eth_packet generate_random_packet();

            task run_phase(uvm_phase phase);
        integer file_txt = $fopen("wireshark_file.txt"); 
        amiq_eth_pcap_livestream livestream = new("wireshark_file");
        phase.raise_objection(this, "Start of test");
        begin
            for(int i = 0; i < number_of_packets; i++) begin
                amiq_eth_packet packet = generate_random_packet();
                $fdisplay(file_txt, {packet.to_wireshark_string(),"\n"});
                livestream.broadcast(packet);
                env.set(packet);
            end
        end
        
        $fclose(file_txt);
        livestream.stop();

        #100;
        phase.drop_objection(this, "Start of test");
    endtask    
endclass


/* SLline 47 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_magic_packets.sv" 1 */


        
class amiq_eth_ve_test_magic_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_magic result = amiq_eth_packet_magic::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_magic_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 48 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_jumbo_packets.sv" 1 */


        
class amiq_eth_ve_test_jumbo_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_jumbo result = amiq_eth_packet_jumbo::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_jumbo_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 49 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_snap_packets.sv" 1 */


        
class amiq_eth_ve_test_snap_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_snap result = amiq_eth_packet_snap::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_snap_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 50 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_pause_packets.sv" 1 */


        
class amiq_eth_ve_test_pause_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_pause result = amiq_eth_packet_pause::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_pause_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 51 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_pfc_pause_packets.sv" 1 */


        
class amiq_eth_ve_test_pfc_pause_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_pfc_pause result = amiq_eth_packet_pfc_pause::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_pfc_pause_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 52 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_ipv4_packets.sv" 1 */


        
class amiq_eth_ve_test_ipv4_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_ipv4 result = amiq_eth_packet_ipv4::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_ipv4_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 53 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_ethernet_configuration_testing_packets.sv" 1 */


        
class amiq_eth_ve_test_ethernet_configuration_testing_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_ethernet_configuration_testing result = amiq_eth_packet_ethernet_configuration_testing::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_ethernet_configuration_testing_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 54 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_hsr_standard_packets.sv" 1 */


        
class amiq_eth_ve_test_hsr_standard_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_hsr_standard result = amiq_eth_packet_hsr_standard::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_hsr_standard_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 55 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_fcoe_packets.sv" 1 */


            
class amiq_eth_ve_test_fcoe_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_fcoe result = amiq_eth_packet_fcoe::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_fcoe_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 56 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_arp_packets.sv" 1 */


        
class amiq_eth_ve_test_arp_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_arp result = amiq_eth_packet_arp::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_arp_packets.sv", 42); 
   end
;
        end
       
        return result;
    endfunction

endclass


/* SLline 57 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    /* SLline 1 "./tests/amiq_eth_ve_test_ptp_packets.sv" 1 */


        
class amiq_eth_ve_test_ptp_packets extends amiq_eth_ve_test_packets;
    
   
   typedef uvm_component_registry #(amiq_eth_ve_producer,"amiq_eth_ve_producer") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "amiq_eth_ve_producer"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


                function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction

            virtual function amiq_eth_packet generate_random_packet();
        amiq_eth_packet_ptp result = amiq_eth_packet_ptp::type_id::create("packet");

        if(!result.randomize()) begin
            
   begin 
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,"AMIQ_ETH")) 
       ovm_report_error ("AMIQ_ETH", $sformatf("Length is too short: %0d", length), OVM_NONE, "/home/alain/surelog/SVIncCompil/Testcases/AmiqEth/tests/amiq_eth_ve_test_ptp_packets.sv", 42); 
   end
;
        end
        
        return result;
    endfunction

endclass


/* SLline 58 "./ve/sv/amiq_eth_ve_pkg.sv" 2 */
    
endpackage 

    
/* SLline 27 "ve/sv/amiq_eth_ve_top.v" 2 */

import uvm_pkg::*;
import amiq_eth_ve_pkg::*;

//top module for starting the UVM flow
module amiq_eth_ve_top;
	initial begin
		run_test();	
	end
endmodule

	