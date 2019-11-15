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
 * NAME:        amiq_eth_packet_ptp.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Precision Time Protocol packet. 
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_PTP
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_PTP

//Ethernet Precision Time Protocol packet header
class amiq_eth_packet_ptp_header extends uvm_object;
    `uvm_object_utils(amiq_eth_packet_ptp_header)

    //Header
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

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
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
        source_port_identity = new[`AMIQ_ETH_PTP_SOURCE_PORT_IDENTITY_SIZE];
        ptp_reserved_1 = new[`AMIQ_ETH_PTP_RESERVED_1_WIDTH];
        foreach (ptp_reserved_1[i]) begin
            ptp_reserved_1[i] = 0;
        end
        ptp_reserved_2 = new[`AMIQ_ETH_PTP_RESERVED_2_WIDTH];
        foreach (ptp_reserved_2[i]) begin
            ptp_reserved_2[i] = 0;
        end
        ptp_reserved_3 = new[`AMIQ_ETH_PTP_RESERVED_3_WIDTH];
        foreach (ptp_reserved_3[i]) begin
            ptp_reserved_3[i] = 0;
        end
        print_lists = 0;
    endfunction

	//pack Ethernet PTP header
    //@param packer - the packer used by this function
    //@param local_pack_transport_specific - boolean to control if to pack or not the "transport_specific" field
    //@param local_pack_message_type - boolean to control if to pack or not the "message_type" field
    //@param local_pack_ptp_reserved_1 - boolean to control if to pack or not the "ptp_reserved_1" field
    //@param local_pack_version - boolean to control if to pack or not the "version" field
    //@param local_pack_message_length - boolean to control if to pack or not the "message_length" field
    //@param local_pack_domain_number - boolean to control if to pack or not the "domain_number" field
    //@param local_pack_ptp_reserved_2 - boolean to control if to pack or not the "ptp_reserved_2" field
    //@param local_pack_flags - boolean to control if to pack or not the "flags" field
    //@param local_pack_correction_field - boolean to control if to pack or not the "correction_field" field
    //@param local_pack_ptp_reserved_3 - boolean to control if to pack or not the "ptp_reserved_3" field
    //@param local_pack_source_port_identity - boolean to control if to pack or not the "source_port_identity" field
    //@param local_pack_sequence_id - boolean to control if to pack or not the "sequence_id" field
    //@param local_pack_control_field - boolean to control if to pack or not the "control_field" field
    //@param local_pack_log_message - boolean to control if to pack or not the "log_message" field
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
            `uvm_pack_enum(transport_specific);
        end

        if (local_pack_message_type) begin
            `uvm_pack_enum(message_type);
        end

        if (local_pack_ptp_reserved_1) begin
            `uvm_pack_array(ptp_reserved_1);
        end

        if (local_pack_version) begin
            `uvm_pack_int(version);
        end

        if (local_pack_message_length) begin
            `uvm_pack_int(message_length);
        end

        if (local_pack_domain_number) begin
            `uvm_pack_int(domain_number);
        end

        if (local_pack_ptp_reserved_2) begin
            `uvm_pack_array(ptp_reserved_2);
        end

        if (local_pack_flags) begin
            `uvm_pack_int(flags);
        end

        if (local_pack_correction_field) begin
            `uvm_pack_int(correction_field);
        end

        if (local_pack_ptp_reserved_3) begin
            `uvm_pack_array(ptp_reserved_3);
        end

        if (local_pack_source_port_identity) begin
            `uvm_pack_array(source_port_identity);
        end

        if (local_pack_sequence_id) begin
            `uvm_pack_int(sequence_id);
        end

        if (local_pack_control_field) begin
            `uvm_pack_enum(control_field);
        end

        if (local_pack_log_message) begin
            `uvm_pack_int(log_message);
        end
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_header_with_options(packer, pack_transport_specific, pack_message_type, pack_ptp_reserved_1, pack_version, pack_message_length, pack_domain_number, pack_ptp_reserved_2, pack_flags, pack_correction_field, pack_ptp_reserved_3, pack_source_port_identity, pack_sequence_id, pack_control_field, pack_log_message);
    endfunction

	//unpack Ethernet PTP header
    //@param packer - the packer used by this function
    //@param local_pack_transport_specific - boolean to control if to unpack or not the "transport_specific" field
    //@param local_pack_message_type - boolean to control if to unpack or not the "message_type" field
    //@param local_pack_ptp_reserved_1 - boolean to control if to unpack or not the "ptp_reserved_1" field
    //@param local_pack_version - boolean to control if to unpack or not the "version" field
    //@param local_pack_message_length - boolean to control if to unpack or not the "message_length" field
    //@param local_pack_domain_number - boolean to control if to unpack or not the "domain_number" field
    //@param local_pack_ptp_reserved_2 - boolean to control if to unpack or not the "ptp_reserved_2" field
    //@param local_pack_flags - boolean to control if to unpack or not the "flags" field
    //@param local_pack_correction_field - boolean to control if to unpack or not the "correction_field" field
    //@param local_pack_ptp_reserved_3 - boolean to control if to unpack or not the "ptp_reserved_3" field
    //@param local_pack_source_port_identity - boolean to control if to unpack or not the "source_port_identity" field
    //@param local_pack_sequence_id - boolean to control if to unpack or not the "sequence_id" field
    //@param local_pack_control_field - boolean to control if to unpack or not the "control_field" field
    //@param local_pack_log_message - boolean to control if to unpack or not the "log_message" field
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
            `uvm_unpack_enum(transport_specific,amiq_eth_ptp_transport_specific);
        end

        if (local_pack_message_type) begin
            `uvm_unpack_enum(message_type,amiq_eth_ptp_message_type);
        end

        if (local_pack_ptp_reserved_1) begin
            `uvm_unpack_array(ptp_reserved_1);
        end

        if (local_pack_version) begin
            `uvm_unpack_int(version);
        end

        if (local_pack_message_length) begin
            `uvm_unpack_int(message_length);
        end

        if (local_pack_domain_number) begin
            `uvm_unpack_int(domain_number);
        end

        if (local_pack_ptp_reserved_2) begin
            `uvm_unpack_array(ptp_reserved_2);
        end

        if (local_pack_flags) begin
            `uvm_unpack_int(flags);
        end

        if (local_pack_correction_field) begin
            `uvm_unpack_int(correction_field);
        end

        if (local_pack_ptp_reserved_3) begin
            `uvm_unpack_array(ptp_reserved_3);
        end

        if (local_pack_source_port_identity) begin
            `uvm_unpack_array(source_port_identity);
        end

        if (local_pack_sequence_id) begin
            `uvm_unpack_int(sequence_id);
        end

        if (local_pack_control_field) begin
            `uvm_unpack_enum(control_field,amiq_eth_ptp_control_field_type);
        end

        if (local_pack_log_message) begin
            `uvm_unpack_int(log_message);
        end
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_header_with_options(packer, pack_transport_specific, pack_message_type, pack_ptp_reserved_1, pack_version, pack_message_length, pack_domain_number, pack_ptp_reserved_2, pack_flags, pack_correction_field, pack_ptp_reserved_3, pack_source_port_identity, pack_sequence_id, pack_control_field, pack_log_message);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = " HEADER : \n";
        $sformat(what_to_return, {what_to_return,"transport_specific: %s",`AMIQ_ETH_FIELD_SEPARATOR},transport_specific.name());
        $sformat(what_to_return, {what_to_return,"message_type: %s",`AMIQ_ETH_FIELD_SEPARATOR},message_type.name());
        $sformat(what_to_return, {what_to_return,"ptp_reserved_1.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},ptp_reserved_1.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_1[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_1[%0d] : %x  "},i,ptp_reserved_1[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"version: %x",`AMIQ_ETH_FIELD_SEPARATOR},version);
        $sformat(what_to_return, {what_to_return,"message_length: %x",`AMIQ_ETH_FIELD_SEPARATOR},message_length);
        $sformat(what_to_return, {what_to_return,"domain_number: %x",`AMIQ_ETH_FIELD_SEPARATOR},domain_number);
        $sformat(what_to_return, {what_to_return,"ptp_reserved_2.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},ptp_reserved_2.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_2[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_2[%0d] : %x  "},i,ptp_reserved_2[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"flags: %x",`AMIQ_ETH_FIELD_SEPARATOR},flags);
        $sformat(what_to_return, {what_to_return,"correction_field: %x",`AMIQ_ETH_FIELD_SEPARATOR},correction_field);
        $sformat(what_to_return, {what_to_return,"ptp_reserved_3.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},ptp_reserved_3.size());
	    if(print_lists == 1) begin
	        foreach (ptp_reserved_3[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_reserved_3[%0d] : %x  "},i,ptp_reserved_3[i]);
	        end        
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"source_port_identity.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},source_port_identity.size());
        foreach (source_port_identity[i]) begin
            $sformat(what_to_return, {what_to_return,"source_port_identity[%0d] : %x  "},i,source_port_identity[i]);
        end 
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"sequence_id: %0x",`AMIQ_ETH_FIELD_SEPARATOR},sequence_id);
        $sformat(what_to_return, {what_to_return,"control_field: %s",`AMIQ_ETH_FIELD_SEPARATOR},control_field.name());
        $sformat(what_to_return, {what_to_return,"log_message: %0x",`AMIQ_ETH_FIELD_SEPARATOR},log_message);
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_header");
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

//PTP body class
class amiq_eth_packet_ptp_body extends uvm_object;
    `uvm_object_utils(amiq_eth_packet_ptp_body)

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = " BODY : \n";
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        return 1;
    endfunction

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
    endfunction

    //get the body size in bytes
    //@return the body size in bytes
    virtual function int body_size_in_bytes();
        bit bitstream[];
        byte unsigned byte_data [];

        void'(pack(bitstream));

        byte_data = {>> {bitstream}};

        return byte_data.size();
    endfunction

endclass

//PTP announce message class
class amiq_eth_packet_ptp_announce_message extends amiq_eth_packet_ptp_body;
    `uvm_object_utils(amiq_eth_packet_ptp_announce_message)

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

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ptp_announce_message_reserved = new[`AMIQ_ETH_PTP_ANNOUNCE_MESSAGE_RESERVED_WIDTH];
        origin_timestamp = new[`AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
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

	//pack Ethernet PTP announce message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to pack or not the "origin_timestamp" field
    //@param local_pack_current_utc_offset - boolean to control if to pack or not the "current_utc_offset" field
    //@param local_pack_reserved - boolean to control if to pack or not the "reserved" field
    //@param local_pack_grandmaster_priority_1 - boolean to control if to pack or not the "grandmaster_priority_1" field
    //@param local_pack_grandmaster_clock_quality - boolean to control if to pack or not the "grandmaster_clock_quality" field
    //@param local_pack_grandmaster_priority_2 - boolean to control if to pack or not the "grandmaster_priority_2" field
    //@param local_pack_grandmaster_identity - boolean to control if to pack or not the "grandmaster_identity" field
    //@param local_pack_steps_removed - boolean to control if to pack or not the "steps_removed" field
    //@param local_pack_time_source - boolean to control if to pack or not the "time_source" field
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
            `uvm_pack_array(origin_timestamp);
        end

        if (local_pack_current_utc_offset) begin
            `uvm_pack_int(current_utc_offset);
        end

        if (local_pack_reserved) begin
            `uvm_pack_array(ptp_announce_message_reserved);
        end

        if (local_pack_grandmaster_priority_1) begin
            `uvm_pack_int(grandmaster_priority_1);
        end

        if (local_pack_grandmaster_clock_quality) begin
            `uvm_pack_int(grandmaster_clock_quality);
        end

        if (local_pack_grandmaster_priority_2) begin
            `uvm_pack_int(grandmaster_priority_2);
        end

        if (local_pack_grandmaster_identity) begin
            `uvm_pack_int(grandmaster_identity);
        end

        if (local_pack_steps_removed) begin
            `uvm_pack_int(steps_removed);
        end

        if (local_pack_time_source) begin
            `uvm_pack_int(time_source);
        end
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_announce_message_with_options(packer,pack_origin_timestamp,pack_current_utc_offset,pack_reserved,pack_grandmaster_priority_1,pack_grandmaster_clock_quality,pack_grandmaster_priority_2,pack_grandmaster_identity,pack_steps_removed,pack_time_source);
    endfunction

	//unpack Ethernet PTP announce message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to unpack or not the "origin_timestamp" field
    //@param local_pack_current_utc_offset - boolean to control if to unpack or not the "current_utc_offset" field
    //@param local_pack_reserved - boolean to control if to unpack or not the "reserved" field
    //@param local_pack_grandmaster_priority_1 - boolean to control if to unpack or not the "grandmaster_priority_1" field
    //@param local_pack_grandmaster_clock_quality - boolean to control if to unpack or not the "grandmaster_clock_quality" field
    //@param local_pack_grandmaster_priority_2 - boolean to control if to unpack or not the "grandmaster_priority_2" field
    //@param local_pack_grandmaster_identity - boolean to control if to unpack or not the "grandmaster_identity" field
    //@param local_pack_steps_removed - boolean to control if to unpack or not the "steps_removed" field
    //@param local_pack_time_source - boolean to control if to unpack or not the "time_source" field
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
            `uvm_unpack_array(origin_timestamp);
        end

        if (local_pack_current_utc_offset) begin
            `uvm_unpack_int(current_utc_offset);
        end

        if (local_pack_reserved) begin
            `uvm_unpack_array(ptp_announce_message_reserved);
        end

        if (local_pack_grandmaster_priority_1) begin
            `uvm_unpack_int(grandmaster_priority_1);
        end

        if (local_pack_grandmaster_clock_quality) begin
            `uvm_unpack_int(grandmaster_clock_quality);
        end

        if (local_pack_grandmaster_priority_2) begin
            `uvm_unpack_int(grandmaster_priority_2);
        end

        if (local_pack_grandmaster_identity) begin
            `uvm_unpack_int(grandmaster_identity);
        end

        if (local_pack_steps_removed) begin
            `uvm_unpack_int(steps_removed);
        end

        if (local_pack_time_source) begin
            `uvm_unpack_int(time_source);
        end
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_announce_message_with_options(packer,pack_origin_timestamp,pack_current_utc_offset,pack_reserved,pack_grandmaster_priority_1,pack_grandmaster_clock_quality,pack_grandmaster_priority_2,pack_grandmaster_identity,pack_steps_removed,pack_time_source);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = " ANNOUNCE MESSAGE : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"current_utc_offset: %x",`AMIQ_ETH_FIELD_SEPARATOR},current_utc_offset);
        $sformat(what_to_return, {what_to_return,"ptp_announce_message_reserved.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},ptp_announce_message_reserved.size());
	    if(print_lists == 1) begin
	        foreach (ptp_announce_message_reserved[i]) begin
	            $sformat(what_to_return, {what_to_return,"ptp_announce_message_reserved[%0d] : %x  "},i,ptp_announce_message_reserved[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"grandmaster_priority_1: %x",`AMIQ_ETH_FIELD_SEPARATOR},grandmaster_priority_1);
        $sformat(what_to_return, {what_to_return,"grandmaster_clock_quality: %x",`AMIQ_ETH_FIELD_SEPARATOR},grandmaster_clock_quality);
        $sformat(what_to_return, {what_to_return,"grandmaster_priority_2: %x",`AMIQ_ETH_FIELD_SEPARATOR},grandmaster_priority_2);
        $sformat(what_to_return, {what_to_return,"grandmaster_identity: %x",`AMIQ_ETH_FIELD_SEPARATOR},grandmaster_identity);
        $sformat(what_to_return, {what_to_return,"steps_removed: %x",`AMIQ_ETH_FIELD_SEPARATOR},steps_removed);
        $sformat(what_to_return, {what_to_return,"time_source: %0x",`AMIQ_ETH_FIELD_SEPARATOR},time_source);
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_announce_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_announce_message");
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

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_announce_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_announce_message");
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

//PTP Synch Message
class amiq_eth_packet_ptp_sync_message extends amiq_eth_packet_ptp_body;
    `uvm_object_utils(amiq_eth_packet_ptp_sync_message)

    rand byte origin_timestamp[];
    local bit pack_origin_timestamp;

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        origin_timestamp = new[`AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
        pack_origin_timestamp = 1;
	    print_lists = 0;   
    endfunction

	//pack Ethernet PTP sync message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to pack or not the "origin_timestamp" field
    virtual function void pack_ptp_sync_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            `uvm_pack_array(origin_timestamp);
        end
        
    endfunction

    //pack the entire PTP Synch Message
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_sync_message_with_options(packer,pack_origin_timestamp);
    endfunction

	//unpack Ethernet PTP sync message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to unpack or not the "origin_timestamp" field
    virtual function void  unpack_ptp_sync_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            `uvm_unpack_array(origin_timestamp);
        end
        
    endfunction

    //unpack the entire PTP Synch Message
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_sync_message_with_options(packer,pack_origin_timestamp);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = " SYNC MESSAGE : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_sync_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_sync_message");
        end
       
        for(int i = 0; i < origin_timestamp.size(); i++) begin
            if(origin_timestamp[i] != casted_rhs.origin_timestamp[i]) begin
                return 0;
            end
        end
        
        return 1;
    endfunction

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_sync_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_sync_message");
        end

        for(int i = 0; i < origin_timestamp.size(); i++) begin
            origin_timestamp[i] = casted_rhs.origin_timestamp[i];
        end        
        
    endfunction

endclass

//PTP delay request message
class amiq_eth_packet_ptp_delay_req_message extends amiq_eth_packet_ptp_body;
    `uvm_object_utils(amiq_eth_packet_ptp_delay_req_message)

    rand byte origin_timestamp[];
    local bit pack_origin_timestamp;

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        origin_timestamp = new[`AMIQ_ETH_PTP_ORIGIN_TIMESTAMP_SIZE];
        pack_origin_timestamp = 1;
	    print_lists = 0;      
    endfunction

	//pack Ethernet PTP delay request message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to pack or not the "origin_timestamp" field
    virtual function void   pack_ptp_delay_req_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            `uvm_pack_array(origin_timestamp);
        end
        
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_delay_req_message_with_options(packer,pack_origin_timestamp);
    endfunction

	//unpack Ethernet PTP delay request message
    //@param packer - the packer used by this function
    //@param local_pack_origin_timestamp - boolean to control if to unpack or not the "origin_timestamp" field
    virtual function void  unpack_ptp_delay_req_message_with_options(uvm_packer packer,
            bit local_pack_origin_timestamp);

        if (local_pack_origin_timestamp) begin
            `uvm_unpack_array(origin_timestamp);
        end
        
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_delay_req_message_with_options(packer,pack_origin_timestamp);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = " DELAY REQ : \n";
        $sformat(what_to_return, {what_to_return,"origin_timestamp.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},origin_timestamp.size());
	    if(print_lists == 1) begin
	        foreach (origin_timestamp[i]) begin
	            $sformat(what_to_return, {what_to_return,"origin_timestamp[%0d] : %x  "},i,origin_timestamp[i]);
	        end 
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ptp_delay_req_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_delay_req_message");
        end
       
        for(int i = 0; i < origin_timestamp.size(); i++) begin
            if(origin_timestamp[i] != casted_rhs.origin_timestamp[i]) begin
                return 0;
            end
        end
        
        return 1;
    endfunction

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
        amiq_eth_packet_ptp_delay_req_message casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ptp_delay_req_message");
        end

        for(int i = 0; i < origin_timestamp.size(); i++) begin
            origin_timestamp[i] = casted_rhs.origin_timestamp[i];
        end        
        
    endfunction

endclass

//PTP packet
class amiq_eth_packet_ptp extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_ptp)

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

    //constructor
    //@param name - the name assigned to the instance of this class
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
        local_source_address=`AMIQ_ETH_GROUP_ADDRESS_MASK;

        //avoid  .... ...1 .... .... .... .... = IG bit: Group address (multicast/broadcast)
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
            default     : `uvm_fatal("AMIQ_ETH", "This si not a PTP message type")
        endcase
        
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction

	//pack Ethernet PTP delay request message
    //@param packer - the packer used by this function
    //@param local_pack_header - boolean to control if to pack or not the "header" field
    //@param local_pack_body - boolean to control if to pack or not the "body" field
    //@param local_pack_fcs - boolean to control if to pack or not the "fcs" field
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
                default     : `uvm_fatal("AMIQ_ETH", "This si not a PTP message type")
            endcase
        end

        if ((local_pack_fcs) & (for_wireshark)) begin
            `uvm_pack_int(fcs);
        end
    endfunction

    //pack the entire Ethernet PTP packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_ptp_with_options(packer, pack_header, pack_body, pack_fcs);
    endfunction

	//unpack Ethernet PTP delay request message
    //@param packer - the packer used by this function
    //@param local_pack_header - boolean to control if to unpack or not the "header" field
    //@param local_pack_body - boolean to control if to unpack or not the "body" field
    //@param local_pack_fcs - boolean to control if to unpack or not the "fcs" field
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
                default     : `uvm_fatal("AMIQ_ETH", "This si not a PTP message type")
            endcase
        end

        if ((local_pack_fcs) & (for_wireshark)) begin
            `uvm_unpack_int(fcs);
        end
    endfunction

    //unpack the entire Ethernet PTP packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_ptp_with_options(packer, pack_header, pack_body, pack_fcs);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf({"%s",`AMIQ_ETH_FIELD_SEPARATOR},super.convert2string());
        $sformat(what_to_return, {what_to_return,header.convert2string(),`AMIQ_ETH_FIELD_SEPARATOR});
        case (header.message_type)
            PTP_AnnounceMessage  : begin
                $sformat(what_to_return, {what_to_return,announce_message_body.convert2string(),`AMIQ_ETH_FIELD_SEPARATOR});
            end
            PTP_SyncMessage  : begin
                $sformat(what_to_return, {what_to_return,sync_message_body.convert2string(),`AMIQ_ETH_FIELD_SEPARATOR});
            end
            PTP_Delay_ReqMessage  : begin
                $sformat(what_to_return, {what_to_return,delay_req_message_body.convert2string(),`AMIQ_ETH_FIELD_SEPARATOR});
            end
            default     : `uvm_fatal("AMIQ_ETH", "This si not a PTP message type")
        endcase
        $sformat(what_to_return, {what_to_return,"fcs: %0x",`AMIQ_ETH_FIELD_SEPARATOR},fcs);
        return what_to_return;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_PTP_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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
            default     : `uvm_fatal("AMIQ_ETH", "This si not a PTP message type")
        endcase

        if(fcs != casted_rhs.fcs) begin
            return 0;
        end

        return 1;
    endfunction

    //function for packing the Ethernet packet using only the required information for computing the FCS
    //@param bitstream - the packed bit stream is placed in "bitstream" parameter
    virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;

        pack_fcs = 0;

        super.pack_for_fcs(bitstream);

        pack_fcs = current_pack_fcs;
    endfunction
    
    //pack the Ethernet packet to a list of bytes in the format required by Wireshark software
    //@param byte_data - array in which to put the packed information
    virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=0;
        super.to_wireshark_array(byte_data);
        for_wireshark=1;
    endfunction

endclass

`endif