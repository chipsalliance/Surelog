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
 * NAME:        amiq_eth_packet_fcoe.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Fibre Channel over Ethernet (FCoE) packet. 
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_FCOE
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_FCOE

//Ethernet Fibre Channel over Ethernet (FCoE) packet
class amiq_eth_packet_fcoe extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_fcoe)

    //version
    rand amiq_eth_fcoe_version version;
    //reserved bits
    protected bit fcoe_reserved_before_sof[];
    //start of frame
    rand amiq_eth_fcoe_sof sof;
    //frame
    rand int unsigned fc_frame_size;
    rand amiq_eth_data fc_frame[];
    //end of frame
    rand amiq_eth_fcoe_eof eof;
    //reserved bits
    protected bit fcoe_reserved_after_eof[];
    //Frame Check Sequence
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

    //determine if to use the correct fcs or not
    rand bit use_correct_fcs;
    
    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_FCOE;
        fcoe_reserved_before_sof = new[`AMIQ_ETH_FCOE_RESERVED_BEFORE_SOF_SIZE];
        foreach (fcoe_reserved_before_sof[i]) begin
            fcoe_reserved_before_sof[i] = 0;
        end
        fcoe_reserved_after_eof = new[`AMIQ_ETH_FCOE_RESERVED_AFTER_EOF_SIZE];
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
        local_source_address=`AMIQ_ETH_GROUP_ADDRESS_MASK;
        
        //avoid  .... ...1 .... .... .... .... = IG bit: Group address (multicast/broadcast)
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
        fc_frame_size >= `AMIQ_ETH_FCOE_FC_FRAME_SIZE_MIN;
        fc_frame_size <= `AMIQ_ETH_FCOE_FC_FRAME_SIZE_MAX;
        fc_frame_size%4 == 0;
        fc_frame.size() == fc_frame_size;
    }
    
	//pack Ethernet FCOE packet
    //@param packer - the packer used by this function
    //@param local_pack_version - boolean to control if to pack or not the "version" field
    //@param local_pack_rsvd_b_sof - boolean to control if to pack or not the "fcoe_reserved_before_sof" field
    //@param local_pack_sof - boolean to control if to pack or not the "sof" field
    //@param local_pack_frame - boolean to control if to pack or not the "fc_frame_size" field
    //@param local_pack_eof - boolean to control if to pack or not the "eof" field
    //@param local_pack_rsvd_a_eof - boolean to control if to pack or not the "fcoe_reserved_after_eof" field
    //@param local_pack_fcs - boolean to control if to pack or not the "fcs" field
    virtual function void pack_fcoe_with_options(uvm_packer packer, bit local_pack_version, bit local_pack_rsvd_b_sof, bit local_pack_sof, bit local_pack_frame, bit local_pack_eof, bit local_pack_rsvd_a_eof, bit local_pack_fcs);
        if (local_pack_version) begin
            `uvm_pack_int(version);
        end

        if (local_pack_rsvd_b_sof) begin
            `uvm_pack_array(fcoe_reserved_before_sof);
        end

        if (local_pack_sof) begin
            `uvm_pack_enum(sof);
        end

        if (local_pack_frame) begin
            if (for_wireshark==0) begin
                `uvm_pack_int(fc_frame_size);
            end
            if (to_compute_crc) begin
                amiq_eth_data fc_frame_l[];
                fc_frame_l = new[fc_frame.size()-`AMIQ_ETH_FCOE_FC_FRAME_CRC_SIZE_IN_BYTES];
                foreach (fc_frame_l[i]) begin
                    fc_frame_l[i] = fc_frame[i];
                end
                `uvm_pack_array(fc_frame_l);
            end else begin
                `uvm_pack_array(fc_frame);
            end
        end

        if (local_pack_eof) begin
            `uvm_pack_enum(eof);
        end

        if (local_pack_rsvd_a_eof) begin
            `uvm_pack_array(fcoe_reserved_after_eof);
        end

        if (local_pack_fcs) begin
            `uvm_pack_int(fcs);
        end
    endfunction


    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        pack_fcoe_with_options(packer, pack_version, pack_rsvd_b_sof, pack_sof, pack_frame, pack_eof, pack_rsvd_a_eof, pack_fcs);
    endfunction

	//unpack Ethernet FCOE packet
    //@param packer - the packer used by this function
    //@param local_pack_version - boolean to control if to unpack or not the "version" field
    //@param local_pack_rsvd_b_sof - boolean to control if to unpack or not the "fcoe_reserved_before_sof" field
    //@param local_pack_sof - boolean to control if to unpack or not the "sof" field
    //@param local_pack_frame - boolean to control if to unpack or not the "fc_frame_size" field
    //@param local_pack_eof - boolean to control if to unpack or not the "eof" field
    //@param local_pack_rsvd_a_eof - boolean to control if to unpack or not the "fcoe_reserved_after_eof" field
    //@param local_pack_fcs - boolean to control if to unpack or not the "fcs" field
    virtual function void unpack_fcoe_with_options(uvm_packer packer, bit local_pack_version, bit local_pack_rsvd_b_sof, bit local_pack_sof, bit local_pack_frame, bit local_pack_eof, bit local_pack_rsvd_a_eof, bit local_pack_fcs);
        `uvm_unpack_int(version);
        `uvm_unpack_array(fcoe_reserved_before_sof);
        `uvm_unpack_enum(sof,amiq_eth_fcoe_sof);
        if (for_wireshark==0) begin
            `uvm_unpack_int(fc_frame_size);
        end
        fc_frame = new[fc_frame_size];
        `uvm_unpack_array(fc_frame);
        `uvm_unpack_enum(eof,amiq_eth_fcoe_eof);
        `uvm_unpack_array(fcoe_reserved_after_eof);
        if (local_pack_fcs) begin
            `uvm_unpack_int(fcs);
        end 
    endfunction
    
    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        unpack_fcoe_with_options(packer, pack_version, pack_rsvd_b_sof, pack_sof, pack_frame, pack_eof, pack_rsvd_a_eof, pack_fcs);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf({"%s",`AMIQ_ETH_FIELD_SEPARATOR},super.convert2string());
        $sformat(what_to_return, {what_to_return,"version: %x",`AMIQ_ETH_FIELD_SEPARATOR},version);
        $sformat(what_to_return, {what_to_return,"fcoe_reserved_before_sof.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},fcoe_reserved_before_sof.size());
	    if(print_lists == 1) begin
	        foreach (fcoe_reserved_before_sof[i]) begin
	            $sformat(what_to_return, {what_to_return,"fcoe_reserved_before_sof[%0d] : %x  "},i,fcoe_reserved_before_sof[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"sof: %s",`AMIQ_ETH_FIELD_SEPARATOR},sof.name());
        $sformat(what_to_return, {what_to_return,"fc_frame_size: %x",`AMIQ_ETH_FIELD_SEPARATOR},fc_frame_size);
	    if(print_lists == 1) begin
	        foreach (fc_frame[i]) begin
	            $sformat(what_to_return, {what_to_return,"fc_frame[%0d] : %x ",`AMIQ_ETH_FIELD_SEPARATOR},i,fc_frame[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"eof: %s",`AMIQ_ETH_FIELD_SEPARATOR},eof.name());
        $sformat(what_to_return, {what_to_return,"fcoe_reserved_after_eof.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},fcoe_reserved_after_eof.size());
	    if(print_lists == 1) begin
	        foreach (fcoe_reserved_after_eof[i]) begin
	            $sformat(what_to_return, {what_to_return,"fcoe_reserved_after_eof[%0d] : %x  "},i,fcoe_reserved_after_eof[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,`AMIQ_ETH_FIELD_SEPARATOR});
        $sformat(what_to_return, {what_to_return,"fcs: %0x",`AMIQ_ETH_FIELD_SEPARATOR},fcs);
        return what_to_return;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_FCOE_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

    //get the correct CRC
    //@return returns the value of the correct CRC
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

    //pack the Ethernet packet to a list of bits used for computing the CRC
    //@param bitstream - array in which to put the packed information
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
        for_wireshark=1;
        super.to_wireshark_array(byte_data);
        for_wireshark=0;
    endfunction

endclass

`endif