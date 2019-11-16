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
 * NAME:        amiq_eth_packet_snap.sv
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration SNAP (SubNetwork Access Protocol) 
 *                 packet. 
 *                 The implementation is based on IEEE 802-2001.
 *                 For more details see file docs/ieee_802-2001/802-2001.pdf, 
 *                 chapter 10.3 Subnetwork Access Protocol
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_SNAP
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_SNAP

//Ethernet SubNetwork Access Protocol (SNAP) packet
class amiq_eth_packet_snap extends amiq_eth_packet;

    `uvm_object_utils(amiq_eth_packet_snap)

    //Length
    rand amiq_eth_length length;

    constraint length_constraint {
        length >= `AMIQ_ETH_PAYLOAD_SIZE_MIN &&
        length <= `AMIQ_ETH_PAYLOAD_SIZE_MAX;
    }

    //Destination Service Access Point
    rand amiq_eth_data dsap;

    constraint dsap_c {
        dsap == `AMIQ_ETH_DEFAULT_SNAP_PACKET_DSAP;
    }

    //Source Service Access Point
    rand amiq_eth_data ssap;

    constraint ssap_c {
        ssap == `AMIQ_ETH_DEFAULT_SNAP_PACKET_SSAP;
    }

    //Control
    rand amiq_eth_data ctl;

    constraint ctl_c {
        ctl == `AMIQ_ETH_DEFAULT_SNAP_PACKET_CTL;
    }

    //Protocol Identifier
    rand amiq_eth_snap_protocol_identifier protocol_identifier;

    //Protocol Data
    rand amiq_eth_data protocol_data[];

    constraint protocol_data_constraint {
        protocol_data.size() == length - 8;
    }

    //Frame Check Sequence
    rand amiq_eth_fcs fcs;

    //determine if to use the correct fcs or not
    rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

    //flag to determine if to pack/unpack the fcs
    local bit pack_fcs;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        pack_fcs = 1;
    endfunction

    //pack FCS field
    //@param packer - the packer used by this function
    virtual function void do_pack_fcs(uvm_packer packer);
        `uvm_pack_int(fcs);
    endfunction

    //unpack FCS field
    //@param packer - the packer used by this function
    virtual function void do_unpack_fcs(uvm_packer packer);
        `uvm_unpack_int(fcs);
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        `uvm_pack_int(length);
        `uvm_pack_int(dsap);
        `uvm_pack_int(ssap);
        `uvm_pack_int(ctl);
        `uvm_pack_int(protocol_identifier);
        `uvm_pack_array(protocol_data);

        if(pack_fcs) begin
            do_pack_fcs(packer);
        end

    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        `uvm_unpack_int(length);
        `uvm_unpack_int(dsap);
        `uvm_unpack_int(ssap);
        `uvm_unpack_int(ctl);
        `uvm_unpack_int(protocol_identifier);

		if(!(length >= 8)) begin
        	`uvm_error("AMIQ_ETH", $sformatf("Length is too short: %0d", length));
		end

        protocol_data = new[length - 8];
        `uvm_unpack_array(protocol_data);

        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end

    endfunction

    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
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

        result = $sformatf("%s%sLength: %0d", result, `AMIQ_ETH_FIELD_SEPARATOR, length);
        result = $sformatf("%s%sDSAP: %X", result, `AMIQ_ETH_FIELD_SEPARATOR, dsap);
        result = $sformatf("%s%sSSAP: %X", result, `AMIQ_ETH_FIELD_SEPARATOR, ssap);
        result = $sformatf("%s%sCTL: %X", result, `AMIQ_ETH_FIELD_SEPARATOR, ctl);
        result = $sformatf("%s%sPROTOCOL IDENTIFIER: %X", result, `AMIQ_ETH_FIELD_SEPARATOR, protocol_identifier);
        result = $sformatf("%s%sPROTOCOL DATA size: %0d", result, `AMIQ_ETH_FIELD_SEPARATOR, protocol_data.size());
        result = $sformatf("%s%sFCS: %X, %s", result, `AMIQ_ETH_FIELD_SEPARATOR, fcs, fcs_info);

        return result;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_SNAP_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

    //function for packing the Ethernet packet using only the required information for computing the FCS
    //@param bitstream - the packed bit stream is placed in "bitstream" parameter
    virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;

        pack_fcs = 0;

        super.pack_for_fcs(bitstream);

        pack_fcs = current_pack_fcs;
    endfunction

endclass

`endif