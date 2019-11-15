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
 * NAME:        amiq_eth_packet_hsr_standard.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet HSR standard packet. 
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_HSR_STANDARD
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_HSR_STANDARD

//Ethernet HSR standard packet
class amiq_eth_packet_hsr_standard extends amiq_eth_packet_hsr_base;
    
    `uvm_object_utils(amiq_eth_packet_hsr_standard)

    //LPDU
    rand amiq_eth_ether_type protocol;
    rand amiq_eth_data lpdu[];
    //Frame Check Sequence
    rand amiq_eth_fcs fcs;

    bit for_wireshark = 0;

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
	    print_lists = 0;
    endfunction

    constraint lpdu_c {
        solve lpdu before size;
        lpdu.size() <= `AMIQ_ETH_HSR_STANDARD_LPDU_MAX;
        lpdu.size() >= `AMIQ_ETH_HSR_STANDARD_LPDU_MIN;
        size == lpdu.size() + (`AMIQ_ETH_HSR_PATH_WIDTH+`AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH+`AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH+`AMIQ_ETH_HSR_STANDARD_PROTOCOL_WIDTH)/8;
    }

    function void post_randomize();
        amiq_eth_address local_source_address;
        local_source_address=`AMIQ_ETH_GROUP_ADDRESS_MASK;

        //avoid  .... ...1 .... .... .... .... = IG bit: Group address (multicast/broadcast)
        source_address = source_address & local_source_address;
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        `uvm_pack_enum(protocol);
        `uvm_pack_array(lpdu);
        `uvm_pack_int(fcs);
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        amiq_eth_length int_protocol;
        super.do_unpack(packer);
        `uvm_unpack_int(int_protocol);
        if(!$cast(protocol, int_protocol)) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Could not cast int %X to protocol", int_protocol))
        end
        lpdu = new[size-(`AMIQ_ETH_HSR_PATH_WIDTH+`AMIQ_ETH_HSR_STANDARD_SIZE_WIDTH+`AMIQ_ETH_HSR_STANDARD_SEQ_WIDTH+`AMIQ_ETH_HSR_STANDARD_PROTOCOL_WIDTH)/8];
        `uvm_unpack_array(lpdu);
        `uvm_unpack_int(fcs);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf({"%s",`AMIQ_ETH_FIELD_SEPARATOR},super.convert2string());
        $sformat(what_to_return, {what_to_return,"protocol: %s",`AMIQ_ETH_FIELD_SEPARATOR},protocol.name());
        $sformat(what_to_return, {what_to_return,"lpdu.size(): %x",`AMIQ_ETH_FIELD_SEPARATOR},lpdu.size());
	    if(print_lists == 1) begin
	        foreach (lpdu[i]) begin
	            $sformat(what_to_return, {what_to_return,"lpdu[%0d] : %0x",`AMIQ_ETH_FIELD_SEPARATOR},i,lpdu[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0x",`AMIQ_ETH_FIELD_SEPARATOR},fcs);
        return what_to_return;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_HSR_STANDARD_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

    //pack the Ethernet packet to a list of bytes in the format required by Wireshark software
    //@param byte_data - array in which to put the packed information
    virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        for_wireshark=1;
        super.to_wireshark_array(byte_data);
        for_wireshark=0;
    endfunction

endclass

`endif