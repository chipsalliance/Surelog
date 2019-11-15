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
 * NAME:        amiq_eth_packet_jumbo.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Jumbo Ethernet packet. 
 *                 Implementation is done based on: http://en.wikipedia.org/wiki/Jumbo_frame
 *                 Jumbo packets are not supported by IEEE standards:
 *                 SOURCE: http://www.ethernetalliance.org/wp-content/uploads/2011/10/EA-Ethernet-Jumbo-Frames-v0-1.pdf
 *                 Furthermore, IEEE has determined they will not support or define Jumbo frames due to concerns around 
 *                 vendor and equipment interoperability. 
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_JUMBO
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_JUMBO

//Ethernet Jumbo packet
class amiq_eth_packet_jumbo extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_jumbo)
    
    //MAC Client Data Size
    rand amiq_eth_jumbo_client_data_size client_data_size;
    
    constraint client_data_size_c {
        client_data_size >= `AMIQ_ETH_MIN_JUMBO_PAYLOAD_SIZE &&
        client_data_size <= `AMIQ_ETH_MAX_JUMBO_PAYLOAD_SIZE;
    }
    
    //MAC Client Data
    rand amiq_eth_data client_data[];
    
    constraint client_data_c {
        solve client_data_size before client_data;
        client_data.size() == client_data_size;
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
    
    //flag to determine if to pack/unpack the client_data_size
    local bit pack_client_data_size;
    
    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_JUMBO_FRAMES;
        pack_fcs = 1;
        pack_client_data_size = 1;
    endfunction
    
    //pack fcs field
    //@param packer - the packer used by this function
    virtual function void do_pack_fcs(uvm_packer packer);
        `uvm_pack_int(fcs);    
    endfunction
    
    //unpack fcs field
    //@param packer - the packer used by this function
    virtual function void do_unpack_fcs(uvm_packer packer);
        `uvm_unpack_int(fcs);
    endfunction
    
    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        
        if(pack_client_data_size) begin
            `uvm_pack_int(client_data_size)
        end
        
        for(int i = 0; i < client_data.size(); i++) begin
            `uvm_pack_int(client_data[i]);
        end
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction
    
    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
        if(pack_client_data_size) begin
            `uvm_unpack_int(client_data_size);
        end
        
        client_data = new[client_data_size];
        for(int i = 0; i < client_data.size(); i++) begin
            `uvm_unpack_int(client_data[i]);
        end
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
        
        if(ether_type != AMIQ_ETH_JUMBO_FRAMES) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("ether_type (%s) is different then AMIQ_ETH_JUMBO_FRAMES", ether_type.name()))    
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
        string fcs_info;
        amiq_eth_fcs correct_fcs = get_correct_fcs();
        
        if(correct_fcs == fcs) begin
            fcs_info = $sformatf("FCS is correct");
        end
        else begin
            fcs_info = $sformatf("FCS is wrong - expecting %X", correct_fcs);
        end
        
        return $sformatf("%s%sData Size: %0d%sFCS: %X, %s",
            super.convert2string(), `AMIQ_ETH_FIELD_SEPARATOR, 
            client_data_size, `AMIQ_ETH_FIELD_SEPARATOR,
            fcs, fcs_info);
    endfunction
    
    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_JUMBO_CODE);
        
        return result;
    endfunction
    
    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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
    
    //function for packing the Ethernet packet using only the required information for computing the FCS
    //@param bitstream - the packed bit stream is placed in "bitstream" parameter
    virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_fcs = pack_fcs;
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_fcs = 0;
        pack_client_data_size = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_fcs = current_pack_fcs;
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
    //pack the Ethernet packet to a list of bytes in the format required by Wireshark software
    //@param byte_data - array in which to put the packed information
    virtual function void to_wireshark_array(ref byte unsigned byte_data[$]);
        bit current_pack_client_data_size = pack_client_data_size;
        
        pack_client_data_size = 0;
        
        super.to_wireshark_array(byte_data);
        
        pack_client_data_size = current_pack_client_data_size;
    endfunction
    
endclass
    
`endif