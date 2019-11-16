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
 * NAME:        amiq_eth_packet_length.sv
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration of the basic Ethernet frame
 *                 in which Length/Type field is interpreted as Length.
 *                 The definition of this packet is described in IEEE 802.3-2012. 
 *                 For more details see file docs/ieee_802.3-2012/802.3-2012_section1.pdf, 
 *                 chapter 3. Media Access Control (MAC) frame and packet specifications
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_LENGTH
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_LENGTH

//Basic class for declaring the Ethernet packets in which Length/Type field is interpreted as Length.
class amiq_eth_packet_length extends amiq_eth_packet;
    
    `uvm_object_utils(amiq_eth_packet_length)
    
    //Length
    rand amiq_eth_length length;
    
    constraint length_constraint {
        length >= `AMIQ_ETH_PAYLOAD_SIZE_MIN &&
        length <= `AMIQ_ETH_PAYLOAD_SIZE_MAX;
    }
    
    //MAC Client Data
    rand amiq_eth_data client_data[$];
    
    constraint client_data_constraint {
        client_data.size() == length;
    }
    
    //Frame Check Sequence
    rand amiq_eth_fcs fcs;
    
    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
    endfunction
    
    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        `uvm_pack_int(length);
        `uvm_pack_queue(client_data);
        `uvm_pack_int(fcs);
    endfunction
    
    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        `uvm_unpack_int(length);
        `uvm_unpack_queue(client_data);
        `uvm_unpack_int(fcs);
    endfunction
    
    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        return $sformatf("%s, Length: %0d, Client DATA size: %0d, FCS: %08X",
            super.convert2string(), length, client_data.size(), fcs);
    endfunction
    
    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_LENGTH_CODE);
        
        return result;
    endfunction
    
endclass
    
`endif