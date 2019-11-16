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
 * NAME:        amiq_eth_packet_arp.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Ethernet Address Resolution Protocol packet. 
 *                 Implementation is done based on: http://en.wikipedia.org/wiki/Address_Resolution_Protocol
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_ARP
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_ARP

//Ethernet Address Resolution Protocol packet
class amiq_eth_packet_arp extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_arp)

    //Hardware type (HTYPE) - This field specifies the network protocol type. 
    rand amiq_eth_arp_htype htype;
    
    //Protocol type (PTYPE) - This field specifies the internetwork protocol for which the ARP request is intended.
    rand amiq_eth_arp_ptype ptype;
    
    //Hardware length (HLEN) - Length (in octets) of a hardware address.
    rand amiq_eth_arp_hlen hlen;
    
    //Protocol length (PLEN) - Length (in octets) of addresses used in the upper layer protocol. (The upper layer protocol specified in PTYPE.) 
    rand amiq_eth_arp_plen plen;
    
    //Operation - Specifies the operation that the sender is performing: 1 for request, 2 for reply.
    rand amiq_eth_arp_oper oper;
    
    constraint oper_c {
        oper inside {`AMIQ_ETH_ARP_OPER_REQUEST, `AMIQ_ETH_ARP_OPER_REPLY};
    }
    
    //Sender hardware address (SHA) - Media address of the sender. 
    //In an ARP request this field is used to indicate the address of the host sending the request. 
    //In an ARP reply this field is used to indicate the address of the host that the request was looking for. (Not necessarily address of the host replying as in the case of virtual media.) 
    //Note that switches do not pay attention to this field, particularly in learning MAC addresses.
    rand amiq_eth_arp_sha sha;
    
    //Sender protocol address (SPA) - internetwork address of the sender.
    rand amiq_eth_arp_spa spa;
    
    //Target hardware address (THA) - Media address of the intended receiver. 
    //In an ARP request this field is ignored. 
    //In an ARP reply this field is used to indicate the address of the host that originated the ARP request.
    rand amiq_eth_arp_tha tha;
    
    //Target protocol address (TPA) - internetwork address of the intended receiver.
    rand amiq_eth_arp_tpa tpa;
    
    //Frame Check Sequence
    rand amiq_eth_fcs fcs;
    
    //determine if to use the correct fcs or not
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

    //flag to determine if to pack/unpack the fcs
    local bit pack_fcs;
    
    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_ARP;
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
        
        `uvm_pack_int(htype);
        `uvm_pack_int(ptype);
        `uvm_pack_int(hlen);
        `uvm_pack_int(plen);
        `uvm_pack_int(oper);
        `uvm_pack_int(sha);
        `uvm_pack_int(spa);
        `uvm_pack_int(tha);
        `uvm_pack_int(tpa);    
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        
        `uvm_unpack_int(htype);
        `uvm_unpack_int(ptype);
        `uvm_unpack_int(hlen);
        `uvm_unpack_int(plen);
        `uvm_unpack_int(oper);
        `uvm_unpack_int(sha);
        `uvm_unpack_int(spa);
        `uvm_unpack_int(tha);
        `uvm_unpack_int(tpa);    
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
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
        
        return $sformatf("%s%sHTYPE: %X%sPTYPE: %X%sHLEN: %X%sPLEN: %X%sOPER: %X%sSHA: %X%sSPA: %X%sTHA: %X%sTPA: %X%sFCS: %0X - %s",
            super.convert2string(), `AMIQ_ETH_FIELD_SEPARATOR,
            htype, `AMIQ_ETH_FIELD_SEPARATOR,
            ptype, `AMIQ_ETH_FIELD_SEPARATOR,
            hlen, `AMIQ_ETH_FIELD_SEPARATOR,
            plen, `AMIQ_ETH_FIELD_SEPARATOR,
            oper, `AMIQ_ETH_FIELD_SEPARATOR,
            sha, `AMIQ_ETH_FIELD_SEPARATOR,
            spa, `AMIQ_ETH_FIELD_SEPARATOR,
            tha, `AMIQ_ETH_FIELD_SEPARATOR,
            tpa, `AMIQ_ETH_FIELD_SEPARATOR,
            fcs, fcs_info);
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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
    
    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_ARP_CODE);
        
        return result;
    endfunction
    
    function void post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
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