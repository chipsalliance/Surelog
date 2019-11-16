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
 * NAME:        amiq_eth_packet_hsr_base.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the HSR Ethernet packet. 
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_HSR_BASE
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_HSR_BASE

//Ethernet HSR packet
class amiq_eth_packet_hsr_base extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_hsr_base)

    //Path
    rand amiq_eth_hsr_path path;
    //Size
    rand amiq_eth_hsr_size size;
    //Sequence
    rand amiq_eth_hsr_seq seq;
    
    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_HSR;        
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        `uvm_pack_int(path);
        `uvm_pack_int(size);
        `uvm_pack_int(seq);
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        `uvm_unpack_int(path);
        `uvm_unpack_int(size);
        `uvm_unpack_int(seq);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf({"%s",`AMIQ_ETH_FIELD_SEPARATOR},super.convert2string());
        $sformat(what_to_return, {what_to_return,"path: %x",`AMIQ_ETH_FIELD_SEPARATOR},path); 
        $sformat(what_to_return, {what_to_return,"size: %x",`AMIQ_ETH_FIELD_SEPARATOR},size); 
        $sformat(what_to_return, {what_to_return,"seq: %x",`AMIQ_ETH_FIELD_SEPARATOR},seq); 
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

`endif