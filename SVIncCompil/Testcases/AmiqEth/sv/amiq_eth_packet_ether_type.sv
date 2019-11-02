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
 * NAME:        amiq_eth_packet_ether_type.sv
 * PROJECT:     amiq_eth
 * Description: This file contains the declaration of the basic Ethernet frame
 *                 in which Length/Type field is interpreted as Type.
 *                 The definition of this packet is described in IEEE 802.3-2012.
 *                 For more details see file docs/ieee_802.3-2012/802.3-2012_section1.pdf, 
 *                 chapter 3. Media Access Control (MAC) frame and packet specifications
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_ETHER_TYPE
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_ETHER_TYPE

//Basic class for declaring the Ethernet packets in which Length/Type field is interpreted as Type.
virtual class amiq_eth_packet_ether_type extends amiq_eth_packet;

    //Ethernet type
    protected amiq_eth_ether_type ether_type;
    
    local bit pack_ether_type;

    //return returns the Ethernet Type - read only variable dependent on the class
    function amiq_eth_ether_type get_ether_type();
        return ether_type;
    endfunction

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        pack_ether_type = 1;
    endfunction

    //pack Ethernet type field
    //@param packer - the packer used by this function
    //@param local_pack_ether_type - boolean to control if to pack or not the Ethernet Type field
    virtual function void do_pack_ether_type(uvm_packer packer, bit local_pack_ether_type);
        if (local_pack_ether_type) begin
            `uvm_pack_enum(ether_type);
        end 
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        do_pack_ether_type(packer,pack_ether_type);
    endfunction
 
    //set new value for pack_ether_type field 
    //@param new_val - the new value of pack_ether_type field
    virtual function void set_pack_ether_type(bit new_val);
        pack_ether_type = new_val;
    endfunction
    
    //get the value for pack_ether_type field
    //@return returns the value of pack_ether_type field
    virtual function bit get_pack_ether_type();
        return pack_ether_type;
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        amiq_eth_length int_ether_type;
        super.do_unpack(packer);

        `uvm_unpack_int(int_ether_type);

        if(!$cast(ether_type, int_ether_type)) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Could not cast int %X to ether_type", int_ether_type))
        end
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf("%s%s",super.convert2string(), `AMIQ_ETH_FIELD_SEPARATOR);
        $sformat(what_to_return, {what_to_return,"Type: %s"},ether_type.name());
        return what_to_return;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

`endif