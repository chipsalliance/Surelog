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
 * NAME:        amiq_eth_packet_pfc_pause.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the PFC Pause Ethernet packet. 
 *                 The definition of this packet is described in IEEE 802.3-2012
 *                 For more details see file docs/ieee_802.3-2012/802.3-2012_section2.pdf,pag. 766
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_PFC_PAUSE
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_PFC_PAUSE

//Ethernet PFC Pause packet
class amiq_eth_packet_pfc_pause extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_pfc_pause)

    //OPCODE
    protected amiq_eth_pfc_opcode pfc_opcode;
	
    //Class Enable Vector
    rand amiq_eth_pfc_class_enable_vector pfc_class_enable_vector;
	
    //Time CoS
    rand amiq_eth_pfc_parameter pfc_parameters[];
	
    //Pad
    protected amiq_eth_data pad[];
	
    //Frame Check Sequence
    rand amiq_eth_fcs fcs;

	//switch to print lists
	bit print_lists = 0;

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        destination_address = `AMIQ_ETH_PFC_PACKET_DESTINATION_ADDRESS;
        ether_type = AMIQ_ETH_MAC_CONTROL;
        pfc_opcode = `AMIQ_ETH_PFC_OPCODE;
        pfc_parameters = new[`AMIQ_ETH_PFC_NUMBER_OF_PARAMETERS];
        pad = new[`AMIQ_ETH_PAYLOAD_SIZE_MIN-(`AMIQ_ETH_PFC_OPCODE_WIDTH+`AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_WIDTH+`AMIQ_ETH_PFC_PARAMETER_WIDTH*`AMIQ_ETH_PFC_NUMBER_OF_PARAMETERS)/`AMIQ_ETH_DATA_WIDTH];
        foreach (pad[i]) begin
            pad[i] = 0;
        end
        print_lists = 0;
    endfunction

    constraint destination_address_c {
        destination_address == `AMIQ_ETH_PFC_PACKET_DESTINATION_ADDRESS;
    }

    constraint pfc_class_enable_vector_c {
        pfc_class_enable_vector >= `AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_MIN;
        pfc_class_enable_vector <= `AMIQ_ETH_PFC_CLASS_ENABLE_VECTOR_MAX;
    }

    constraint pfc_parameters_c {
        pfc_parameters.size() == `AMIQ_ETH_PFC_NUMBER_OF_PARAMETERS;
        foreach(pfc_parameters[i]) {
            pfc_parameters[i] >= `AMIQ_ETH_PFC_PARAMETER_MIN;
            pfc_parameters[i] <= `AMIQ_ETH_PFC_PARAMETER_MAX;
        }
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
        `uvm_pack_int(pfc_opcode);
        `uvm_pack_int(pfc_class_enable_vector);
        `uvm_pack_array(pfc_parameters);
        `uvm_pack_array(pad);
        `uvm_pack_int(fcs);
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        `uvm_unpack_int(pfc_opcode);
        `uvm_unpack_int(pfc_class_enable_vector);
        `uvm_unpack_array(pfc_parameters);
        `uvm_unpack_array(pad);
        `uvm_unpack_int(fcs);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
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

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_PFC_PAUSE_CODE);
        
        return result;
    endfunction
    
    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
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

`endif