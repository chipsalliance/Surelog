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
 * NAME:        amiq_eth_packet_ethernet_configuration_testing.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Configuration Testing Protocol Ethernet packet.
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING

//Ethernet Configuration Testing Protocol packet
class amiq_eth_packet_ethernet_configuration_testing extends amiq_eth_packet_ether_type;
    
    `uvm_object_utils(amiq_eth_packet_ethernet_configuration_testing)

    //SkipCount
    rand amiq_eth_ethernet_configuration_testing_skipcount skipcount;
    
    //Function
    rand amiq_eth_ethernet_configuration_testing_function cfg_test_function;
    
    //Data
    rand int data_size;
    
    rand amiq_eth_data data[];
    
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
        ether_type = AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_PROTOCOL;
    endfunction

    function void post_randomize();
        amiq_eth_address local_source_address;
        amiq_eth_ethernet_configuration_testing_skipcount local_skipcount=skipcount;
        amiq_eth_ethernet_configuration_testing_function local_cfg_test_function=cfg_test_function;
        local_source_address=`AMIQ_ETH_GROUP_ADDRESS_MASK;

        //avoid  .... ...1 .... .... .... .... = IG bit: Group address (multicast/broadcast)
        source_address = source_address & local_source_address;

        for(int i = 1 ; i<= `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_SKIPCOUNT_WIDTH/8;i++) begin
            for(int j = 0 ; j< 8;j++) begin
                skipcount[`AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_SKIPCOUNT_WIDTH-8*i+j] = local_skipcount[8*(i-1)+j];
            end
        end
        for(int i = 1 ; i<= `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FUNCTION_WIDTH;i++) begin
            for(int j = 0 ; j< 8;j++) begin
                cfg_test_function[`AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_FUNCTION_WIDTH-8*i+j] = local_cfg_test_function[8*(i-1)+j];
            end
        end
        
    endfunction

    constraint data_c {
        solve data_size before data;
        solve data_size before skipcount;
        data_size <= `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_DATA_MAX;
        data_size >= `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_DATA_MIN;
        data.size() == data_size;
        skipcount <= data_size;
    }

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        `uvm_pack_int(skipcount);
        `uvm_pack_enum(cfg_test_function);
        if ((data_size > `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_DATA_MAX) || (data_size < `AMIQ_ETH_ETHERNET_CONFIGURATION_TESTING_DATA_MIN)) begin
            `uvm_fatal("ETHERNET_CONFIGURATION_TESTING", $sformatf("Illegal Pack: \ndata_size: %0d", data_size));
        end
        if (for_wireshark==0) begin
            `uvm_pack_int(data_size);
            if (data.size() != data_size) begin
                `uvm_fatal("ETHERNET_CONFIGURATION_TESTING", $sformatf("Illegal Pack: \ndata_size: %0d\ndata.size(): %0d", data_size, data.size()));
            end
        end
        `uvm_pack_array(data);
        `uvm_pack_int(fcs);
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        `uvm_unpack_int(skipcount);
        `uvm_unpack_enum(cfg_test_function,amiq_eth_ethernet_configuration_testing_function);
        if (for_wireshark==0) begin
            `uvm_unpack_int(data_size);
        end
        data = new[data_size];
        `uvm_unpack_array(data);
        `uvm_unpack_int(fcs);
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string what_to_return = $sformatf({"%s",`AMIQ_ETH_FIELD_SEPARATOR},super.convert2string());
        $sformat(what_to_return, {what_to_return,"skipcount: %x",`AMIQ_ETH_FIELD_SEPARATOR},skipcount);
        $sformat(what_to_return, {what_to_return,"cfg_test_function: %s",`AMIQ_ETH_FIELD_SEPARATOR},cfg_test_function);
        $sformat(what_to_return, {what_to_return,"data.size(): %0d",`AMIQ_ETH_FIELD_SEPARATOR},data.size());
	    if(print_lists == 1) begin
	        foreach (data[i]) begin
	            $sformat(what_to_return, {what_to_return,"data[%0d] : %0x",`AMIQ_ETH_FIELD_SEPARATOR},i,data[i]);
	        end
	    end
        $sformat(what_to_return, {what_to_return,"fcs: %0x",`AMIQ_ETH_FIELD_SEPARATOR},fcs);
        return what_to_return;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_ETHERNET_CONFIGURATION_TESTING_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ethernet_configuration_testing casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(skipcount != casted_rhs.skipcount) begin
            return 0;
        end

        if(cfg_test_function != casted_rhs.cfg_test_function) begin
            return 0;
        end

        for(int i = 0; i < data.size(); i++) begin
            if(data[i] != casted_rhs.data[i]) begin
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