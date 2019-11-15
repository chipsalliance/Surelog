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
 * NAME:        amiq_eth_packet_magic.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the Magic Ethernet packet. 
 *                 The definition of this packet is described in IEEE 802.1X-2010.
 *                 For more details see file docs/ieee_802.1X-2010/802.1X-2010.pdf, 
 *                 Annex F - Support for ‘Wake-on-LAN’ protocols.
 *                 A more detail description of the magic packet was found on 
 *                 Wiki: http://en.wikipedia.org/wiki/Wake-on-LAN#Magic_packet
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_MAGIC
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_MAGIC

//Ethernet Magic packet
class amiq_eth_packet_magic extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_magic)

    //the address of the target device
    rand amiq_eth_address target_mac;

    //password size
    rand int unsigned password_size;

    //password
    rand amiq_eth_data password[];

    //MAC Client Data Size
    rand int unsigned client_data_size;

    constraint password_c {
        solve password_size before password;
        solve password_size before client_data_size;
        password.size() == password_size;
    }

    constraint client_data_size_c {
        solve password_size before client_data_size;
        solve target_mac before client_data_size;
        password_size inside {0, 4, 6};
        //problem in system-verilog: if using here get_useful_info_size() "solve-before" no longer works
        client_data_size >= (((`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH + (`AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS * `AMIQ_ETH_ADDRESS_WIDTH) + (password_size * `AMIQ_ETH_DATA_WIDTH)) / 8)) &&
        client_data_size >= `AMIQ_ETH_PAYLOAD_SIZE_MIN &&
        client_data_size <= `AMIQ_ETH_PAYLOAD_SIZE_MAX;
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

    //starting index of the magic packet synchronization stream
    rand int unsigned synch_stream_starting_index;

    constraint synch_stream_starting_index_c {
        solve client_data_size before synch_stream_starting_index;
        solve password_size before synch_stream_starting_index;
        synch_stream_starting_index <= client_data_size - 1 - ((`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH + (`AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS * `AMIQ_ETH_ADDRESS_WIDTH) +
                (password_size * `AMIQ_ETH_DATA_WIDTH)) / 8);
    }

    function int unsigned get_useful_info_size();
        int unsigned result = ((`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH + (`AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS * `AMIQ_ETH_ADDRESS_WIDTH) +
                (password_size * `AMIQ_ETH_DATA_WIDTH)) / 8);
        return result;
    endfunction

    //flag to determine if to pack/unpack the fcs
    local bit pack_fcs;
    
    //flag to determine if to pack/unpack the client_data_size
    local bit pack_client_data_size;
    
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
    
    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_WAKE_ON_LAN;
        pack_fcs = 1;
        pack_client_data_size = 1;
    endfunction

    //set the information such as magic packet synchronization stream and target address in the client data 
    virtual function void set_useful_info_in_client_data();
        if(client_data.size() < get_useful_info_size()) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("%0d: client_data.size(): %0d (client_data_size: %0d) should be bigger or equal to get_useful_info_size(): %0d",
                    get_inst_id(), client_data.size(), client_data_size, get_useful_info_size()));
        end

        begin
            amiq_eth_data temp_data[];
            temp_data = { >> {`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM} };

            for(int i = 0; i < (`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8); i++) begin
                int unsigned client_data_index = i + synch_stream_starting_index;
                client_data[client_data_index] = temp_data[i];
            end
        end

        begin
            int target_address_starting_index = synch_stream_starting_index + (`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8);
            int target_address_width_in_bytes = ($bits(target_mac) / 8);
            amiq_eth_data temp_data[];
            temp_data = { >> {target_mac} };

            for(int target_mac_index = 0; target_mac_index < `AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS; target_mac_index++) begin
                for(int byte_index = 0; byte_index < target_address_width_in_bytes; byte_index++) begin
                    int unsigned client_data_index = target_address_starting_index + (target_mac_index * target_address_width_in_bytes) + byte_index;
                    client_data[client_data_index] = temp_data[byte_index];
                end
            end
        end
    endfunction

    //extract the information such as magic packet synchronization stream and target address in the client data 
    virtual function void get_useful_info_from_client_data();
        int unsigned local_synch_stream_starting_index;
        amiq_eth_data local_synch_stream[];
        amiq_eth_address local_target_mac;
        amiq_eth_data local_password[$];
        bit success = 0;

        local_synch_stream = { >> {`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM} };

        begin
            int unsigned client_data_index = 0;
            int synch_stream_index = 0;

            while(client_data_index < client_data.size()) begin
                if(synch_stream_index < (`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8)) begin
                    //synchronization stream was not found

                    int starting_index = client_data_index;

                    for(synch_stream_index = 0; synch_stream_index < (`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8); synch_stream_index++) begin
                        if(client_data[client_data_index] != local_synch_stream[synch_stream_index]) begin
                            client_data_index = starting_index + 1;

                            if(synch_stream_index > 0) begin
                                `uvm_info("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH)
                            end

                            synch_stream_index = 0;

                            break;
                        end
                        else begin
                            if(synch_stream_index == 0) begin
                                local_synch_stream_starting_index = client_data_index;
                            end

                            client_data_index++;
                        end
                    end

                    if(synch_stream_index >= (`AMIQ_ETH_MAGIC_PACKET_SYNCH_STREAM_WIDTH / 8)) begin
                        amiq_eth_data target_mac_array[];
                        bit target_mac_byte_mismatch_detected = 0;
                        int unsigned target_mac_bytes_number = $bits(target_mac) / 8;

                        `uvm_info("AMIQ_ETH", $sformatf("Identified a synchronization stream starting from index: %0d, client_data_index: %0d",
                                local_synch_stream_starting_index, client_data_index), UVM_HIGH)

                        for(int target_mac_index = 0; target_mac_index < target_mac_bytes_number; target_mac_index++) begin
                            target_mac_array = new[target_mac_array.size() + 1] (target_mac_array);
                            target_mac_array[target_mac_array.size() - 1] = client_data[client_data_index];
                            for(int target_mac_repetition_index = 0; target_mac_repetition_index < `AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS; target_mac_repetition_index++) begin
                                int current_index = client_data_index + ((target_mac_repetition_index * target_mac_bytes_number));

                                if(target_mac_array[target_mac_array.size() - 1] != client_data[current_index]) begin
                                    `uvm_info("AMIQ_ETH", $sformatf("target MAC mismatch target_mac_array[%0d]: %X, client_data[%0d]: %X",
                                            target_mac_array.size() - 1, target_mac_array[target_mac_array.size() - 1], current_index, client_data[current_index]), UVM_HIGH)

                                    target_mac_byte_mismatch_detected = 1;
                                    synch_stream_index = 0;
                                    client_data_index = starting_index + 1;
                                    target_mac_array = new[0];

                                    `uvm_info("AMIQ_ETH", $sformatf("Synchronization lost - restarting at index %0d...", client_data_index), UVM_HIGH)
                                    break;
                                end
                            end

                            if(target_mac_byte_mismatch_detected == 1) begin
                                break;
                            end
                            else begin
                                client_data_index++;
                            end
                        end

                        if(target_mac_byte_mismatch_detected == 1) begin
                            continue;
                        end
                        else begin
                            client_data_index = client_data_index + (target_mac_bytes_number * (`AMIQ_ETH_MAGIC_PACKET_TARGET_MAC_REPETITIONS - 1));
                            local_target_mac = { >> {target_mac_array}};
                            `uvm_info("AMIQ_ETH", $sformatf("Identified a target MAC: %0X", local_target_mac), UVM_HIGH)

                            synch_stream_starting_index = local_synch_stream_starting_index;
                            target_mac = local_target_mac;
                            success = 1;

                            begin
                                int unsigned local_password_size = 0;
                                if(client_data_index < client_data.size() - 6) begin
                                    local_password_size = 6;
                                end
                                else if(client_data_index < client_data.size() - 4) begin
                                    local_password_size = 4;
                                end
                                else begin
                                    break;
                                end

                                begin
                                    password = new[local_password_size];

                                    for(int password_index = 0; password_index < local_password_size; password_index++) begin
                                        password[password_index] = client_data[client_data_index + password_index];
                                    end

                                    break;
                                end

                            end
                        end
                    end
                end
                else begin
                    //synchronization stream was found - the code should never get in this part
                    `uvm_fatal("AMIQ_ETH", $sformatf("Problem in the algorithm - code should never get here"));
                end

            end

        end

        if(success != 1) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Could not find Magic pattern and Target MAC in the payload of packet: %s", convert2string()));
        end

    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        set_useful_info_in_client_data();
        super.do_pack(packer);
        
        if(pack_client_data_size) begin
            `uvm_pack_int(client_data_size)
        end
        
        for(int i = 0; i < client_data_size; i++) begin
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
        for(int i = 0; i < client_data_size; i++) begin
            amiq_eth_data local_data;
            `uvm_unpack_int(local_data);
            client_data[i] = local_data;
        end
        
        if(pack_fcs) begin
            do_unpack_fcs(packer);
        end
        
        get_useful_info_from_client_data();

        if(ether_type != AMIQ_ETH_WAKE_ON_LAN) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("ether_type (%s) is different then AMIQ_ETH_WAKE_ON_LAN", ether_type.name()))
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
        
        result = $sformatf("%s%sStarting Index: %0d", result, `AMIQ_ETH_FIELD_SEPARATOR, synch_stream_starting_index);
        result = $sformatf("%s%sTarget MAC: %012X", result, `AMIQ_ETH_FIELD_SEPARATOR, target_mac);
        result = $sformatf("%s%spassword.size(): %0d", result, `AMIQ_ETH_FIELD_SEPARATOR, password.size());
        result = $sformatf("%s%sclient_data.size(): %0d", result, `AMIQ_ETH_FIELD_SEPARATOR, client_data.size());
        result = $sformatf("%s%sFCS: %X, %s", result, `AMIQ_ETH_FIELD_SEPARATOR, fcs, fcs_info);

        return result;
    endfunction

    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_MAGIC_CODE);

        return result;
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_magic casted_rhs;

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(client_data_size != casted_rhs.client_data_size) begin
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
        
        if(synch_stream_starting_index != casted_rhs.synch_stream_starting_index) begin
            return 0;
        end

        if(target_mac != casted_rhs.target_mac) begin
            return 0;
        end

        for(int i = 0; i < password.size(); i++) begin
            if(i < casted_rhs.password.size()) begin
                if(client_data[i] != casted_rhs.client_data[i]) begin
                    return 0;
                end
            end
            else begin
                break;
            end
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