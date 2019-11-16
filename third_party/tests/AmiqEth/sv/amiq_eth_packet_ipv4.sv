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
 * NAME:        amiq_eth_packet_ipv4.sv
 * PROJECT:     amiq_eth
 * Description: This file declare the IPV4 Ethernet packet. 
 *                 Implementation is done based on: http://en.wikipedia.org/wiki/Internet_Protocol_version_4
 *******************************************************************************/

`ifndef __AMIQ_ETH_PACKET_IPV4
    //protection against multiple includes
    `define __AMIQ_ETH_PACKET_IPV4

//Ethernet IPV4 packet header
class amiq_eth_packet_ipv4_header extends uvm_object;
    `uvm_object_utils(amiq_eth_packet_ipv4_header)

    //Version
    rand amiq_eth_ipv4_header_version version;

    constraint version_c {
        version == `AMIQ_ETH_IPV4_HEADER_VERSION_VALUE;
    }

    //Internet Header Length (IHL)
    rand amiq_eth_ipv4_header_ihl ihl;

    constraint ihl_c {
        ihl >= `AMIQ_ETH_MINIMUM_HEADER_LENGTH_IN_WORDS;
    }

    //Differentiated Services Code Point (DSCP)
    rand amiq_eth_ipv4_header_dscp dscp;

    //Explicit Congestion Notification (ECN)
    rand amiq_eth_ipv4_header_ecn ecn;

    //Total Length
    rand amiq_eth_ipv4_header_total_length total_length;

    constraint total_length_c {
        total_length >= (ihl * 4) & total_length <= `AMIQ_ETH_IPV4_REQUIRED_REASSEMBLE_LENGTH;
    }

    //Identification
    rand amiq_eth_ipv4_header_identification identification;

    //Flags
    rand amiq_eth_ipv4_header_flags flags;

    //Fragment Offset
    rand amiq_eth_ipv4_header_fragment_offset fragment_offset;

    //Time To Live (TTL)
    rand amiq_eth_ipv4_header_ttl ttl;

    //Protocol
    rand amiq_eth_ipv4_header_protocol protocol;

    //Header Checksum
    rand amiq_eth_ipv4_header_checksum checksum;

    //determine if to use the correct checksum or not
    rand bit use_correct_checksum;

    constraint use_correct_checksum_c {
        use_correct_checksum == 1;
    }

    //Source address
    rand amiq_eth_ipv4_header_source_ip_address source_ip_address;

    //Destination address
    rand amiq_eth_ipv4_header_destination_ip_address destination_ip_address;

    //Options
    rand amiq_eth_ipv4_header_option options[];
    
    constraint options_c {
        solve  ihl before options;
        options.size() == (ihl - get_minimum_header_length_in_words());
    }

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
    endfunction

    //get the minimum length of the header, in bits
    //@return the minimum length of the header, in bits
    virtual function int unsigned get_minimum_header_length_in_bits();
        return (`AMIQ_ETH_MINIMUM_HEADER_LENGTH_IN_BITS);
    endfunction

    //get the minimum length of the header, in bytes
    //@return the minimum length of the header, in bytes
    virtual function int unsigned get_minimum_header_length_in_bytes();
        return (get_minimum_header_length_in_bits() / 8);
    endfunction

    //get the minimum length of the header, in words
    //@return the minimum length of the header, in words
    virtual function int unsigned get_minimum_header_length_in_words();
        return (get_minimum_header_length_in_bits() / 32);
    endfunction
    
    //get the header length in bytes
    //@return the header length in bytes
    virtual function int unsigned get_header_length_in_bytes();
        return (ihl * 4);
    endfunction
    
    //get the options size in words
    //@param local_ihl - Internet Header Length (IHL)
    //@return the options size in words
    virtual function int unsigned get_options_size_in_words(amiq_eth_ipv4_header_ihl local_ihl);
        if(local_ihl < get_minimum_header_length_in_words()) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Internet Header Length (%0d) should be bigger or equal then Minimum Header Length in words (%0d) - AMIQ_ETH_MINIMUM_HEADER_LENGTH_IN_WORDS: %0d", 
                local_ihl, get_minimum_header_length_in_words(), `AMIQ_ETH_MINIMUM_HEADER_LENGTH_IN_WORDS));
            return 0;
        end
        
        return (local_ihl - get_minimum_header_length_in_words());
    endfunction
    
    //get the data length in bytes
    //@return the data length in bytes
    virtual function int unsigned get_data_length_in_bytes();
        if(total_length < get_header_length_in_bytes()) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Total Length (%0d) should be bigger or equal to IHL in bytes (%0d)", total_length, get_header_length_in_bytes()));    
        end
        
        return (total_length - get_header_length_in_bytes());
    endfunction

    //pack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_pack(uvm_packer packer);
        `uvm_pack_int(version);
        `uvm_pack_int(ihl);
        `uvm_pack_int(dscp);
        `uvm_pack_int(ecn);
        `uvm_pack_int(total_length);
        `uvm_pack_int(identification);
        `uvm_pack_int(flags);
        `uvm_pack_int(fragment_offset);
        `uvm_pack_int(ttl);
        `uvm_pack_int(protocol);
        `uvm_pack_int(checksum);
        `uvm_pack_int(source_ip_address);
        `uvm_pack_int(destination_ip_address);
        
        for (int index = 0; index < options.size(); index++) begin
            `uvm_pack_int(options[index]);
        end
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        `uvm_unpack_int(version);
        `uvm_unpack_int(ihl);
        `uvm_unpack_int(dscp);
        `uvm_unpack_int(ecn);
        `uvm_unpack_int(total_length);
        `uvm_unpack_int(identification);
        `uvm_unpack_int(flags);
        `uvm_unpack_int(fragment_offset);
        `uvm_unpack_int(ttl);
        `uvm_unpack_int(protocol);
        `uvm_unpack_int(checksum);
        `uvm_unpack_int(source_ip_address);
        `uvm_unpack_int(destination_ip_address);

        begin
            int unsigned minimum_header_length = get_minimum_header_length_in_words();

            if(ihl < get_minimum_header_length_in_words()) begin
                `uvm_fatal("AMIQ_ETH", $sformatf("Internet Header Length (%0d) should be bigger or equal to minimum length (%0d)", ihl, minimum_header_length))
            end

            options = new[ihl - minimum_header_length];

            `uvm_unpack_array(options);
        end
    endfunction
    
    //get an easy-to-read string containing the IP value
    //@param address - the IP address
    //@return easy-to-read string containing the IP value
    local function string get_printable_ip(bit[31:0] address);
        string result = "";
        
        for(int i = 3; i >= 0; i--) begin
            byte unsigned data = (address >> (8 * i)) & 8'hFF;
            result = $sformatf("%s%0d%s", result, data, ((i > 0) ? "." : ""));
        end
        
        return result;
    endfunction

    //converts the information containing in the instance of this class to an easy-to-read string
    //@return easy-to-read string with the information contained in the instance of this class
    virtual function string convert2string();
        string source_ip = get_printable_ip(source_ip_address);
        string destination_ip = get_printable_ip(destination_ip_address);
        
        return $sformatf("Version: %X%sIHL: %0d%sDSCP: %X%sECN: %X%sTotal Length: %0d%sIdentification: %X%sFlags: %X%sFragment Offset: %X%sTTL: %0d%sProtocol: %0d%sChecksum: %X%sSource IP: %s%sDestination IP: %s%sOptions size: %0d",
            version, `AMIQ_ETH_FIELD_SEPARATOR,
            ihl, `AMIQ_ETH_FIELD_SEPARATOR,
            dscp, `AMIQ_ETH_FIELD_SEPARATOR,
            ecn, `AMIQ_ETH_FIELD_SEPARATOR,
            total_length, `AMIQ_ETH_FIELD_SEPARATOR,
            identification, `AMIQ_ETH_FIELD_SEPARATOR,
            flags, `AMIQ_ETH_FIELD_SEPARATOR,
            fragment_offset, `AMIQ_ETH_FIELD_SEPARATOR,
            ttl, `AMIQ_ETH_FIELD_SEPARATOR,
            protocol, `AMIQ_ETH_FIELD_SEPARATOR,
            checksum, `AMIQ_ETH_FIELD_SEPARATOR,
            source_ip, `AMIQ_ETH_FIELD_SEPARATOR,
            destination_ip, `AMIQ_ETH_FIELD_SEPARATOR,
            options.size());
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ipv4_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(ihl != casted_rhs.ihl) begin
            return 0;
        end

        if(dscp != casted_rhs.dscp) begin
            return 0;
        end

        if(ecn != casted_rhs.ecn) begin
            return 0;
        end

        if(total_length != casted_rhs.total_length) begin
            return 0;
        end

        if(identification != casted_rhs.identification) begin
            return 0;
        end

        if(flags != casted_rhs.flags) begin
            return 0;
        end

        if(fragment_offset != casted_rhs.fragment_offset) begin
            return 0;
        end

        if(ttl != casted_rhs.ttl) begin
            return 0;
        end

        if(protocol != casted_rhs.protocol) begin
            return 0;
        end

        if(checksum != casted_rhs.checksum) begin
            return 0;
        end

        if(source_ip_address != casted_rhs.source_ip_address) begin
            return 0;
        end

        if(destination_ip_address != casted_rhs.destination_ip_address) begin
            return 0;
        end

        if(options.size() != casted_rhs.options.size()) begin
            return 0;
        end

        for(int i = 0; i < options.size(); i++) begin
            if(options[i] != casted_rhs.options[i]) begin
                return 0;
            end
        end

        return 1;
    endfunction

    //copy the right hand side class instance to this current instance
    //@param rhs - Right Hand Side object
    function void copy(uvm_object rhs);
        amiq_eth_packet_ipv4_header casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            `uvm_fatal("AMIQ_ETH", "Could not cast object to a amiq_eth_packet_ipv4_header");
        end

        version = casted_rhs.version;
        ihl = casted_rhs.ihl;
        dscp = casted_rhs.dscp;
        ecn = casted_rhs.ecn;
        total_length = casted_rhs.total_length;
        identification = casted_rhs.identification;
        flags = casted_rhs.flags;
        fragment_offset = casted_rhs.fragment_offset;
        ttl = casted_rhs.ttl;
        protocol = casted_rhs.protocol;
        checksum = casted_rhs.checksum;
        source_ip_address = casted_rhs.source_ip_address;
        destination_ip_address = casted_rhs.destination_ip_address;
        options = new[casted_rhs.options.size()];

        for(int i = 0; i < options.size(); i++) begin
            options[i] = casted_rhs.options[i];
        end

    endfunction

    //get the correct checksum
    //@return returns the value of the correct checksum
    virtual function amiq_eth_ipv4_header_checksum get_correct_checksum();
        //this logic is based on wiki - http://en.wikipedia.org/wiki/IPv4_header_checksum
        amiq_eth_packet_ipv4_header header;
        bit unsigned bitstream[];
        bit[31:0] halfwords_sum = 0;
        bit[15:0] halfwords[];


        header = amiq_eth_packet_ipv4_header::type_id::create("header");
        header.copy(this);
        header.checksum = 0;

        void'(header.pack(bitstream));

        if(bitstream.size() != ihl * 32) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Bit stream size error detected - expected: %0d, received: %0d",
                    ihl * 32, bitstream.size()));
        end
        
        halfwords = { >> {bitstream}};

        if(halfwords.size() != (2 * ihl)) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Halfwords size error detected - expected: %0d, received: %0d",
                    (2 * ihl), halfwords.size()));
        end

        for(int i = 0; i < halfwords.size(); i++) begin
            halfwords_sum += halfwords[i];
        end
        
        get_correct_checksum = halfwords_sum[31:16] + halfwords_sum[15:0];
        get_correct_checksum = ~get_correct_checksum;
    endfunction

    function void post_randomize();
        if(use_correct_checksum == 1) begin
            checksum = get_correct_checksum();
        end
    endfunction

endclass

//Ethernet IPV4 packet
class amiq_eth_packet_ipv4 extends amiq_eth_packet_ether_type;
    `uvm_object_utils(amiq_eth_packet_ipv4)

    //header
    rand amiq_eth_packet_ipv4_header header;

    //data
    rand amiq_eth_data data[];
    
    //Pad field
    rand amiq_eth_data pad[];
    
    //Frame Check Sequence
    rand amiq_eth_fcs fcs;
    
    //determine if to use the correct fcs or not
    rand bit use_correct_fcs;

    constraint use_correct_fcs_c {
        use_correct_fcs == 1;
    }

    //flag to determine if to pack/unpack the pad
    local bit pack_pad;
    
    //flag to determine if to pack/unpack the fcs
    local bit pack_fcs;
    
    //get the pad size based on the value of the input parameters
    //@param min_frame_size - minimum frame size
    //@param - header - Ethernet IPV4 packet header
    //@return the pad size
    virtual function int unsigned get_pad_size_by_fields(int min_frame_size, amiq_eth_packet_ipv4_header header);
        int unsigned value = ((header.total_length + (2 * (`AMIQ_ETH_ADDRESS_WIDTH / 8)) + 6));
        
        if(min_frame_size >= value) begin
            return (min_frame_size - value);    
        end
        else begin
            return 0;
        end
    endfunction
    
    //get the pad size
    //@return the pad size
    virtual function int unsigned get_pad_size();
        return get_pad_size_by_fields(min_frame_size, header);
    endfunction
    
    constraint pad_c {
        solve header.total_length before pad;
        foreach (pad[i]) { 
            pad[i] == 8'hFF; 
        }
        pad.size() == (min_frame_size - ((header.total_length + (2 * (`AMIQ_ETH_ADDRESS_WIDTH / 8)) + 6)));
    }
    
    //get data length in bytes
    //@param local_header - Ethernet IPV4 packet header
    //@return data length in bytes
    virtual function int unsigned get_data_length_in_bytes(amiq_eth_packet_ipv4_header local_header);
        if(local_header.total_length < local_header.get_header_length_in_bytes()) begin
            `uvm_fatal("AMIQ_ETH", $sformatf("Total Length (%0d) should be bigger or equal to IHL in bytes (%0d)", local_header.total_length, local_header.get_header_length_in_bytes()));    
        end
        
        return (local_header.total_length - local_header.get_header_length_in_bytes());
    endfunction
    
    constraint data_c {
        data.size() == (header.total_length - (header.ihl * 4));
    }

    //constructor
    //@param name - the name assigned to the instance of this class
    function new(string name = "");
        super.new(name);
        ether_type = AMIQ_ETH_IPV4;
        header = amiq_eth_packet_ipv4_header::type_id::create("header");
        pack_pad = 1;
        pack_fcs = 1;
    endfunction
    
    //pack data field
    //@param packer - the packer used by this function
    virtual function void do_pack_data(uvm_packer packer);
        for (int index = 0; index < data.size(); index++) begin
            `uvm_pack_int(data[index]);
        end
    endfunction
    
    //unpack data field
    //@param packer - the packer used by this function
    virtual function void do_unpack_data(uvm_packer packer);
        data = new[header.get_data_length_in_bytes()];        
        for (int index = 0; index < data.size(); index++) begin
            `uvm_unpack_int(data[index]);
        end
    endfunction
    
    //pack pad field
    //@param packer - the packer used by this function
    virtual function void do_pack_pad(uvm_packer packer);
        for (int index = 0; index < pad.size(); index++) begin
            `uvm_pack_int(pad[index]);
        end
    endfunction
    
    //unpack pad field
    //@param packer - the packer used by this function
    virtual function void do_unpack_pad(uvm_packer packer);
        int pad_size = get_pad_size();
        
        pad = new[pad_size];        
        for (int index = 0; index < pad_size; index++) begin
            `uvm_unpack_int(pad[index]);
        end
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
        header.do_pack(packer);
        do_pack_data(packer);
        
        if(pack_pad) begin
            do_pack_pad(packer);
        end
        
        if(pack_fcs) begin
            do_pack_fcs(packer);
        end
        
    endfunction

    //unpack the entire Ethernet packet
    //@param packer - the packer used by this function
    virtual function void do_unpack(uvm_packer packer);
        super.do_unpack(packer);
        header.do_unpack(packer);
        do_unpack_data(packer);
        
        if(pack_pad) begin
            do_unpack_pad(packer);
        end
        
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
        
        return $sformatf("%s%s%s%sdata size: %0d%spad.size(): %0d%sFCS: %0X - %s",
            super.convert2string(), `AMIQ_ETH_FIELD_SEPARATOR,
            header.convert2string(), `AMIQ_ETH_FIELD_SEPARATOR,
            data.size(), `AMIQ_ETH_FIELD_SEPARATOR,
            pad.size(), `AMIQ_ETH_FIELD_SEPARATOR,
            fcs, fcs_info);
    endfunction

    //compares the current class instance with the one provided as an argument
    //@param rhs - Right Hand Side object
    //@param comparer - The UVM comparer object used in evaluating this comparison - default is "null"
    //@return 1 - objects are the same, 0 - objects are different
    virtual function bit compare (uvm_object rhs, uvm_comparer comparer=null);
        amiq_eth_packet_ipv4 casted_rhs;

        if($cast(casted_rhs, rhs) == 0) begin
            return 0;
        end

        if(super.compare(rhs, comparer) == 0) begin
            return 0;
        end

        if(header.compare(casted_rhs.header, comparer) == 0) begin
            return 0;
        end

        if(data.size() != casted_rhs.data.size()) begin
            return 0;
        end

        for(int i = 0; i < data.size(); i++) begin
            if(data[i] != casted_rhs.data[i]) begin
                return 0;
            end
        end

        if(pad.size() != casted_rhs.pad.size()) begin
            return 0;
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
    
    //function for packing the Ethernet packet into an UVM generic payload class
    //@return an instance of the UVM generic payload containing the packed Ethernet packet
    virtual function uvm_tlm_generic_payload to_generic_payload();
        uvm_tlm_generic_payload result = super.to_generic_payload();
        result.set_address(`AMIQ_ETH_PACKET_IPV4_CODE);
        
        return result;
    endfunction
    
    function void post_randomize();
        //calling header.post_randomize() is necessary here in order to ensure that the checksum from the header
        //is computed - normally header.post_randomize() will be called after this.post_randomize()
        header.post_randomize();
        if(use_correct_fcs == 1) begin
            fcs = get_correct_fcs();
        end
    endfunction
    
    //function for packing the Ethernet packet using only the required information for computing the FCS
    //@param bitstream - the packed bit stream is placed in "bitstream" parameter
    virtual function void pack_for_fcs(ref bit bitstream[]);
        bit current_pack_pad = pack_pad;
        bit current_pack_fcs = pack_fcs;
        
        pack_pad = 0;
        pack_fcs = 0;
        
        super.pack_for_fcs(bitstream);
        
        pack_pad = current_pack_pad;
        pack_fcs = current_pack_fcs;
    endfunction
    
endclass

`endif