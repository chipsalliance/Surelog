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
 * NAME:        amiq_eth_ve_test_packets.sv
 * PROJECT:     amiq_eth
 * Description: This file declares generic test for driving Ethernet packets.
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_TEST_PACKETS
    //protection against multiple includes
    `define __AMIQ_ETH_VE_TEST_PACKETS

//test class which sends random packets to System-C side
virtual class amiq_eth_ve_test_packets extends amiq_eth_ve_test_basic;
    
    int unsigned number_of_packets = 1000;

    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);
    endfunction
    
    //generate correct type of ethernet class
    //@return ethernet packet
    pure virtual function amiq_eth_packet generate_random_packet();

    //UVM run phase
    //@param phase - current phase
    task run_phase(uvm_phase phase);
        integer file_txt = $fopen("wireshark_file.txt"); 
        amiq_eth_pcap_livestream livestream = new(`AMIQ_ETH_WIRESHARK_FILE);
        phase.raise_objection(this, "Start of test");
        begin
            for(int i = 0; i < number_of_packets; i++) begin
                amiq_eth_packet packet = generate_random_packet();
                $fdisplay(file_txt, {packet.to_wireshark_string(),"\n"});
                livestream.broadcast(packet);
                env.set(packet);
            end
        end
        
        $fclose(file_txt);
        livestream.stop();

        #100;
        phase.drop_objection(this, "Start of test");
    endtask    
endclass

`endif
