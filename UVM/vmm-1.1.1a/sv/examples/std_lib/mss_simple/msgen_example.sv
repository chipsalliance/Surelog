//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


`include "vmm.sv"
`include "atm_cell.sv"

constraint atm_cell::test {
   payload[0] == stream_id;
   payload[1] == scenario_id % 256;
   payload[2] == data_id % 256;
}

class my_atm_cell_scenario extends atm_cell_scenario;
    local bit [7:0] id;

    function new(bit [7:0] id);
        super.new();
        this.id = id;
        void'(this.define_scenario("MY CELL SCENARIO", 1));
    endfunction

    function void post_randomize();
        `foreach (this.items,i)
            items[i].gfc = this.id;
    endfunction
endclass: my_atm_cell_scenario


class cpu extends vmm_data;
   typedef enum {OP_DIRECT, OP_IMMEDIATE,
                 JMP_RELATIVE, JMP_ABSOLUTE, JMP_INDIRECT,
                 IMPLICIT, OTHER} addr_mode_t;
   rand addr_mode_t addr_mode;

   `vmm_data_member_begin(cpu)
      `vmm_data_member_enum(addr_mode, vmm_data::DO_ALL);
   `vmm_data_member_end(cpu)
endclass
`vmm_channel(cpu)
`vmm_scenario_gen(cpu, "CPU INSN")

class my_cpu_scenario extends cpu_scenario;
    function new();
        super.new();
        void'(this.define_scenario("MY CPU SCENARIO", 1));
    endfunction

    constraint op_direct {
      foreach(items[i]) {
        items[i].addr_mode == cpu::OP_IMMEDIATE |
        items[i].addr_mode == cpu::OP_DIRECT;
      }
    }
endclass: my_cpu_scenario
    
class my_scenario extends vmm_ms_scenario;
    my_atm_cell_scenario atm_scenario;
    my_cpu_scenario cpu_scenario;

    int MSC = this.define_scenario("Multistream SCENARIO", 0);
    local bit [7:0] id;

    function new(bit [7:0] id);
        super.new(null);
        atm_scenario = new(id);
        cpu_scenario = new();
        this.id = id;
    endfunction: new

    task execute(ref int n);
        fork
          begin
             atm_cell_channel out_chan;
             int unsigned nn = 0;
             $cast(out_chan, this.get_channel("ATM_SCENARIO_CHANNEL"));
             atm_scenario.randomize() with {atm_scenario.length == 1;};
             atm_scenario.apply(out_chan, nn);
             n += nn;
          end
          begin
             cpu_channel out_chan;
             int unsigned nn = 0;
             $cast(out_chan,this.get_channel("CPU_SCENARIO_CHANNEL"));
             cpu_scenario.randomize() with {cpu_scenario.length == 1;};
             cpu_scenario.apply(out_chan, nn);
             n += nn;
          end
        join
    endtask: execute
endclass: my_scenario

program test;
    vmm_log log;
    vmm_ms_scenario_gen gen;

    my_scenario sc0;

    atm_cell_channel atm_chan;
    cpu_channel      cpu_chan;

    bit [7:0] last_hec = 8'hFF;
    bit [4095:0] cpu_tr;

initial
  begin
     log = new("Multistream Scenario Simple Example", "Program");
     gen = new("Multistream Scenario Gen", 7);

     sc0 = new(0);

     atm_chan = new("ATM CELL CHANNEL", "TEST");
     cpu_chan = new("CPU CELL CHANNEL", "TEST");

     gen.register_channel("ATM_SCENARIO_CHANNEL", atm_chan);
     gen.register_channel("CPU_SCENARIO_CHANNEL", cpu_chan);
     gen.register_ms_scenario("SCENARIO_0", sc0);
     
     `vmm_note(log, "Checking ms_gen with 2 streams (ATM, CPU)");
     
     gen.stop_after_n_scenarios = 10;
     
     fork
        forever begin
           atm_cell ac;
	   atm_chan.get(ac);
	   ac.display("AtmCell: ");
        end
        forever begin
           cpu cc;
           cpu_chan.get(cc);
	   cc.display("Cpu: ");
        end
     join_none

     gen.start_xactor();
     gen.notify.wait_for(vmm_ms_scenario_gen::DONE);
     #100;

     log.report();
  end

endprogram


