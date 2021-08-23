/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/

// The wav APB agent.
class wav_APB_agent extends uvm_agent;

  protected int id;

  `uvm_component_utils_begin(wav_APB_agent)
    `uvm_field_int(id, UVM_DEFAULT)
  `uvm_component_utils_end

  wav_APB_driver driver;
  wav_APB_sequencer sequencer;
  wav_APB_monitor monitor;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = wav_APB_monitor::type_id::create("monitor", this);

    if(get_is_active() == UVM_ACTIVE) begin
	 `uvm_info(get_type_name(), $psprintf("APB Agent is UVM_ACTIVE"), UVM_MEDIUM);
      sequencer = wav_APB_sequencer::type_id::create("sequencer", this);
      driver = wav_APB_driver::type_id::create("driver", this);
    end
  endfunction

  function void set_interface(wav_APB_vif vif_a);
    if(driver != null) begin
      driver.set_interface(vif_a);
    end
    monitor.set_interface(vif_a);
  endfunction : set_interface

  function void connect_phase(uvm_phase phase);
    if(get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass
