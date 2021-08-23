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

// The  wav APB monitor.
class wav_APB_monitor extends uvm_monitor;

  // Virtual interface used to view HDL signals.
  protected wav_APB_vif vif;

  // Agent id.
  protected int id;
  // Control whether checks are enabled.
  bit checks_enable  = 1;
  bit monitor_enable = 1;
  // Control whether coverage is enabled.
  bit coverage_enable = 0;

  bit set_inf_done;

  // Collected transfer.
  protected wav_APB_transfer trans_collected;
  protected wav_APB_transfer trans_collected_cloned;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(wav_APB_transfer) item_collected_port;

  // Trigger event for the collected transfer covergroup.
  protected event collected_transfer_event;

  `uvm_component_utils_begin(wav_APB_monitor)
    `uvm_field_int(id, UVM_DEFAULT)
    `uvm_field_int(checks_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  function new (string name, uvm_component parent);
    super.new(name, parent);

    // Init the collected data.
    trans_collected = new();

    // Allocate the ports.
    item_collected_port = new("item_collected_port", this);

    // Allocate the covergroups.
    //collected_transfer_covergroup = new();
    //collected_transfer_covergroup.set_inst_name({get_full_name(), ".cov_trans"});
  endfunction

  function void build_phase(uvm_phase phase);
    // Check the virtual interface.
    `ifndef WAV_BCS_VIP
    if(!uvm_config_db#(virtual wav_APB_if)::get(this, "", "APB_vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".APB_vif"});
    `endif
    set_inf_done = 1;
  endfunction

  function void set_interface(wav_APB_vif vif_a);
    if(vif_a == null) `uvm_error(get_type_name(), $psprintf("set_interface - vif null; pwdata : %0h", vif_a.pwdata))
    else `uvm_info(get_type_name(), $psprintf("set_interface - vif; pwdata : %0h", vif_a.pwdata), UVM_NONE)
    vif = vif_a;
    set_inf_done = 0;
  endfunction : set_interface

  //-----RUN PHASE
  virtual task run_phase(uvm_phase phase);
    `ifdef WAV_BCS_VIP
      if(set_inf_done)
        `uvm_fatal("NOVIF",{"set_inf - virtual interface must be set for: ",get_full_name(),".APB_vif"});
    `endif

   forever begin
     if(monitor_enable) begin
       fork
        monitor_reset_done();
        collect_transfers();
       join
     end //end if
   end //end forever

  endtask
   // Monitors the reset.
  task monitor_reset_done();
    fork
      forever begin
        @(negedge vif.reset);
      end
    join
  endtask

  // Collects transfers.
  virtual protected task collect_transfers();

       //`uvm_info(get_type_name(), $psprintf("Begin Transfer collection"), UVM_DEBUG)

    forever begin
      collect_transfer();

      //`uvm_info(get_type_name(), $psprintf("Transfer collected :\n%s", trans_collected.sprint()), UVM_DEBUG)

    end
  endtask

  // Collects a transfer.
  task collect_transfer();
    //@(posedge vif.clock iff vif.reset === 0);
    //void'(this.begin_tr(trans_collected));
    //`uvm_info(get_type_name(), $psprintf("1. Collection started,waiting on p_sel:%d",vif.psel), UVM_DEBUG)

    @(posedge vif.pclk);

    //Wait until a transfer is initialized
    while (vif.psel !== 1) begin
     @(posedge vif.pclk);
   //  `uvm_info(get_type_name(), $psprintf("2. Inside While: Waiting on p_sel:%d",vif.psel), UVM_DEBUG)
    end

    //`uvm_info(get_type_name(), $psprintf("3. PSEL ASSSERTED.Collection continues..."), UVM_DEBUG)

    //`uvm_info(get_type_name(), $psprintf("4. WAIT FOR PENABLE p_enable:%d",vif.penable), UVM_DEBUG)

    // wait(vif.psel);
    @(posedge vif.penable);

    //`uvm_info(get_type_name(), $psprintf("5. Collection continues,p_enable asserted:%d",vif.penable), UVM_DEBUG)

    // @(posedge vif.pclk) begin
     trans_collected.addr      = vif.paddr;
     trans_collected.direction = apb_direction_enum'(vif.pwrite);
     trans_collected.prot      = vif.pprot;
     trans_collected.strb      = vif.pstrb;
     trans_collected.err       = vif.pslverr;
    // end

    if(vif.pwrite)
     trans_collected.data = vif.pwdata;

   // item_collected_port.write(trans_collected);

     wait(vif.pready);
     if(trans_collected.direction == APB_READ) begin
      @(negedge vif.pclk);
    	trans_collected.data = vif.prdata;
     end

     //item_collected_port.write(trans_collected);

     // Clone and publish the cloned collected_transfer to the subscribers
       $cast(trans_collected_cloned, trans_collected.clone());
       item_collected_port.write(trans_collected_cloned);
     //  this.end_tr(trans_collected);

      @(negedge vif.penable);
   //  @(posedge vif.pclk);

  endtask

  // Performs transfer checks.
 // virtual protected function void perform_transfer_checks();
 //   if (checks_enable) begin
      // TODO Implement wav_APB_monitor.perform_transfer_checks()
 //   end
 // endfunction

  // Performs transfer coverage.
 // virtual protected function void perform_transfer_coverage();
 //   if (coverage_enable) begin
      // TODO Implement wav_APB_monitor.perform_transfer_coverage()
      // For example:
 //     -> collected_transfer_event;
 //   end
 // endfunction

  // Covergroup for the collected transfer.
  //covergroup collected_transfer_covergroup @collected_transfer_event;
  //  option.per_instance = 1;
    // TODO Add coverage items for wav_APB_monitor.collected_transfer_covergroup
    // For example:
  //  data : coverpoint trans_collected.data;
    // FIXME here we should use some bins
  //endgroup

endclass
