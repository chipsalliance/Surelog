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

// The  wav APB driver.
class wav_APB_driver extends uvm_driver #(wav_APB_transfer);

  // Virtual interfaced used to drive and view HDL signals.
  protected wav_APB_vif vif;

  // Agent id.
  protected int id;

  bit set_inf_done;
  wav_APB_Agent_config cfg;
  bit [9:0] prdy_dly;

  bit apb_master;
  `uvm_component_utils_begin(wav_APB_driver)
    `uvm_field_int(id, UVM_DEFAULT)
  `uvm_component_utils_end

  function new (string name, uvm_component parent);
    super.new(name, parent);
    apb_master = 1;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    `ifndef WAV_BCS_VIP
    // Check the virtual interface.
    if(!uvm_config_db#(virtual wav_APB_if)::get(this, "", "APB_vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".APB_vif"});
    `endif
    set_inf_done = 1;
    if(!uvm_config_db#(bit)::get(this, "", "apb_master", apb_master)) apb_master= 1;

    cfg= wav_APB_Agent_config::type_id::create("cfg", this);
  endfunction

  function void set_interface(wav_APB_vif vif_a);
    vif = vif_a;
    set_inf_done = 0;
  endfunction : set_interface

  virtual task run_phase(uvm_phase phase);
    `ifdef WAV_BCS_VIP
      if(set_inf_done)
        `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".APB_vif"});
    `endif

    //reset_signals();

    fork
      reset_signals();
      if(apb_master) get_and_drive();
      else drive_as_slave();
    join
  endtask

  // Resets signals.
  virtual protected task reset_signals();
    forever begin
      @(posedge vif.reset);
      //`uvm_info(get_type_name(),$psprintf("Resetting APB Driver"), UVM_DEBUG)
      vif.mp_drv.cb_drv.pwdata  <= 'd0;
      vif.mp_drv.cb_drv.paddr   <= 0;
      vif.mp_drv.cb_drv.penable <= 0;
      vif.mp_drv.cb_drv.psel    <= 0;
      vif.mp_drv.cb_drv.pwrite  <= 0;
    end
  endtask

  // Drives transfers.
  virtual protected task get_and_drive();
    @(negedge vif.reset);
    forever begin
      //@(negedge vif.pclk);
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      //`uvm_info(get_type_name(),$psprintf("wav_APB %1d start driving transfer :\n%s", id, rsp.sprint()), UVM_DEBUG)
      drive_transfer(rsp);
      //`uvm_info(get_type_name(),$psprintf("wav_APB %0d done driving transfer :\n%s", id, rsp.sprint()), UVM_DEBUG)
      seq_item_port.item_done();
      seq_item_port.put_response(rsp);
    end
  endtask

  // Drives a transfer.
  virtual protected task drive_transfer (wav_APB_transfer trans);
    // TODO Implement wav_D2D_APB_driver.drive_transfer()
    // For example:

    //`uvm_info(get_type_name(),$psprintf("Inside drive_transfer...1st line; addr : %0h", trans.addr), UVM_DEBUG)

    @(vif.mp_drv.cb_drv);

    //Drive the address phase of the transfer
    //slave_indx = cfg.get_slave_psel_by_addr(trans.addr);
    vif.mp_drv.cb_drv.paddr   <= trans.addr;
    vif.mp_drv.cb_drv.psel    <= 1;
    vif.mp_drv.cb_drv.penable <= 0;

    //`uvm_info(get_type_name(),$psprintf("Inside drive_transfer...2nd line"), UVM_DEBUG)

    if(trans.direction == APB_READ)
      vif.mp_drv.cb_drv.pwrite <= 0;
    else begin
      vif.mp_drv.cb_drv.pwrite <= 1'b1;
      vif.mp_drv.cb_drv.pwdata <= trans.data;
    end

    //`uvm_info(get_type_name(),$psprintf("Inside drive_transfer...3rd line"), UVM_DEBUG)

    //Data phase - Grab data if executing an APB_READ
    @(vif.mp_drv.cb_drv);
    vif.mp_drv.cb_drv.penable <= 1;

    //`uvm_info(get_type_name(),$psprintf("Inside drive_transfer...4th line pwrite=%d",vif.mp_drv.cb_drv.pwrite), UVM_DEBUG)

    fork: pready_timeout
       begin : PREADY_PROCESS
         do
         begin
          @(vif.mp_drv.cb_drv);
          //`uvm_info(get_type_name(),$psprintf("NOT-Received pready : %0d", vif.mp_drv.cb_drv.pready), UVM_DEBUG)
         end
         while(vif.mp_drv.cb_drv.pready === 0);

         //`uvm_info(get_type_name(),$psprintf("Received pready: %0d", vif.mp_drv.cb_drv.pready), UVM_DEBUG)
          disable TIMEOUT_PROCESS;

       end

       begin: TIMEOUT_PROCESS
         #4us; // fork off timeout time
         //`uvm_error(get_type_name(), "PREADY not recieved from DUT");
       end

    join_any

    disable pready_timeout;

    //`uvm_info(get_type_name(),$psprintf("Inside drive_transfer...5th line: %0d", vif.mp_drv.cb_drv.pready), UVM_DEBUG)

    if(trans.direction == APB_READ)
      trans.data = vif.mp_drv.cb_drv.prdata;

    vif.mp_drv.cb_drv.pwdata  <= 'd0;
    vif.mp_drv.cb_drv.penable <= 0;
    vif.mp_drv.cb_drv.psel    <= 0;
    vif.mp_drv.cb_drv.pwrite  <= 0;

    if(cfg.wait_for_pready_low) begin
      //`uvm_info(get_type_name(),$psprintf("waiting for prady low"), UVM_NONE)
      @ (negedge vif.pready);
    end

  endtask

  task drive_as_slave();
    //`uvm_info(get_type_name(),$psprintf("drive_as_slave started **************&&&&&&&&&&&&&&&&&"), UVM_DEBUG)
    fork // fork...join_any is used as slave component need not hold the phase
      vif.mp_slv_drv.cb_slv_drv.prdata <= 'd0;
      vif.mp_slv_drv.cb_slv_drv.pready  <= 1'b1;
      vif.mp_slv_drv.cb_slv_drv.pslverr <= 1'b0;
      forever begin
        @ (posedge vif.mp_slv_drv.cb_slv_drv.psel);
        @(vif.mp_slv_drv.cb_slv_drv);
        vif.mp_slv_drv.cb_slv_drv.pready  <= 1'b0;
        prdy_dly = (cfg.prdy_rand_dly_en) ? $urandom_range(0, cfg.prdy_max_dly) : cfg.prdy_dly_fixed;
        //`uvm_info(get_type_name(),$psprintf("drive_as_slave; driving pwdata ****pwrite : %0d; prdy_dly : %0d prdy_rand_dly_en=%0d: prdy_max_dly=%0d",vif.pwrite, prdy_dly,cfg.prdy_rand_dly_en,cfg.prdy_max_dly), UVM_DEBUG)
        repeat(prdy_dly) @(vif.mp_slv_drv.cb_slv_drv); // @ (posedge vif.pclk);
        vif.mp_slv_drv.cb_slv_drv.pready  <= 1'b1;
        if(vif.mp_slv_drv.cb_slv_drv.pwrite) begin // write
          //`uvm_info(get_type_name(),$psprintf("drive_as_slave; driving pwdata **************&&&&&&&&&&&&&&&&&1111111111111111"), UVM_DEBUG)
          // put_data(vif.paddr, vif.pwdata);                               // TODO
        end else begin // read
         // `uvm_info(get_type_name(),$psprintf("drive_as_slave; driving prdata **************&&&&&&&&&&&&&&&&&1111111111111111"), UVM_DEBUG)
          vif.mp_slv_drv.cb_slv_drv.pready  <= 1'b1;                                              // TODO this should be low for some transations.
          // vif.prdata <= get_data(vif.paddr);                             // TODO
          vif.mp_slv_drv.cb_slv_drv.prdata <= $random();
          //`uvm_info(get_type_name(),$psprintf(" driving before  pslverr=%0b",vif.mp_slv_drv.cb_slv_drv.pslverr), UVM_DEBUG)
          vif.mp_slv_drv.cb_slv_drv.pslverr <= cfg.get_slv_err(vif.mp_slv_drv.cb_slv_drv.paddr);
          //`uvm_info(get_type_name(),$psprintf(" driving after pslverr=%0b",vif.mp_slv_drv.cb_slv_drv.pslverr), UVM_DEBUG)
        end
        @(vif.mp_slv_drv.cb_slv_drv);
      end
    join_any
  endtask : drive_as_slave

 endclass
