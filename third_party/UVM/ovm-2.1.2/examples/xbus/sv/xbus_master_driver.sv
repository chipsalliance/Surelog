// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus_master_driver.sv#1 $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`ifndef XBUS_MASTER_DRIVER_SV
`define XBUS_MASTER_DRIVER_SV

//------------------------------------------------------------------------------
//
// CLASS: xbus_master_driver
//
//------------------------------------------------------------------------------

class xbus_master_driver extends ovm_driver #(xbus_transfer);

  // The virtual interface used to drive and view HDL signals.
  protected virtual xbus_if xmi;

  // Master Id
  protected int master_id;

  // Provide implmentations of virtual methods such as get_type_name and create
  `ovm_component_utils_begin(xbus_master_driver)
    `ovm_field_int(master_id, OVM_ALL_ON)
  `ovm_component_utils_end

  // new - constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  // assign_vi
  function void assign_vi(virtual interface xbus_if xmi);
    this.xmi = xmi;
  endfunction : assign_vi

  // run phase
  virtual task run();
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run

  // get_and_drive 
  virtual protected task get_and_drive();
    @(negedge xmi.sig_reset);
    forever begin
      @(posedge xmi.sig_clock);
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      drive_transfer(rsp);
      seq_item_port.item_done(rsp);
    end
  endtask : get_and_drive

  // reset_signals
  virtual protected task reset_signals();
    forever begin
      @(posedge xmi.sig_reset);
      xmi.sig_request[master_id]  <= 0;
      xmi.rw                      <= 'h0;
      xmi.sig_addr           <= 'hz;
      xmi.sig_data_out       <= 'hz;
      xmi.sig_size           <= 'bz;
      xmi.sig_read           <= 'bz;
      xmi.sig_write          <= 'bz;
      xmi.sig_bip            <= 'bz;
    end
  endtask : reset_signals

  // drive_transfer
  virtual protected task drive_transfer (xbus_transfer trans);
    if (trans.transmit_delay > 0) begin
      repeat(trans.transmit_delay) @(posedge xmi.sig_clock);
    end
    arbitrate_for_bus();
    drive_address_phase(trans);
    drive_data_phase(trans);
  endtask : drive_transfer

  // arbitrate_for_bus
  virtual protected task arbitrate_for_bus();
    xmi.sig_request[master_id] <= 1;
    @(posedge xmi.sig_clock iff xmi.sig_grant[master_id] === 1);
    xmi.sig_request[master_id] <= 0;
  endtask : arbitrate_for_bus

  // drive_address_phase
  virtual protected task drive_address_phase (xbus_transfer trans);
    xmi.sig_addr <= trans.addr;
    drive_size(trans.size);
    drive_read_write(trans.read_write);
    @(posedge xmi.sig_clock);
    xmi.sig_addr <= 32'bz;
    xmi.sig_size <= 2'bz;
    xmi.sig_read <= 1'bz;
    xmi.sig_write <= 1'bz;  
  endtask : drive_address_phase

  // drive_data_phase
  virtual protected task drive_data_phase (xbus_transfer trans);
    bit err;
    for(int i = 0; i <= trans.size - 1; i ++) begin
      if (i == (trans.size - 1))
        xmi.sig_bip <= 0;
      else
        xmi.sig_bip <= 1;
      case (trans.read_write)
        READ    : read_byte(trans.data[i], err);
        WRITE   : write_byte(trans.data[i], err);
      endcase
    end //for loop
    xmi.sig_data_out <= 8'bz;
    xmi.sig_bip <= 1'bz;
  endtask : drive_data_phase

  // read_byte
  virtual protected task read_byte (output bit [7:0] data, output bit error);
    xmi.rw <= 1'b0;
    @(posedge xmi.sig_clock iff xmi.sig_wait === 0);
    data = xmi.sig_data;
  endtask : read_byte

  // write_byte
  virtual protected task write_byte (bit[7:0] data, output bit error);
    xmi.rw <= 1'b1;
    xmi.sig_data_out <= data;
    @(posedge xmi.sig_clock iff xmi.sig_wait === 0);
    xmi.rw <= 'h0;
  endtask : write_byte

  // drive_size
  virtual protected task drive_size (int size);
    case (size)
      1: xmi.sig_size <=  2'b00;
      2: xmi.sig_size <=  2'b01;
      4: xmi.sig_size <=  2'b10;
      8: xmi.sig_size <=  2'b11;
    endcase
  endtask : drive_size

  // drive_read_write            
  virtual protected task drive_read_write(xbus_read_write_enum rw);
    case (rw)
      NOP   : begin xmi.sig_read <= 0; xmi.sig_write <= 0; end
      READ  : begin xmi.sig_read <= 1; xmi.sig_write <= 0; end
      WRITE : begin xmi.sig_read <= 0; xmi.sig_write <= 1; end
    endcase
  endtask : drive_read_write

endclass : xbus_master_driver

`endif // XBUS_MASTER_DRIVER_SV

