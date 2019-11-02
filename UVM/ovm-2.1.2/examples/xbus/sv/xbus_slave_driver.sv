// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus_slave_driver.sv#1 $
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

`ifndef XBUS_SLAVE_DRIVER_SV
`define XBUS_SLAVE_DRIVER_SV

//------------------------------------------------------------------------------
//
// CLASS: xbus_slave_driver
//
//------------------------------------------------------------------------------

class xbus_slave_driver extends ovm_driver #(xbus_transfer);

  // The virtual interface used to drive and view HDL signals.
  protected virtual xbus_if xsi;

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils(xbus_slave_driver)

  // new - constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  // assign the virtual interface
  function void assign_vi(virtual interface xbus_if xsi);
    this.xsi = xsi;
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
    @(negedge xsi.sig_reset);
    forever begin
      @(posedge xsi.sig_clock);
      seq_item_port.get_next_item(req);
      respond_to_transfer(req);
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // reset_signals
  virtual protected task reset_signals();
    forever begin
      @(posedge xsi.sig_reset);
      xsi.sig_error      <= 1'bz;
      xsi.sig_wait       <= 1'bz;
      xsi.rw             <= 1'b0;
    end
  endtask : reset_signals

  // respond_to_transfer
  virtual protected task respond_to_transfer(xbus_transfer resp);
    if (resp.read_write != NOP)
    begin
      xsi.sig_error <= 1'b0;
      for (int i = 0; i < resp.size; i++)
      begin
        case (resp.read_write)
          READ : begin
            xsi.rw <= 1'b1;
            xsi.sig_data_out <= resp.data[i];
          end
          WRITE : begin
          end
        endcase
        if (resp.wait_state[i] > 0) begin
          xsi.sig_wait <= 1'b1;
          repeat (resp.wait_state[i])
            @(posedge xsi.sig_clock);
        end
        xsi.sig_wait <= 1'b0;
        @(posedge xsi.sig_clock);
        resp.data[i] = xsi.sig_data;
      end
      xsi.rw <= 1'b0;
      xsi.sig_wait  <= 1'bz;
      xsi.sig_error <= 1'bz;
    end
  endtask : respond_to_transfer

endclass : xbus_slave_driver

`endif // XBUS_SLAVE_DRIVER_SV

