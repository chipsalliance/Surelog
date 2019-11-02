// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus_transfer.sv#1 $
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

`ifndef XBUS_TRANSFER_SV
`define XBUS_TRANSFER_SV

//------------------------------------------------------------------------------
//
// xbus transfer enums, parameters, and events
//
//------------------------------------------------------------------------------

typedef enum { NOP,
               READ,
               WRITE
             } xbus_read_write_enum;

//------------------------------------------------------------------------------
//
// CLASS: xbus_transfer
//
//------------------------------------------------------------------------------

class xbus_transfer extends ovm_sequence_item;                                  

  rand bit [15:0]           addr;
  rand xbus_read_write_enum read_write;
  rand int unsigned         size;
  rand bit [7:0]            data[];
  rand bit [3:0]            wait_state[];
  rand int unsigned         error_pos;
  rand int unsigned         transmit_delay = 0;
  string                    master = "";
  string                    slave = "";

  constraint c_read_write {
    read_write inside { READ, WRITE };
  }
  constraint c_size {
    size inside {1,2,4,8};
  }
  constraint c_data_wait_size {
    data.size() == size;
    wait_state.size() == size;
  }
  constraint c_transmit_delay { 
    transmit_delay <= 10 ; 
  }

  `ovm_object_utils_begin(xbus_transfer)
    `ovm_field_int      (addr,           OVM_ALL_ON)
    `ovm_field_enum     (xbus_read_write_enum, read_write, OVM_ALL_ON)
    `ovm_field_int      (size,           OVM_ALL_ON)
    `ovm_field_array_int(data,           OVM_ALL_ON)
    `ovm_field_array_int(wait_state,     OVM_ALL_ON)
    `ovm_field_int      (error_pos,      OVM_ALL_ON)
    `ovm_field_int      (transmit_delay, OVM_ALL_ON)
    `ovm_field_string   (master,         OVM_ALL_ON|OVM_NOCOMPARE)
    `ovm_field_string   (slave,          OVM_ALL_ON|OVM_NOCOMPARE)
  `ovm_object_utils_end

  // new - constructor
  function new (string name = "xbus_transfer_inst");
    super.new(name);
  endfunction : new

endclass : xbus_transfer

`endif // XBUS_TRANSFER_SV

