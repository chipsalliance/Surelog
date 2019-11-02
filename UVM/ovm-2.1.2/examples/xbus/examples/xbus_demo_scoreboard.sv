// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/examples/xbus_demo_scoreboard.sv#1 $
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

`ifndef XBUS_DEMO_SCOREBOARD_SVH
`define XBUS_DEMO_SCOREBOARD_SVH

//------------------------------------------------------------------------------
//
// CLASS: xbus_demo_scoreboard
//
//------------------------------------------------------------------------------

class xbus_demo_scoreboard extends ovm_scoreboard;

  ovm_analysis_imp#(xbus_transfer, xbus_demo_scoreboard) item_collected_export;

  protected bit disable_scoreboard = 0;
  protected int num_writes = 0;
  protected int num_init_reads = 0;
  protected int num_uninit_reads = 0;

  protected int unsigned m_mem_expected[int unsigned];

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils_begin(xbus_demo_scoreboard)
    `ovm_field_int(disable_scoreboard, OVM_ALL_ON)
    `ovm_field_int(num_writes, OVM_ALL_ON|OVM_DEC)
    `ovm_field_int(num_init_reads, OVM_ALL_ON|OVM_DEC)
    `ovm_field_int(num_uninit_reads, OVM_ALL_ON|OVM_DEC)
  `ovm_component_utils_end

  // new - constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  //build
  function void build();
    item_collected_export = new("item_collected_export", this);
  endfunction

  // write
  virtual function void write(xbus_transfer trans);
    if(!disable_scoreboard)
      memory_verify(trans);
  endfunction : write

  // memory_verify
  protected function void memory_verify(input xbus_transfer trans);
    int unsigned data, exp;
    for (int i = 0; i < trans.size; i++) begin
      // Check to see if entry in associative array for this address when read
      // If so, check that transfer data matches associative array data.
      if (m_mem_expected.exists(trans.addr + i)) begin
        if (trans.read_write == READ) begin
          data = trans.data[i];
          `ovm_info(get_type_name(),
            $psprintf("%s to existing address...Checking address : %0h with data : %0h", 
            trans.read_write.name(), trans.addr, data), OVM_LOW)
          assert(m_mem_expected[trans.addr + i] == trans.data[i]) else begin
            exp = m_mem_expected[trans.addr + i];
            `ovm_error(get_type_name(),
              $psprintf("Read data mismatch.  Expected : %0h.  Actual : %0h", 
              exp, data))
          end
          num_init_reads++;
        end
        if (trans.read_write == WRITE) begin
          data = trans.data[i];
          `ovm_info(get_type_name(),
            $psprintf("%s to existing address...Updating address : %0h with data : %0h", 
            trans.read_write.name(), trans.addr + i, data), OVM_LOW)
          m_mem_expected[trans.addr + i] = trans.data[i];
          num_writes++;
        end
      end
      // Check to see if entry in associative array for this address
      // If not, update the location regardless if read or write.
      else begin
        data = trans.data[i];
        `ovm_info(get_type_name(),
          $psprintf("%s to empty address...Updating address : %0h with data : %0h", 
          trans.read_write.name(), trans.addr + i, data), OVM_LOW)
        m_mem_expected[trans.addr + i] = trans.data[i];
        if(trans.read_write == READ)
          num_uninit_reads++;
        else if (trans.read_write == WRITE)
          num_writes++;
      end
    end
  endfunction : memory_verify

  // report
  virtual function void report();
    if(!disable_scoreboard) begin
      `ovm_info(get_type_name(),
        $psprintf("Reporting scoreboard information...\n%s", this.sprint()), OVM_LOW)
    end
  endfunction : report

endclass : xbus_demo_scoreboard

`endif // XBUS_DEMO_SCOREBOARD_SVH

