// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/examples/xbus_example_master_seq_lib.sv#1 $
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

//------------------------------------------------------------------------------
//
// SEQUENCE: incr_read_byte_seq
//
//------------------------------------------------------------------------------

class incr_read_byte_seq extends xbus_base_sequence;

  function new(string name="incr_read_byte_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(incr_read_byte_seq, xbus_master_sequencer)

  read_byte_seq read_byte_seq0;

  rand int unsigned count;
    constraint count_ct { (count < 20); }
  rand bit [15:0] start_address;
  rand int unsigned incr_transmit_del = 0;
    constraint transmit_del_ct { (incr_transmit_del <= 10); }
 
  virtual task body();
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting with count = %0d", 
      get_sequence_path(), count), OVM_MEDIUM);
    repeat(count) begin : repeat_block
      `ovm_do_with(read_byte_seq0,
        { read_byte_seq0.start_addr == start_address;
          read_byte_seq0.transmit_del == incr_transmit_del; } )
      start_address++;
    end : repeat_block
  endtask : body
 
endclass : incr_read_byte_seq


//------------------------------------------------------------------------------
//
// SEQUENCE: incr_write_byte_seq
//
//------------------------------------------------------------------------------

class incr_write_byte_seq extends xbus_base_sequence;

  function new(string name="incr_write_byte_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(incr_write_byte_seq, xbus_master_sequencer)
    
  write_byte_seq write_byte_seq0;

  rand int unsigned count;
    constraint count_ct { (count < 20); }
  rand bit [15:0] start_address;
  rand int unsigned incr_transmit_del = 0;
    constraint transmit_del_ct { (incr_transmit_del <= 10); }

  virtual task body();
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting with count = %0d",
      get_sequence_path(), count), OVM_MEDIUM);
    repeat(count) begin : repeat_block
      `ovm_do_with(write_byte_seq0,
        { write_byte_seq0.start_addr == start_address;
          write_byte_seq0.transmit_del == incr_transmit_del; } )
      start_address++;
    end : repeat_block
  endtask : body

endclass : incr_write_byte_seq


//------------------------------------------------------------------------------
//
// SEQUENCE: incr_read_write_read_seq
//
//------------------------------------------------------------------------------

class incr_read_write_read_seq extends xbus_base_sequence;

  function new(string name="incr_read_write_read_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(incr_read_write_read_seq, xbus_master_sequencer)

  incr_read_byte_seq  read0;
  incr_write_byte_seq write0;

  virtual task body();
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting sequence",
      get_sequence_path()), OVM_MEDIUM);
    `ovm_do(read0)
    `ovm_do(write0)
    `ovm_do(read0)
  endtask : body

endclass : incr_read_write_read_seq


//------------------------------------------------------------------------------
//
// SEQUENCE: r8_w8_r4_w4_seq
//
//------------------------------------------------------------------------------

class r8_w8_r4_w4_seq extends xbus_base_sequence;

  function new(string name="r8_w8_r4_w4_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(r8_w8_r4_w4_seq, xbus_master_sequencer)    

  read_word_seq read_word_seq0;
  read_double_word_seq read_double_word_seq0;
  write_word_seq write_word_seq0;
  write_double_word_seq write_double_word_seq0;

  rand bit [15:0] start_address;

  constraint start_address_ct { (start_address == 16'h4000); }

  virtual task body();
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting...",
      get_sequence_path()), OVM_MEDIUM);
    `ovm_do_with(read_double_word_seq0, 
      { read_double_word_seq0.start_addr == start_address;
        read_double_word_seq0.transmit_del == 2; } )
    `ovm_do_with(write_double_word_seq0,
      { write_double_word_seq0.start_addr == start_address;
        write_double_word_seq0.transmit_del == 4; } )
    start_address = start_address + 8;
    `ovm_do_with(read_word_seq0,
      { read_word_seq0.start_addr == start_address;
        read_word_seq0.transmit_del == 6; } )
    `ovm_do_with(write_word_seq0,
      { write_word_seq0.start_addr == start_address;
        write_word_seq0.transmit_del == 8; } )
  endtask : body

endclass : r8_w8_r4_w4_seq
  

//------------------------------------------------------------------------------
//
// SEQUENCE: read_modify_write_seq
//
//------------------------------------------------------------------------------

class read_modify_write_seq extends xbus_base_sequence;

  function new(string name="read_modify_write_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(read_modify_write_seq, xbus_master_sequencer)    

  read_byte_seq read_byte_seq0;
  write_byte_seq write_byte_seq0;

  rand bit [15:0] addr_check;
  bit [7:0] m_data0_check;

  virtual task body();
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting...",
      get_sequence_path()), OVM_MEDIUM);
    // READ A RANDOM LOCATION
    `ovm_do_with(read_byte_seq0, {read_byte_seq0.start_addr == 'h12;
       read_byte_seq0.transmit_del == 0; })
    addr_check = read_byte_seq0.rsp.addr;
    m_data0_check = read_byte_seq0.rsp.data[0] + 1;
    // WRITE MODIFIED READ DATA
    `ovm_do_with(write_byte_seq0,
      { write_byte_seq0.start_addr == addr_check;
        write_byte_seq0.data0 == m_data0_check; } )
    // READ MODIFIED WRITE DATA
    `ovm_do_with(read_byte_seq0,
      { read_byte_seq0.start_addr == addr_check; } )
    assert(m_data0_check == read_byte_seq0.rsp.data[0]) else
      p_sequencer.ovm_report_error(get_type_name(),
        $psprintf("%s Read Modify Write Read error!", 
        get_sequence_path()));
  endtask : body

endclass : read_modify_write_seq


//------------------------------------------------------------------------------
//
// SEQUENCE: loop_read_modify_write_seq
//
//------------------------------------------------------------------------------

class loop_read_modify_write_seq extends xbus_base_sequence;

  int itr;

  function new(string name="loop_read_modify_write_seq");
    super.new(name);
  endfunction : new

  `ovm_sequence_utils(loop_read_modify_write_seq, xbus_master_sequencer)    

  read_modify_write_seq rmw_seq;

  virtual task body();
    void'(p_sequencer.get_config_int("loop_read_modify_write_seq.itr", itr));
    p_sequencer.ovm_report_info(get_type_name(),
      $psprintf("%s starting...",
      get_sequence_path()), OVM_MEDIUM);
    for(int i = 0; i < itr; i++) begin
      `ovm_do(rmw_seq)
    end
  endtask : body

endclass : loop_read_modify_write_seq

