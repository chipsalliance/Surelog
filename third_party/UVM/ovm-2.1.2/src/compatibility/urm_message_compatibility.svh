// $Id: //dvt/vtech/dev/main/ovm/src/compatibility/urm_message_compatibility.svh#8 $
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

  // User-Fields
  // -----------

  int unsigned recording_detail = OVM_NONE;

// create_unit
// -----------

  // For name change from unit to component
  function ovm_component create_unit (string type_name,
                                      string inst_name);
    return create_component(type_name, inst_name);
  endfunction


// do_print (override)
// --------

function void do_print(ovm_printer printer);
  string v;
  super.do_print(printer);

  // recording_detail is from compatibility/urm_message_compatibility.svh
  // It is printed only if its value is other than the default (OVM_NONE)
  if(ovm_verbosity'(recording_detail) != OVM_NONE)
    case (recording_detail)
      OVM_LOW : printer.print_generic("recording_detail", "ovm_verbosity", 
        $bits(recording_detail), "OVM_LOW");
      OVM_MEDIUM : printer.print_generic("recording_detail", "ovm_verbosity", 
        $bits(recording_detail), "OVM_MEDIUM");
      OVM_HIGH : printer.print_generic("recording_detail", "ovm_verbosity", 
        $bits(recording_detail), "OVM_HIGH");
      OVM_FULL : printer.print_generic("recording_detail", "ovm_verbosity", 
        $bits(recording_detail), "OVM_FULL");
      default : printer.print_field("recording_detail", recording_detail, 
        $bits(recording_detail), OVM_DEC, , "integral");
    endcase

  if (enable_stop_interrupt != 0) begin
    printer.print_field("enable_stop_interrupt", enable_stop_interrupt,
                        $bits(enable_stop_interrupt), OVM_BIN, ".", "bit");
  end

endfunction


// set_int_local (override)
// -------------

function void set_int_local (string field_name,
                             ovm_bitstream_t value,
                             bit recurse=1);

  //call the super function to get child recursion and any registered fields
  super.set_int_local(field_name, value, recurse);

  //set the local properties
  if(ovm_is_match(field_name, "recording_detail"))
    recording_detail = value;

endfunction


