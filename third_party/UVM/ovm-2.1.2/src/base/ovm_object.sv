// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_object.sv#41 $
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

`include "base/ovm_object.svh"
typedef class ovm_component;


//----------------------------------------------------------------------------
//
// CLASS- ovm_object
//
//----------------------------------------------------------------------------


// new
// ---

function ovm_object::new (string name="");

  m_inst_id = m_inst_count++;
  m_leaf_name = name;
  m_field_automation (null, OVM_CHECK_FIELDS, "");
endfunction


// reseed
// ------

function void ovm_object::reseed ();
  if(use_ovm_seeding)
    this.srandom(ovm_create_random_seed(get_type_name(), get_full_name()));
endfunction


// get type
// --------

function ovm_object_wrapper ovm_object::get_type();
  ovm_report_error("NOTYPID", "get_type not implemented in derived class.", OVM_NONE);
  return null;
endfunction


// get inst_id
// -----------

function int ovm_object::get_inst_id();
  return m_inst_id;
endfunction


// get_object_type
// ---------------

function ovm_object_wrapper ovm_object::get_object_type();
  if(get_type_name() == "<unknown>") return null;
  return factory.find_by_name(get_type_name());
endfunction


// get inst_count
// --------------

function int ovm_object::get_inst_count();
  return m_inst_count;
endfunction


// get_name
// --------

function string ovm_object::get_name ();
  return m_leaf_name;
endfunction


// get_full_name
// -------------

function string ovm_object::get_full_name ();
  return get_name();
endfunction


// set_name
// --------

function void ovm_object::set_name (string name);
  m_leaf_name = name;
endfunction


// print 
// -----
 
function void ovm_object::print(ovm_printer printer=null);

  if(printer==null)
    printer = ovm_default_printer;

  if(printer.istop()) begin
    printer.print_object(get_name(), this);
  end
  else begin
    //do m_field_automation here so user doesn't need to call anything to get
    //automation.
    ovm_auto_options_object.printer = printer;
    m_field_automation(null, OVM_PRINT, "");
    //call user override
    do_print(printer);
  end
endfunction


// sprint
// ------

function string ovm_object::sprint(ovm_printer printer=null);
  bit p;

  if(printer==null)
    printer = ovm_default_printer;

  p = printer.knobs.sprint;
  printer.knobs.sprint = 1;

  print(printer);

  printer.knobs.sprint = p;  //revert back to regular printing
  return printer.m_string;
endfunction


// do_sprint (deprecated)
// ---------

function string ovm_object::do_sprint(ovm_printer printer);
  ovm_top.ovm_report_warning("deprecated",
      {"ovm_object::do_sprint() is deprecated and replaced by ",
      "ovm_object::convert2string()"}, OVM_NONE);
  return convert2string();
endfunction


// convert2string (virtual)
// --------------

function string ovm_object::convert2string();
  return "";
endfunction


// print_field_match (static)
// -----------------

function void ovm_object::print_field_match(string fnc, string match);
  string scratch;

  if(m_sc.save_last_field)
    m_sc.last_field = m_sc.get_full_scope_arg();

  if(print_matches) begin
    int style;
    scratch = {
      fnc, ": Matched string ", match, " to field ", m_sc.get_full_scope_arg()
    };
    ovm_report_info("STRMTC", scratch, OVM_LOW);
  end
endfunction

// set
// ---

function void  ovm_object::set_int_local (string      field_name,
                                          ovm_bitstream_t value,
                                          bit         recurse=1);
  if(m_sc.scope.in_hierarchy(this)) return;

  this.m_sc.status = 0;
  this.m_sc.bitstream = value;

  m_field_automation(null, OVM_SETINT, field_name);

  if(m_sc.warning && !this.m_sc.status) begin
    ovm_report_error("NOMTC", $psprintf("did not find a match for field %s", field_name),OVM_NONE);
  end

endfunction


// set_object_local
// ----------------

function void  ovm_object::set_object_local (string     field_name,
                                             ovm_object value,
                                             bit        clone=1,
                                             bit        recurse=1);
  ovm_object cc;
  if(m_sc.scope.in_hierarchy(this)) return;

  if(clone && (value!=null)) begin 
    cc = value.clone();
    if(cc != null) cc.set_name(field_name); 
    value = cc; 
  end 

  this.m_sc.status = 0;
  this.m_sc.object = value;
  ovm_auto_options_object.clone = clone;

  m_field_automation(null, OVM_SETOBJ, field_name);

  if(m_sc.warning && !this.m_sc.status) begin
    ovm_report_error("NOMTC", $psprintf("did not find a match for field %s", field_name), OVM_NONE);
  end

endfunction


// set_string_local
// ----------------
function void  ovm_object::set_string_local (string field_name,
                                             string value,
                                             bit    recurse=1);
  if(m_sc.scope.in_hierarchy(this)) return;
  this.m_sc.status = 0;
  this.m_sc.stringv = value;

  m_field_automation(null, OVM_SETSTR, field_name);

  if(m_sc.warning && !this.m_sc.status) begin
`ifdef INCA
    ovm_report_error("NOMTC", $psprintf("did not find a match for field %s (@%0d)", field_name, this), OVM_NONE);
`else
    ovm_report_error("NOMTC", $psprintf("did not find a match for field %s", field_name), OVM_NONE);
`endif
  end
endfunction


// m_do_set (static)
// ------------

// function m_do_set (match, arg, lhs, what, flag)
//   Precondition:
//     match     -- a match string to test against arg to do the set
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do on (left hand side)
//     what      -- integer, what to do
//     flag      -- object flags
//
//     ovm_object::m_sc.bitstream -- rhs object used for set/get
//     ovm_object::m_sc.status        -- return status for set/get calls
//


function int ovm_object::m_do_set (string match,
                                       string arg,
                                       inout ovm_bitstream_t lhs, 
                                       input int what,
                                       int flag);

  bit matched;

  if (what < OVM_START_FUNCS || what > OVM_END_FUNCS)
     return 0;

  matched = ovm_is_match(match, m_sc.scope.get_arg());

  case (what)
    OVM_SETINT:
      begin
        if(matched) begin
          if(flag &OVM_READONLY) begin
            ovm_report_warning("RDONLY", $psprintf("Readonly argument match %s is ignored", 
               m_sc.get_full_scope_arg()), OVM_NONE);
            return 0;
          end
          print_field_match("set_int()", match);
          lhs = ovm_object::m_sc.bitstream;
          ovm_object::m_sc.status = 1;
          return 1;
        end
      end
    default:
      begin
        if(matched) begin
          ovm_report_warning("MTCTYP", $psprintf("matched integral field %s, %s", 
          m_sc.get_full_scope_arg(),
          "but expected a non-integral type"), OVM_NONE);
        end
      end
  endcase
  return 0;
endfunction


// m_do_set_string (static)
// -------------------

// function m_do_set_string (match, arg, lhs, what, flag)
//   Precondition:
//     match     -- a match string to test against arg to do the set
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do get or set on (left hand side)
//     what      -- integer, what to do
//     flag      -- object flags
//
//     ovm_object::m_sc.stringv    -- rhs object used for set/get
//     ovm_object::m_sc.status        -- return status for set/get calls
//

function int ovm_object::m_do_set_string(string match,
                                             string arg,
                                             inout string lhs, 
                                             input int what,
                                             int flag);

  bit matched;
  string s;

  if (what < OVM_START_FUNCS || what > OVM_END_FUNCS)
     return 0;

  matched = ovm_is_match(match, m_sc.scope.get_arg());

  case (what)
    OVM_SETSTR:
      begin
        if(matched) begin
          if(flag &OVM_READONLY) begin
            ovm_report_warning("RDONLY", $psprintf("Readonly argument match %s is ignored", 
               m_sc.get_full_scope_arg()), OVM_NONE);
            return 0;
          end
          print_field_match("set_string()", match);
          lhs = ovm_object::m_sc.stringv;
          ovm_object::m_sc.status = 1;
          return 1;
        end
      end
    default:
      begin
        if(matched) begin
          ovm_report_warning("MTCTYP", $psprintf("matched string field %s, %s", 
          m_sc.get_full_scope_arg(),
          "but expected a non-string type"), OVM_NONE);
        end
      end
  endcase
  return 0;
endfunction


// m_do_set_object (static)
// -----------------

// function m_do_set_object (match, arg, lhsobj, what, flag)
//   Precondition:
//     match     -- a match string to test against arg to do the set
//     arg       -- the name of the short name of the lhs object
//     lhsobj    -- the object to do set_object on (left hand side)
//     what      -- integer, what to do
//     flag      -- object flags
//
//     ovm_object::m_sc.object -- rhs object used for set
//     ovm_object::m_sc.status     -- return status for set/get calls. set
//       always returns 0.
//
//   Postcondition:
//     Performs the set or get operation on an object. If the object doesn't
//     match then the object is recursed. The get* operations return true if
//     an index was returned. The set* always return 0.

function int ovm_object::m_do_set_object (string match,
                                            string arg,
                                            inout ovm_object lhsobj, 
                                            input int what,
                                                  int flag);

  bit matched;
  bit prev;
  int cnt;

  if (what < OVM_START_FUNCS || what > OVM_END_FUNCS)
     return 0;

  matched = ovm_is_match(match, m_sc.scope.get_arg());

  case (what)
    OVM_SETOBJ:
      begin
        if(matched) begin
          if(flag &OVM_READONLY) begin
            ovm_report_warning("RDONLY", $psprintf("Readonly argument match %s is ignored", 
               m_sc.get_full_scope_arg()), OVM_NONE);
            return 0;
          end
          print_field_match("set_object()", match);
          lhsobj = ovm_object::m_sc.object;
          ovm_object::m_sc.status = 1;
        end
        else if(lhsobj==null) return 0;
        if(flag &OVM_READONLY) 
          return 0; 
        //Only traverse if there is a possible match.
        for(cnt=0; cnt<match.len(); ++cnt) begin
          if(match[cnt] == "." || match[cnt] == "*") break;
        end
        if(cnt!=match.len())
          lhsobj.m_field_automation(null, OVM_SETOBJ, match);
        return ovm_object::m_sc.status;
      end
  endcase

  if(matched) begin
    ovm_report_warning("MTCTYP", $psprintf("matched object field %s, %s", 
          m_sc.get_full_scope_arg(),
          "but expected a non-object type"), OVM_NONE);
  end
  if(lhsobj==null) return 0;
  lhsobj.m_field_automation(null, what, match);

  return ovm_object::m_sc.status;

endfunction

// clone
// -----

function ovm_object ovm_object::clone();
  ovm_object tmp;
  tmp = this.create(get_name());
  if(tmp == null) begin
//    ovm_report_warning("CRFLD", $psprintf("The create method failed for %s,  object will be copied using shallow copy", get_name()));
//    tmp = new this;
    ovm_report_warning("CRFLD", $psprintf("The create method failed for %s,  object cannot be cloned", get_name()), OVM_NONE);
  end
  else begin
    tmp.copy(this);
  end

  return(tmp);
endfunction


// copy
// ----

ovm_copy_map ovm_global_copy_map = new;
function void ovm_object::copy (ovm_object rhs);
  //For cycle checking
  static int depth;
  if((rhs !=null)  && (ovm_global_copy_map.get(rhs) != null)) begin
    return;
  end

  if(rhs==null) begin
    ovm_report_warning("NULLCP", "A null object was supplied to copy; copy is ignored", OVM_NONE);
    return;
  end

  ovm_global_copy_map.set(rhs, this); 
  ++depth;

  do_copy(rhs);
  m_field_automation(rhs, OVM_COPY, "");

  --depth;
  if(depth==0) begin
    ovm_global_copy_map.clear();
  end
endfunction


// do_copy
// -------

function void ovm_object::do_copy (ovm_object rhs);
  return;
endfunction


// init_status
// -----------

function ovm_status_container ovm_object::init_status();
  if(m_sc==null) m_sc=new;
  return m_sc;
endfunction


// compare
// -------

function bit  ovm_object::compare (ovm_object rhs,
                                   ovm_comparer comparer=null);
  bit t, dc;
  static int style;
  bit done;
  done = 0;
  if(comparer != null) 
    ovm_auto_options_object.comparer = comparer;
  else 
    ovm_auto_options_object.comparer = ovm_default_comparer;
  comparer = ovm_auto_options_object.comparer;

  if(!m_sc.scope.depth()) begin
    comparer.compare_map.clear();
    comparer.result = 0;
    comparer.miscompares = "";
    comparer.scope = m_sc.scope;
    if(get_name() == "") begin
      m_sc.scope.down("<object>", this);
    end
    else
      m_sc.scope.down(this.get_name(), this);
  end
  if(!done && (rhs == null)) begin
    if(m_sc.scope.depth()) begin
      comparer.print_msg_object(this, rhs);
    end
    else begin
      comparer.print_msg_object(this, rhs);
`ifdef INCA
      ovm_report_info("MISCMP",
           $psprintf("%0d Miscompare(s) for object %s@%0d vs. @%0d", 
           comparer.result, get_name(), this, rhs), ovm_auto_options_object.comparer.verbosity);
`else
      ovm_report_info("MISCMP",
           $psprintf("%0d Miscompare(s) for object %s", 
           comparer.result, get_name()), ovm_auto_options_object.comparer.verbosity);
`endif
      done = 1;
    end
  end

  if(!done && (comparer.compare_map.get(rhs) != null)) begin
    if(comparer.compare_map.get(rhs) != this) begin
      comparer.print_msg_object(this, comparer.compare_map.get(rhs));
    end 
    done = 1;  //don't do any more work after this case, but do cleanup
  end

  if(!done && comparer.check_type && get_type_name() != rhs.get_type_name()) begin
    m_sc.stringv = { "lhs type = \"", get_type_name(), 
                     "\" : rhs type = \"", rhs.get_type_name(), "\""};
    comparer.print_msg(m_sc.stringv);
  end

  if(!done) begin
    comparer.compare_map.set(rhs, this);
    m_field_automation(rhs, OVM_COMPARE, "");
    dc = do_compare(rhs, comparer);
  end

  if(m_sc.scope.depth() == 1)  begin
    m_sc.scope.up(this);
  end

  comparer.print_rollup(this, rhs);
  return (comparer.result == 0 && dc == 1);
endfunction


// do_compare
// ----------

function bit  ovm_object::do_compare (ovm_object rhs,
                                      ovm_comparer comparer);
  return 1;
endfunction


// m_field_automation
// --------------

function void ovm_object::m_field_automation ( ovm_object tmp_data__,
                                             int        what__,
                                             string     str__ );
  return;
endfunction


// check_fields
// ------------

function void ovm_object::m_do_field_check(string field);
  if(m_field_array.exists(field) && (m_field_array[field] == 1)) begin
    ovm_report_error("MLTFLD", $psprintf("Field %s is defined multiple times in type %s",
       field, get_type_name()), OVM_NONE);
  end
  m_field_array[field]++; 
endfunction

function void ovm_object::m_delete_field_array();
  m_field_array.delete();
endfunction

// do_print (virtual override)
// ------------

function void ovm_object::do_print(ovm_printer printer);
  return;
endfunction


// m_pack
// ------

function void ovm_object::m_pack (inout ovm_packer packer);

  if(packer!=null) 
    ovm_auto_options_object.packer = packer;
  else  
    ovm_auto_options_object.packer = ovm_default_packer;
  packer = ovm_auto_options_object.packer;

  packer.reset();
  packer.scope.down(get_name(), this);

  m_field_automation(null, OVM_PACK, "");
  do_pack(packer);

  packer.set_packed_size();

  packer.scope.up(this); 

endfunction
  

// pack
// ---- 
  
function int ovm_object::pack (ref bit bitstream [],
                               input ovm_packer packer =null );
  m_pack(packer);
  packer.get_bits(bitstream);
  return packer.get_packed_size();
endfunction

// pack_bytes
// ----------

function int ovm_object::pack_bytes (ref byte unsigned bytestream [],
                                     input ovm_packer packer=null );
  m_pack(packer);
  packer.get_bytes(bytestream);
  return packer.get_packed_size();
endfunction


// pack_ints
// ---------

function int ovm_object::pack_ints (ref int unsigned intstream [],
                                    input ovm_packer packer=null );
  m_pack(packer);
  packer.get_ints(intstream);
  return packer.get_packed_size();
endfunction


// do_pack
// -------

function void ovm_object::do_pack (ovm_packer packer );
  return;
endfunction


// m_unpack_pre
// ------------
  
function void ovm_object::m_unpack_pre (inout ovm_packer packer);
  if(packer!=null)
    ovm_auto_options_object.packer = packer;
  else
    ovm_auto_options_object.packer = ovm_default_packer;
  packer = ovm_auto_options_object.packer;
  packer.reset();
endfunction
  

// m_unpack_post
// -------------

function void ovm_object::m_unpack_post (ovm_packer packer);

  int provided_size; 

  provided_size = packer.get_packed_size();

  //Put this object into the hierarchy
  packer.scope.down(get_name(), this);

  m_field_automation(null, OVM_UNPACK, "");

  do_unpack(packer);

  //Scope back up before leaving
  packer.scope.up(this);

  if(packer.get_packed_size() != provided_size) begin
    ovm_report_warning("BDUNPK", $psprintf("Unpack operation unsuccessful: unpacked %0d bits from a total of %0d bits", packer.get_packed_size(), provided_size), OVM_NONE);
  end

endfunction


// unpack
// ------

function int ovm_object::unpack (ref    bit        bitstream [],
                                 input  ovm_packer packer=null);
  m_unpack_pre(packer);
  packer.put_bits(bitstream);
  m_unpack_post(packer);
  packer.set_packed_size();
  return packer.get_packed_size();
endfunction


// unpack_bytes
// ------------

function int ovm_object::unpack_bytes (ref    byte unsigned bytestream [],
                                       input  ovm_packer packer=null);
  m_unpack_pre(packer);
  packer.put_bytes(bytestream);
  m_unpack_post(packer);
  packer.set_packed_size();
  return packer.get_packed_size();
endfunction


// unpack_ints
// -----------
  
function int ovm_object::unpack_ints (ref    int unsigned intstream [],
                                      input  ovm_packer packer=null);
  m_unpack_pre(packer);
  packer.put_ints(intstream);
  m_unpack_post(packer);
  packer.set_packed_size();
  return packer.get_packed_size();
endfunction


// do_unpack
// ---------

function void ovm_object::do_unpack (ovm_packer packer);
  return;
endfunction


// record
// ------

function void ovm_object::record (ovm_recorder recorder=null);
//mxg  if(!recorder) 
  if(recorder == null) 
    recorder = ovm_default_recorder;

  if(!recorder.tr_handle) return;

  ovm_auto_options_object.recorder = recorder;
  recorder.recording_depth++;
  m_field_automation(null, OVM_RECORD, "");
  do_record(recorder);

  recorder.recording_depth--;

  if(recorder.recording_depth==0) begin
    recorder.tr_handle = 0;
  end
endfunction


// do_record (virtual)
// ---------

function void ovm_object::do_record (ovm_recorder recorder);
  return;
endfunction


// m_get_function_type (static)
// -------------------

function string ovm_object::m_get_function_type (int what);
  case (what)
    OVM_COPY:              return "copy";
    OVM_COMPARE:           return "compare";
    OVM_PRINT:             return "print";
    OVM_RECORD:            return "record";
    OVM_PACK:              return "pack";
    OVM_UNPACK:            return "unpack";
    OVM_FLAGS:             return "get_flags";
    OVM_SETINT:            return "set";
    OVM_SETOBJ:            return "set_object";
    OVM_SETSTR:            return "set_string";
    default:           return "unknown";
  endcase
endfunction


// m_get_report_object
// -------------------

function ovm_report_object ovm_object::m_get_report_object();
  return null;
endfunction


// m_record_field_object (static)
// ---------------------

function void ovm_object::m_record_field_object (string arg,
                                               ovm_object value,
                                               ovm_recorder recorder =null,
                                               int flag = OVM_DEFAULT);
  begin
    if(recorder == null)
      recorder=ovm_auto_options_object.recorder;

    if((flag&OVM_NORECORD) != 0) return;

    recorder.record_object(arg, value);

  end
endfunction


// m_do_data (static)
// ---------

// function m_do_data (arg, lhs, rhs, what, flag)
//   Precondition:
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do work on (left hand side)
//     lhs       -- the rhs to do work from (right hand side)
//     what      -- integer, what to do
//     flag      -- object flags

function int ovm_object::m_do_data (string arg,
                                  inout ovm_bitstream_t lhs,
                                  input ovm_bitstream_t rhs,
                                        int what,
                                        int bits,
                                        int flag);


  if (what > OVM_END_DATA_EXTRA)
     return 0;
  if(bits > OVM_STREAMBITS) begin
    ovm_report_error("FLDTNC",$psprintf("%s is %0d bits; maximum field size is %0d, truncating",
                 arg, bits, OVM_STREAMBITS), OVM_NONE);
  end
  case (what)
    OVM_COPY:
      begin
        if(((flag)&OVM_NOCOPY) == 0) begin
          ovm_bitstream_t mask;
          mask = -1;
          mask >>= (OVM_STREAMBITS-bits);
          lhs = rhs & mask;
        end
        return 0;
      end
    OVM_COMPARE:
      begin
        if(((flag)&OVM_NOCOMPARE) == 0) begin
          bit r;
          if(bits <= 64)
            r = ovm_auto_options_object.comparer.compare_field_int(arg, lhs, rhs, bits, ovm_radix_enum'(flag&OVM_RADIX));
          else
            r = ovm_auto_options_object.comparer.compare_field(arg, lhs, rhs, bits, ovm_radix_enum'(flag&OVM_RADIX));
        end
        return 0;
      end
    OVM_PACK:
      begin
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
            if(bits<=64)
              ovm_auto_options_object.packer.pack_field_int(lhs, bits);
            else
              ovm_auto_options_object.packer.pack_field(lhs, bits);
          end
        end
        return 0;
      end
    OVM_UNPACK:
      begin
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
            if(bits<=64)
              lhs=ovm_auto_options_object.packer.unpack_field_int(bits);
            else
              lhs=ovm_auto_options_object.packer.unpack_field(bits);
          end
        end
        return 0;
      end
    OVM_PRINT:
      begin
        if(((flag)&OVM_NOPRINT) == 0) 
        begin  
          ovm_printer printer; 
          ovm_radix_enum radix;
          radix = ovm_radix_enum'(flag&OVM_RADIX);
          printer = ovm_auto_options_object.printer; 
          printer.print_field(arg, lhs, bits, radix);
        end
      end
    OVM_RECORD:
      begin
        if(((flag)&OVM_NORECORD) == 0) 
        begin 
          integer h;
          ovm_radix_enum radix;

          radix = ovm_radix_enum'(flag&OVM_RADIX);
          ovm_auto_options_object.recorder.record_field(arg, lhs, bits, radix);
        end 
      end
  endcase
  return 0;
endfunction


// m_do_data_real (static)
// --------------

// function m_do_data_real (arg, lhs, rhs, what, flag)
//   Precondition:
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do work on (left hand side)
//     lhs       -- the rhs to do work from (right hand side)
//     what      -- integer, what to do
//     flag      -- object flags

function int ovm_object::m_do_data_real (string arg,
                                  inout real lhs,
                                  input real rhs,
                                        int what,
                                        int flag);


  if (what > OVM_END_DATA_EXTRA)
     return 0;
  case (what)
    OVM_COPY:
      begin
        if(((flag)&OVM_NOCOPY) == 0) begin
          lhs = rhs;
        end
        return 0;
      end
    OVM_COMPARE:
      begin
        if(((flag)&OVM_NOCOMPARE) == 0) begin
          bit r;
          r = ovm_auto_options_object.comparer.compare_field_real(arg, lhs, rhs);
        end
        return 0;
      end
    OVM_PACK:
      begin
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
            ovm_auto_options_object.packer.pack_field_int($realtobits(lhs), 64);
          end
        end
        return 0;
      end
    OVM_UNPACK:
      begin
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
            lhs=$bitstoreal(ovm_auto_options_object.packer.unpack_field_int(64));
          end
        end
        return 0;
      end
    OVM_PRINT:
      begin
        if(((flag)&OVM_NOPRINT) == 0) 
        begin  
          ovm_printer printer; 
          printer = ovm_auto_options_object.printer; 
          printer.print_field_real(arg, lhs);
        end
      end
    OVM_RECORD:
      begin
        if(((flag)&OVM_NORECORD) == 0) 
        begin 
          ovm_auto_options_object.recorder.record_field_real(arg, lhs);
        end 
      end
  endcase
  return 0;
endfunction


// m_do_data_object (static)
// ----------------

// function m_do_data_object (arg, lhs, rhs, what, flag)
//   Precondition:
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do work on (left hand side)
//     lhs       -- the rhs to do work from (right hand side)
//     what      -- integer, what to do
//     flag      -- object flags

function int ovm_object::m_do_data_object (string arg,
                                       inout ovm_object lhs,
                                       input ovm_object rhs,
                                             int what,
                                             int flag);

  ovm_object lhs_obj;

  if (what > OVM_END_DATA_EXTRA)
     return 0;

  case (what)
    OVM_COPY:
      begin
        int rval;
        if(((flag)&OVM_NOCOPY) != 0) begin
          return 0;
        end
        if(rhs == null) begin
          lhs = null;
          return OVM_REFERENCE;
        end

        if(flag & OVM_SHALLOW) begin
          rval = OVM_SHALLOW;
        end
        else if(flag & OVM_REFERENCE) begin
          lhs = rhs;
          rval = OVM_REFERENCE;
        end
        else  //deepcopy
        begin
          ovm_object v;
          v = ovm_global_copy_map.get(rhs);
          if(v != null) begin
            lhs = v;
            rval = OVM_REFERENCE;
          end
          else if(lhs==null) begin
            lhs = rhs.clone();
            lhs.set_name(arg);
            rval = OVM_REFERENCE;
          end
          else if(rhs == null) begin
            rval = OVM_REFERENCE;
          end
          else begin
            //lhs doesn't change for this case, so don't need to copy back
            lhs.copy(rhs);
             rval = 0;
          end
        end
        return rval;
      end
    OVM_COMPARE:
      begin
        bit refcmp;

        if(((flag)&OVM_NOCOMPARE) != 0) begin
          return 0;
        end

        //if the object are the same then don't need to do a deep compare
        if(rhs == lhs) return 0;

        refcmp = (flag & OVM_SHALLOW) && !(ovm_auto_options_object.comparer.policy == OVM_DEEP);

        //do a deep compare here 
        if(!refcmp && !(ovm_auto_options_object.comparer.policy == OVM_REFERENCE))
        begin
          if(((rhs == null) && (lhs != null)) || ((lhs==null) && (rhs!=null))) begin
            ovm_auto_options_object.comparer.print_msg_object(lhs, rhs);
            return 1;  //miscompare
          end
          if((rhs == null) && (lhs==null))
            return 0;
          else begin
            bit r;
            r = lhs.compare(rhs, ovm_auto_options_object.comparer);
            if(r == 0) begin
              return 1;
            end
            else begin
              return 0;
            end
          end
        end
        else begin //reference compare
          if(lhs != rhs) begin
            ovm_auto_options_object.comparer.print_msg_object(lhs, rhs);
            return 1;
          end
        end
      end
    OVM_PACK:
      begin
        if(((flag&OVM_NOPACK) == 0) && ((flag&OVM_REFERENCE)==0)) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
            ovm_auto_options_object.packer.pack_object(lhs);
          end
        end
        return 0;
      end
    OVM_UNPACK:
      begin
        if(((flag&OVM_NOPACK) == 0) && ((flag&OVM_REFERENCE)==0)) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
          ovm_auto_options_object.packer.unpack_object_ext(lhs);
          end
        end
        return 0;
      end
    OVM_PRINT:
      begin
        if(((flag)&OVM_NOPRINT) == 0) 
        begin  
          if(((flag)&OVM_REFERENCE) || (lhs == null)) begin
            int d;
            d = ovm_auto_options_object.printer.knobs.depth;
            ovm_auto_options_object.printer.knobs.depth = 0;
            ovm_auto_options_object.printer.print_object(arg, lhs);
            ovm_auto_options_object.printer.knobs.depth = d;
          end
          else begin
            ovm_component obj;
            if(lhs != null) begin
              if($cast(obj,lhs)) begin 
                if(ovm_auto_options_object.printer.m_scope.current() == obj.get_parent() )
                  ovm_auto_options_object.printer.print_object(arg, lhs);
                else
                  ovm_auto_options_object.printer.print_object_header(arg, lhs);
              end
              else begin
                ovm_auto_options_object.printer.print_object(arg, lhs);
              end
            end
          end
        end
      end
    OVM_RECORD:
      begin
        if(((flag)&OVM_NORECORD) == 0) 
        begin 
          m_sc.scope.up(lhs); //need to scope up since gets scoped down before
          if(lhs != null && lhs.get_name()!="") arg = lhs.get_name(); 
          //If refernce is on then don't want to do cycle check since only
          //recording the reference.
          if( ((flag) & int'(OVM_REFERENCE)) != 0) 
            m_record_field_object(arg, lhs, ovm_auto_options_object.recorder,flag);
          else begin
            if(!m_sc.scope.in_hierarchy(lhs)) 
              m_record_field_object(arg, lhs, ovm_auto_options_object.recorder,flag);
          end
          m_sc.scope.down(arg,lhs); //need to scope back dwon
        end 
      end
  endcase
  return 0;
endfunction


// m_do_data_string (static)
// ----------------

// function m_do_data_string (arg, lhs, rhs, what, flag)
//   Precondition:
//     arg       -- the name of the short name of the lhs object
//     lhs       -- the lhs to do work on (left hand side)
//     lhs       -- the rhs to do work from (right hand side)
//     what      -- integer, what to do
//     flag      -- object flags
//

function int ovm_object::m_do_data_string(string arg,
                                      inout string lhs,
                                      input string rhs,
                                            int what,
                                            int flag);

  if (what > OVM_END_DATA_EXTRA)
     return 0;

  case (what)
    OVM_COPY:
      begin
        if(((flag)&OVM_NOCOPY) == 0) begin
          lhs = rhs;
        end
        return 0;
      end
    OVM_COMPARE:
      begin
        if(((flag)&OVM_NOCOMPARE) == 0) begin
          if(lhs != rhs) begin
            m_sc.stringv = { "lhs = \"", lhs, "\" : rhs = \"", rhs, "\""};
            ovm_auto_options_object.comparer.print_msg(m_sc.stringv);
            return 1;
          end
        end
        return 0;
      end
    OVM_PACK:
      begin 
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
          ovm_auto_options_object.packer.pack_string(lhs);
          end
        end
        return 0;
      end
    OVM_UNPACK:
      begin
        if(((flag)&OVM_NOPACK) == 0) begin
          if(((flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) ||
             (!(flag&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin
          lhs = ovm_auto_options_object.packer.unpack_string();
          end
        end
        return 0;
      end
    OVM_PRINT:
      begin
        if(((flag)&OVM_NOPRINT) == 0) 
        begin  
          ovm_auto_options_object.printer.print_string(arg, lhs);
        end
      end
    OVM_RECORD:
      begin
        if(((flag)&OVM_NORECORD) == 0) 
        begin 
          m_sc.scope.up(null); //need to scope up since gets scoped down before
          ovm_auto_options_object.recorder.record_string(arg, lhs);
          m_sc.scope.down(arg,null); //need to scope back dwon
        end 
      end
  endcase
  return 0;

endfunction


//-----------------------------------------------------------------------------
//
// ovm_status_container
//
//-----------------------------------------------------------------------------

function string ovm_status_container::get_full_scope_arg ();
  get_full_scope_arg = scope.get_arg();
endfunction

function ovm_scope_stack ovm_status_container::init_scope();
  if(scope==null) scope=new;
  return scope;
endfunction

//-----------------------------------------------------------------------------
//
// ovm_options_container
//
//-----------------------------------------------------------------------------

ovm_options_container ovm_auto_options_object = ovm_options_container::init();

function ovm_options_container::new();
  comparer = ovm_default_comparer;
  packer   = ovm_default_packer;
  recorder = ovm_default_recorder;
  printer  = ovm_default_printer;
endfunction

function ovm_options_container ovm_options_container::init();
  if(ovm_auto_options_object==null) ovm_auto_options_object=new;
  return ovm_auto_options_object;
endfunction

