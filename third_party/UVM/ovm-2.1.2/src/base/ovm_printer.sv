// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_printer.sv#25 $
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

`include "base/ovm_printer.svh"

function string ovm_printer_knobs::get_radix_str(ovm_radix_enum radix);
  if(show_radix == 0) return "";
  if(radix == OVM_NORADIX) radix = default_radix;
  case(radix)
    OVM_BIN: return bin_radix;
    OVM_OCT: return oct_radix;
    OVM_UNSIGNED: return unsigned_radix;
    OVM_DEC: return dec_radix;
    OVM_HEX: return hex_radix;
    default:  return "";
  endcase
endfunction

//------------------------------------------------------------------------------
//
// Loose functions for utility-
//   int ovm_num_characters (ovm_radix_enum radix, ovm_bitstream_t value, int size)
//   string ovm_vector_to_string (ovm_bitstream_t value, int size, 
//                                ovm_radix_enum radix=OVM_NORADIX);
// 
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// ovm_num_characters
// --------------
//
// int ovm_num_characters (ovm_radix_enum radix, ovm_bitstream_t value, int size)
//   Precondition:
//     radix: the radix to use to calculate the number of characters
//     value: integral value to test to find number of characters
//     size:  number of bits in value
//     radix_str: the string that identifes the radix
//   Postcondition:
//     Returns the minimum number of ascii characters needed to represent
//     value in the desired base.
//------------------------------------------------------------------------------

function automatic int ovm_num_characters (ovm_radix_enum radix, ovm_bitstream_t value, 
      int size, string radix_str="");
  int chars;
  int r;
  ovm_bitstream_t mask;
  if(radix==OVM_NORADIX)
    radix = OVM_HEX;

  mask = {OVM_STREAMBITS{1'b1}};
  mask <<= size;
  mask = ~mask;
  value &= mask;

  //fast way of finding number of characters is to use division, slow way
  //is to construct a string. But, if x's are in the value then the  
  //string method is much easier.
  if((^value) !== 1'bx) begin
    case(radix)
      OVM_BIN: r = 2;
      OVM_OCT: r = 8;
      OVM_UNSIGNED: r = 10;
      OVM_DEC: r = 10;
      OVM_HEX: r = 16;
      OVM_TIME: r = 10;
      OVM_STRING: return size/8;
      default:  r = 16;
    endcase
    chars = radix_str.len() + 1;
    if((radix == OVM_DEC) && (value[size-1] === 1)) begin
      //sign extend and get 2's complement of value
      mask = ~mask;
      value |= mask;
      value = ~value + 1;
      chars++; //for the negative
    end
    for(ovm_bitstream_t i=r; value/i != 0; i*=r) 
      chars++;
    return chars;
  end
  else begin
    string s;
    s = ovm_vector_to_string(value, size, radix, radix_str);
    return s.len();
  end
endfunction

function string ovm_vector_to_string (ovm_bitstream_t value, int size,
                                      ovm_radix_enum radix=OVM_NORADIX,
                                      string radix_str="");
  ovm_bitstream_t mask;
  string str;

  mask = {OVM_STREAMBITS{1'b1}};
  mask <<= size;
  mask = ~mask;

  case(radix)
    OVM_BIN:     begin
               $swrite(str, "%0s%0b", radix_str, value&mask);
             end
    OVM_OCT:     begin
               $swrite(str, "%0s%0o", radix_str, value&mask);
             end
    OVM_UNSIGNED: begin
               $swrite(str, "%0s%0d", radix_str, (value&mask));
             end
    OVM_DEC:     begin
               if(value[size-1] === 1) begin
                 //sign extend for negative value
                 ovm_bitstream_t sval; mask = ~mask; 
                 sval = (value|mask);
                 //don't show radix for negative
                 $swrite(str, "%0d", sval);
               end
               else begin
                 $swrite(str, "%0s%0d", radix_str, (value&mask));
               end
             end
    OVM_STRING:  begin
               $swrite(str, "%0s%0s", radix_str, value&mask);
             end
    OVM_TIME:    begin
               $swrite(str, "%0s%0t", radix_str, value&mask);
             end
    default: begin
               $swrite(str, "%0s%0x", radix_str, value&mask);
             end
  endcase
  return str;
endfunction

//------------------------------------------------------------------------------
//
// Class- ovm_printer
//
//------------------------------------------------------------------------------

// write_stream
// ------------

function void ovm_printer::write_stream(string str);
  string space;
  if(!knobs.max_width) return;
  if((str.len() > 0) && (str[str.len()-1] == " ")) begin
    space = " ";
    str = str.substr(0,str.len()-2);
  end
  else space = "";

  if((knobs.max_width != -1) && (str.len() > knobs.max_width)) begin
    str = {str.substr(0, knobs.max_width-2), knobs.truncation}; 
  end
  if(knobs.sprint)
    m_string = {m_string, str, space};
  else
    $fwrite(knobs.mcd, "%s%s", str, space);
  knobs.column+=str.len()+space.len();
endfunction


// print_header
// ------------

function void ovm_printer::print_header();
  if(!m_scope.depth()) begin
    m_scope.set_arg("");
    m_string = "";
    write_stream(knobs.prefix);
    indent(knobs.global_indent, " ");
  end
  return;
endfunction


// print_footer
// ------------

function void ovm_printer::print_footer();
  return;
endfunction


// print_id
// --------

function void ovm_printer::print_id(string id, byte scope_separator=".");
  string str, idstr;
  if(id == "") return;
  if(knobs.identifier) begin
    if(knobs.full_name || id == "...") begin
      str = { id, " " };
    end
    else begin
      str = ovm_leaf_scope(id, scope_separator);
    end
    write_stream(str);
  end
  return;
endfunction


// print_type_name
// ---------------

function void ovm_printer::print_type_name(string name, bit is_object=0);
  if(knobs.type_name && name.len() && name != "-") begin
    write_stream(" (");
    write_stream(name);
    write_stream(")");
  end
  return;
endfunction


// print_size
// ----------

function void ovm_printer::print_size(int size=-1);
  string str;
  if(!knobs.size)
    return;
  if(size == -1)
    return;
  else
    $swrite(str, "%0d", size);

  if(knobs.sprint)
    m_string = {m_string, " (", str, ") "};
  else
    $fwrite(knobs.mcd, " (%s) ", str);
  knobs.column+=str.len()+4;
  return;
endfunction


// print_value
// -----------

function void ovm_printer::print_value(ovm_bitstream_t value, int size,
                                       ovm_radix_enum radix=OVM_NORADIX);
  string str;

  if(radix == OVM_NORADIX)
    radix = knobs.default_radix;
  str = ovm_vector_to_string (value, size, radix, knobs.get_radix_str(radix));

//  if(knobs.sprint)
//    m_string = {m_string, str};
//  else
//    $fwrite(knobs.mcd, "%s", str);
//  knobs.column+=str.len();
  write_stream(str);
endfunction


// print_value_object
// ------------------

function void ovm_printer::print_value_object (ovm_object value);
  string str;
  if(!knobs.reference) return;
`ifdef INCA
  str = ovm_object_value_str(value);
  write_stream({"(", str, ")"});
`else
`endif
endfunction


// print_value_string
// ------------------

function void ovm_printer::print_value_string (string value);
  if(value != "-")
    write_stream ( value );
endfunction


// print_value_array
// -----------------

function void ovm_printer::print_value_array (string value="", int size=0);
  write_stream(value);
endfunction


// print_array_header
// ------------------

function void ovm_printer::print_array_header (string name, int size,
    string arraytype="array", byte scope_separator=".");

  if(name != "")
    m_scope.set_arg(name);
  print_id (m_scope.get_arg(), scope_separator);
  print_type_name (arraytype);
  print_size (size);
  print_value_array("", size);
  print_newline();
  m_scope.down(name, null);
  m_array_stack.push_back(1);
endfunction


// print_array_footer
// ------------------

function void  ovm_printer::print_array_footer (int size=0);
  if(m_array_stack.size()) begin
    m_scope.up(null);
    void'(m_array_stack.pop_front());
  end
endfunction


// print_array_range
// -----------------

function void ovm_printer::print_array_range(int min, int max);
  string tmpstr;
  if(min == -1 && max == -1) return;
  if(min == -1) min = max;
  if(max == -1) max = min;
  if(max < min) return;
//  $swrite(tmpstr, "[%0d:%0d]", min, max);
  tmpstr = "...";
  print_generic(tmpstr, "...", -2, " ...");
endfunction


// print_field
// -----------

function void ovm_printer::print_field (string name,
                                        ovm_bitstream_t value, 
                                        int size, 
                                        ovm_radix_enum radix=OVM_NORADIX,
                                        byte scope_separator=".",
                                        string type_name="");
  print_header();

  if(name != "")
    m_scope.set_arg(name);

  print_id (m_scope.get_arg(), scope_separator);
  if(type_name != "") begin
    print_type_name(type_name);
  end
  else begin
    if(radix == OVM_TIME)
      print_type_name ("time");
    else if(radix == OVM_STRING)
      print_type_name ("string");
    else
      print_type_name ("integral");
  end
  print_size (size);
  print_value ( value, size, radix);
  print_newline();

  print_footer();
endfunction
  

// print_time
// ----------

function void ovm_printer::print_time (string name, time value,
                                       byte scope_separator=".");
  print_field(name, value, 64, OVM_TIME, scope_separator);
endfunction


// print_object_header
// -------------------

function void ovm_printer::print_object_header ( string name,
                                                ovm_object value, 
                                                byte scope_separator=".");
  print_header();

  if(name != "")
    m_scope.set_arg(name);
  print_id (m_scope.get_arg(), scope_separator);

  if(value != null) 
    print_type_name(value.get_type_name());
  else
    print_type_name ("object");
  print_size (-1);
  print_value_object ( value );
  print_newline();
endfunction


// print_object
// ------------

function void ovm_printer::print_object (string name, ovm_object value,
                                         byte scope_separator=".");
  ovm_component    named, child;

  if(name == "") begin
    if(value!=null) begin
      if((m_scope.depth()==0) && $cast(named, value)) begin
        name = named.get_full_name();
      end
      else begin
        name=value.get_name();
      end
    end
  end
        
  if(name == "") 
    name = "<unnamed>";

  print_object_header(name, value, scope_separator);

  if(value != null) 
    if((knobs.depth == -1 || (knobs.depth > m_scope.depth())) &&
       !m_scope.in_hierarchy(value)) 
    begin

      m_scope.down(name, value);

      //Handle children of the named_object
      if($cast(named, value)) begin
        string name;
        if (named.get_first_child(name))
          do begin
            child = named.get_child(name);
            if(child.print_enabled)
              this.print_object("",child);
          end while (named.get_next_child(name));
      end
      if(knobs.sprint)
        //ignore the return because the m_string will be appended
        void'(value.sprint(this));
      else begin
        value.print(this);
      end

      if(name[0] == "[")
        m_scope.up(value,"[");
      else
        m_scope.up(value,".");
    end

  print_footer();
endfunction


// istop
// -----

function bit ovm_printer::istop ();
  return (m_scope.depth() == 0);
endfunction


// print_string
// ------------

function void ovm_printer::print_string (string name, string value,
                                         byte scope_separator=".");
  print_header();

  if(name != "")
    m_scope.set_arg(name);

  print_id (m_scope.get_arg(), scope_separator);
  print_type_name ("string");
  print_size (value.len());
  //print_value_string ( {"\"", value, "\""} );
  print_value_string ( value );
  print_newline();

  print_footer();
endfunction


// print_newline
// -------------

function void ovm_printer::print_newline(bit do_global_indent=1);
  write_stream("\n");
  if(do_global_indent) begin
    write_stream(knobs.prefix);
    indent(knobs.global_indent, " ");
  end
  knobs.column=0;
  return;
endfunction


// print_generic
// -------------

function void ovm_printer::print_generic (string name, string type_name,        
     int size, string value, byte scope_separator=".");
  print_header();

  if(name != "")
    m_scope.set_arg(name);

  if(name == "...")
    print_id (name, scope_separator);
  else
    print_id (m_scope.get_arg(), scope_separator);
  print_type_name (type_name);
  print_size (size);
  print_value_string ( value );
  print_newline();

  print_footer();
endfunction


// print_field_real
// ---------------

function void ovm_printer::print_field_real (string name, 
     real value, byte scope_separator=".");
  string str;
  print_header();

  if(name != "")
    m_scope.set_arg(name);

  print_id (name, scope_separator);
  print_type_name ("real");
  print_size (64);
  $swrite(str,value);
  print_value_string ( str );
  print_newline();

  print_footer();
endfunction


// index
// -----

function int ovm_printer::index(string name);
  string tmp;
  if(name == "" || name[name.len()-1] != "]")
    return -1;
  tmp="";
  for(int c = name.len()-2; c>=0 && name[c] != "["; --c) begin
    tmp = {" ", tmp};
    tmp[0] = name[c];
  end
  if(!tmp.len())
    return -1;
  return tmp.atoi();
endfunction


// index_string
// ------------

function string ovm_printer::index_string(int index, string name="");
  index_string.itoa(index);
  index_string = { name, "[", index_string, "]" }; 
endfunction


// indent
// ------

function void ovm_printer::indent(int depth, string indent_str="  ");
  for(int i=0; i<depth; ++i) begin
    write_stream(indent_str);
  end
endfunction

  
//------------------------------------------------------------------------------
//
// Class- ovm_table_printer
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_table_printer::new(); 
  super.new();
  super.knobs = knobs;
endfunction


// print_header
// ------------

function void ovm_table_printer::print_header();
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  ovm_printer::print_header();
  if(!knobs.header || m_scope.depth() != 0) return;

  for(int i=0; 
      i<(knobs.name_width+type_width+size_width+knobs.value_width); 
      ++i)
    write_stream("-");

  print_newline();
  if(knobs.name_width) begin
    if(knobs.max_width != -1) knobs.max_width = knobs.name_width;
    write_stream("Name ");
    indent(knobs.name_width-5, " ");
  end
  if(type_width) begin
    if(knobs.max_width != -1) knobs.max_width = type_width;
    write_stream("Type ");
    indent(type_width-5, " ");
  end
  if(size_width) begin
    if(knobs.max_width != -1) knobs.max_width = size_width-1;
    write_stream("Size ");
    indent(size_width-5, " ");
  end
  if(knobs.value_width) begin
    if(knobs.max_width != -1) knobs.max_width = knobs.value_width;
    indent(knobs.value_width-5, " ");
    write_stream("Value");
  end

  print_newline();
  for(int i=0; 
      i<(knobs.name_width+type_width+size_width+knobs.value_width); 
      ++i)
    write_stream("-");
  print_newline();
  knobs.column=0;
endfunction


// print_footer
// ------------

function void ovm_table_printer::print_footer();
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  if(!knobs.footer || m_scope.depth() != 0) return;
  for(int i=0; 
      i<(knobs.name_width+type_width+size_width+knobs.value_width); 
      ++i) 
    write_stream("-");
  print_newline(0);
  knobs.column=0;
endfunction


// print_id
// --------

function void ovm_table_printer::print_id (string id, byte scope_separator=".");
  int fn;
  if(!knobs.name_width) return;
  if(knobs.max_width != -1) 
    knobs.max_width=knobs.name_width-
                    (m_scope.depth()*knobs.indent_str.len())-1;
  fn = knobs.full_name;
  if(knobs.show_root && m_scope.depth()==0) 
     knobs.full_name = 1;

  indent(m_scope.depth(), knobs.indent_str);
  super.print_id(id, scope_separator);
  indent(knobs.name_width-knobs.column, " ");

  knobs.full_name = fn;
endfunction


// print_type_name
// ---------------

function void ovm_table_printer::print_type_name (string name, bit is_object=0);
  int type_width = knobs.type_name ? knobs.type_width : 0;

  if(!type_width) return;
  if(knobs.max_width != -1) knobs.max_width = type_width-1;

  indent(knobs.name_width-knobs.column, " ");
  if(knobs.type_name) begin
    write_stream({name, " "});
  end
  indent((knobs.name_width+type_width)-knobs.column, " ");
endfunction


// print_size
// ----------

function void ovm_table_printer::print_size (int size=-1);
  string str;
  int chars;
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  if(!size_width) return;
  if(knobs.max_width != -1) knobs.max_width = size_width-1;

  if(!knobs.size)
    size = -1;

  if(size == -1) chars = 1;
  else chars = ovm_num_characters (OVM_DEC, size, 32);
  indent(type_width-knobs.column-1, " ");
  indent(size_width-knobs.column-chars-1, " ");
  if(size == -1)
    str = "-";
  else if(size == -2)
    str = "...";
  else
    $swrite(str, "%0d", size);
  indent((knobs.name_width+type_width)-knobs.column, " ");
  write_stream(str);
  write_stream(" ");
  indent((knobs.name_width+type_width+size_width)-knobs.column,
          " ");
  return;
endfunction


// print_value
// -----------

function void ovm_table_printer::print_value (ovm_bitstream_t value, int size,
     ovm_radix_enum radix=OVM_NORADIX);
  int chars;
  string s;
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  if(!knobs.value_width) return;
  if(knobs.max_width != -1) knobs.max_width = knobs.value_width;

  if(radix==OVM_NORADIX) radix = knobs.default_radix;
  if(radix != OVM_TIME) begin
    if(knobs.show_radix) begin
      if((radix != OVM_DEC) || (value[size-1] !== 1)) //for negative, don't print radix
        chars = ovm_num_characters(radix, value, size, knobs.get_radix_str(radix));
      else
        chars = ovm_num_characters(radix, value, size);
    end
    else
      chars = ovm_num_characters(radix, value, size);
  end
  else begin
    $swrite(s, "%0t", value);
    chars = s.len();
  end
  indent((knobs.name_width+type_width+size_width)-knobs.column,
          " ");
  indent(knobs.value_width-chars, " ");
  super.print_value(value, size, radix);
endfunction


// ovm_object_value_str 
// ---------------------

// This function is needed to work around a but in $swrite
function string ovm_object_value_str(ovm_object v);
  if(v == null) return "<null>";
`ifdef INCA
  $swrite(ovm_object_value_str, "@%0d",v);
`else
  ovm_object_value_str.itoa(v.get_inst_id());
  ovm_object_value_str = {v.get_name(),"@",ovm_object_value_str};
`endif
endfunction

// print_value_object
// ------------------
function void ovm_table_printer::print_value_object (ovm_object value);
  string str;
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  if(!knobs.value_width) return;
  if(knobs.max_width != -1) knobs.max_width = knobs.value_width-1;
  if(!knobs.reference) begin
    indent((knobs.name_width+type_width+size_width)-knobs.column,
            " ");
    indent(knobs.value_width-1, " ");
    write_stream("-");
  end
  else begin
    indent((knobs.name_width+type_width+size_width)-knobs.column,
            " ");
    str = ovm_object_value_str(value);
    indent(knobs.value_width-str.len(), " ");
    if(!knobs.sprint) begin
      write_stream(str);
    end
    else begin
      m_string = {m_string, str};
    end
  end
endfunction


// print_value_string
// ------------------

function void ovm_table_printer::print_value_string (string value);
  int type_width = knobs.type_name ? knobs.type_width : 0;
  int size_width = knobs.size ? knobs.size_width : 0;

  if(!knobs.value_width) return;
  if(knobs.max_width != -1) knobs.max_width = knobs.value_width;

  indent((knobs.name_width+type_width+size_width)-knobs.column,
          " ");
  indent(knobs.value_width-value.len(), " ");
  write_stream(value);
endfunction


// print_value_array
// -----------------

function void  ovm_table_printer::print_value_array (string value="", 
                                                     int size=0); 
  if(!value.len())
    value = "-";
  print_value_string(value);
endfunction

//------------------------------------------------------------------------------
//
// Class- ovm_tree_printer
//
//------------------------------------------------------------------------------


// print_value_object
// ------------------

function ovm_tree_printer::new();
  super.new();
  super.knobs = knobs;
  knobs.size = 0;
endfunction


// print_scope_close
// -----------------

function void ovm_tree_printer::print_scope_close();
  if(((knobs.depth == -1) || (knobs.depth > m_scope.depth())) && 
      (knobs.separator.len()==2))
   begin
    indent(m_scope.depth(), knobs.indent_str);
    if(knobs.sprint) begin
      //Can't use swrite on a string index, so use this workaround
      //$swrite(m_string, "%c", knobs.separator[1]);
      m_string = {m_string, " "};
      m_string[m_string.len()-1] = knobs.separator[1];
    end
    else begin
      $fwrite(knobs.mcd, "%c", knobs.separator[1]);
    end
    if(m_scope.depth())
      print_newline();
    else
      print_newline(0);
    knobs.column=0;
  end
  return;
endfunction


// print_scope_open
// ----------------

function void ovm_tree_printer::print_scope_open();
  if(((knobs.depth == -1) || (knobs.depth > m_scope.depth())) && 
      knobs.separator.len()>0) 
  begin
    if(knobs.sprint) begin
      //Can't use swrite on a string index, so use this workaround
      //$swrite(m_string, "%c", knobs.separator[0]);
      m_string = {m_string, "  "};
      m_string[m_string.len()-1] = knobs.separator[0];
    end
    else
      $fwrite(knobs.mcd, " %c", knobs.separator[0]);
    knobs.column++;
  end
  return;
endfunction


// print_id
// --------

function void ovm_tree_printer::print_id (string id, byte scope_separator=".");
  int fn;
  fn = knobs.full_name;
  if(knobs.show_root && m_scope.depth()==0) 
     knobs.full_name = 1;

  indent(m_scope.depth(), knobs.indent_str);
  super.print_id(id, scope_separator);
  if(id == "" || id == "...") return;
  write_stream(": "); 

  knobs.full_name = fn;
endfunction


// print_type_name
// ---------------

function void ovm_tree_printer::print_type_name (string name, bit is_object=0);
  if(knobs.type_name && name.len()>0) begin
    if(is_object)
    begin
      write_stream("("); 
      write_stream(name);
      if(!knobs.reference) 
        write_stream(")"); //end paren is printed by ::print_value_object
    end
  end
endfunction


// print_string
// ------------

function void ovm_tree_printer::print_string (string name, string value,
                                              byte scope_separator=".");
  print_header();

  if(name != "")
    m_scope.set_arg(name);

  print_id (m_scope.get_arg(), scope_separator);
  print_type_name ("string");
  //print_value_string ( {"\"", value, "\""} );
  print_value_string ( value );
  print_newline();

  print_footer();
endfunction


// print_object_header
// -------------------

function void ovm_tree_printer::print_object_header ( string name,
                                                     ovm_object value, 
                                                     byte scope_separator=".");
  ovm_component no;
  print_header();

  if(name != "" && name != "<unnamed>")
    m_scope.set_arg(name);
  print_id (m_scope.get_arg(), scope_separator);

  if(value!=null)
    print_type_name(value.get_type_name(), 1);
  else
    print_type_name ("object", 1);
  print_size (-1);
  print_value_object ( value );
  print_newline();
endfunction


// print_object
// ------------

function void ovm_tree_printer::print_object (string name, ovm_object value,
                                              byte scope_separator=".");
  super.print_object(name, value, scope_separator);
  if(value!=null)
    print_scope_close();
endfunction


// print_value_object
// ------------------

function void ovm_tree_printer::print_value_object (ovm_object value);
  string str;
  if(!knobs.reference) begin
    if(value!=null)
      print_scope_open();
    return;
  end
`ifdef INCA
  str = ovm_object_value_str(value);
  if(value == null)
    write_stream(" <null>) "); 
  else
    write_stream({str, ") "}); 
`else
  write_stream(") ");
`endif
  if(value!=null)
    print_scope_open();
endfunction

// print_value_array
// -----------------

function void  ovm_tree_printer::print_value_array (string value= "", 
                                                    int    size=0);
  if(size && ((knobs.depth == -1) || (knobs.depth > m_scope.depth()+1)))
    print_scope_open();
endfunction


// print_array_footer
// ------------------

function void  ovm_tree_printer::print_array_footer (int size=0);
  ovm_printer::print_array_footer(size);
  if(size)
    print_scope_close();
endfunction


//------------------------------------------------------------------------------
//
// Class- ovm_line_printer
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_line_printer::new(); 
  super.new();
  knobs.indent_str = "";
endfunction


// print_newline
// -------------

function void ovm_line_printer::print_newline (bit do_global_indent=1);
  write_stream(" ");
endfunction


//------------------------------------------------------------------------------
//
// Class- ovm_hier_printer_knobs
//
//------------------------------------------------------------------------------


// new
// ---

function ovm_hier_printer_knobs::new(); 
  full_name = 0; 
endfunction


