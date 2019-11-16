// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_printer.svh#12 $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

`ifndef OVM_PRINTER_SVH
`define OVM_PRINTER_SVH


typedef class ovm_printer_knobs;
typedef class ovm_hier_printer_knobs;
typedef class ovm_table_printer_knobs;
typedef class ovm_tree_printer_knobs;

parameter OVM_STDOUT = 1;  // Writes to standard out and logfile

//------------------------------------------------------------------------------
//
// CLASS: ovm_printer
//
// The ovm_printer class provides an interface for printing <ovm_objects> in
// various formats. Subtypes of ovm_printer implement different print formats,
// or policies.
//
// A user-defined printer format can be created, or one of the following four
// built-in printers can be used:
//
// (see ovm_ref_printer.gif)
//
// - <ovm_printer> - provides raw, essentially un-formatted output
//
// - <ovm_table_printer> - prints the object in a tabular form. 
//
// - <ovm_tree_printer> - prints the object in a tree form. 
//
// - <ovm_line_printer> - prints the information on a single line, but uses the
//   same object separators as the tree printer.
//
// Printers have knobs that you use to control what and how information is printed.
// These knobs are contained in separate knob classes:
//
// (see ovm_ref_printer_knobs.gif)
//
// - <ovm_printer_knobs> - common printer settings
//
// - <ovm_hier_printer_knobs> - settings for printing hierarchically
//
// - <ovm_table_printer_knobs> - settings specific to the table printer
//
// - <ovm_tree_printer_knobs> - settings specific to the tree printer
//
//
// For convenience, global instances of each printer type are available for
// direct reference in your testbenches.
//
//  -  <ovm_default_tree_printer>
//  -  <ovm_default_line_printer>
//  -  <ovm_default_table_printer>
//  -  <ovm_default_printer> (set to default_table_printer by default)
//
// The <ovm_default_printer> is used by <ovm_object::print> and <ovm_object::sprint>
// when the optional ~ovm_printer~ argument to these methods is not provided. 
//
//------------------------------------------------------------------------------

class ovm_printer;

  // Variable: knobs
  //
  // The knob object provides access to the variety of knobs associated with a
  // specific printer instance. 
  //
  // Each derived printer class overwrites the knobs variable with the
  // a derived knob class that extends <ovm_printer_knobs>. The derived knobs
  // class adds more knobs to the base knobs.

  ovm_printer_knobs knobs = new;


  // Group: Methods for printer usage

  // These functions are called from <ovm_object::print>, or they are called
  // directly on any data to get formatted printing.

  // Function: print_field
  //
  // Prints an integral field.
  //
  // name  - The name of the field. 
  // value - The value of the field.
  // size  - The number of bits of the field (maximum is 4096). 
  // radix - The radix to use for printingthe printer knob for radix is used
  //           if no radix is specified. 
  // scope_separator - is used to find the leaf name since many printers only
  //           print the leaf name of a field.  Typical values for the separator
  //           are . (dot) or [ (open bracket).

  extern virtual function void print_field (string  name, 
                                            ovm_bitstream_t value, 
                                            int     size, 
                                            ovm_radix_enum  radix=OVM_NORADIX,
                                            byte    scope_separator=".",
                                            string  type_name="");


  // Function: print_object_header
  //
  // Prints the header of an object. 
  //
  // This function is called when an object is printed by reference. 
  // For this function, the object will not be recursed.

  extern virtual function void print_object_header (
                                            string     name,
                                            ovm_object value, 
                                            byte       scope_separator=".");


  // Function: print_object
  //
  // Prints an object. Whether the object is recursed depends on a variety of
  // knobs, such as the depth knob; if the current depth is at or below the
  // depth setting, then the object is not recursed. 
  //
  // By default, the children of <ovm_components> are printed. To turn this
  // behavior off, you must set the <ovm_component::print_enabled> bit to 0 for
  // the specific children you do not want automatically printed.

  extern virtual function void print_object (string     name,
                                             ovm_object value, 
                                             byte       scope_separator=".");


  // Function: print_string
  //
  // Prints a string field.

  extern virtual function void print_string (string name,
                                             string value, 
                                             byte   scope_separator=".");


  // Function: print_time
  //
  // Prints a time value. name is the name of the field, and value is the
  // value to print. 
  //
  // The print is subject to the ~$timeformat~ system task for formatting time
  // values.

  extern virtual function void print_time (string name,
                                           time   value, 
                                           byte   scope_separator=".");


  // Group: Methods for printer subtyping

  // Function: print_header
  //
  // Prints header information. It is called when the current depth is 0,
  // before any fields have been printed.

  extern virtual function void print_header ();


  // Function: print_footer
  //
  // Prints footer information.  It is called when the current depth is 0,
  // after all fields have been printed.

  extern virtual function void print_footer ();


  // Function: print_id
  //
  // Prints a field's name, or ~id~, which is the full instance name.
  //
  // The intent of the separator is to mark where the leaf name starts if the
  // printer if configured to print only the leaf name of the identifier. 

  extern virtual protected function void print_id (string id, 
                                                   byte scope_separator=".");


  // Function: print_type_name
  //
  // Prints a field's type name. 
  //
  // The ~is_object~ bit indicates that the item being printed is an object
  // derived from <ovm_object>.

  extern virtual protected function void print_type_name (string name,
                                                          bit is_object=0);


  // Function: print_size
  //
  // Prints a field's size.  A size of -1 indicates that no size is available,
  // in which case the printer inserts the appropriate white space if the format
  // requires it.

  extern virtual protected function void print_size (int size=-1);


  // Function: print_newline
  //
  // Prints a newline character.  It is up to the printer to determine how
  // or whether to display new lines.  The ~do_global_indent~ bit indicates
  // whether the call to print_newline() should honor the indent knob.

  extern virtual protected function void print_newline (bit do_global_indent=1);


  // Function: print_value
  //
  // Prints an integral field's value. 
  //
  // The ~value~ vector is up to 4096 bits, and the ~size~ input indicates the
  // number of bits to actually print. 
  //
  // The ~radix~ input is the radix that should be used for printing the value.

  extern virtual protected function void print_value (ovm_bitstream_t value, 
                                             int size, 
                                             ovm_radix_enum  radix=OVM_NORADIX);
  
  
  // Function: print_value_object
  //
  // Prints a unique handle identifier for the given object.
  
  extern virtual protected function void print_value_object (ovm_object value);


  // Function: print_value_string
  //
  // Prints a string field's value.

  extern virtual protected function void print_value_string (string value);


  // Function: print_value_array
  //
  // Prints an array's value. 
  //
  // This only prints the header value of the array, which means that it
  // implements the printer-specific print_array_header(). 
  //
  // ~value~ is the value to be printed for the array. It is generally the
  // string representation of ~size~, but it may be any string. ~size~ is the
  // number of elements in the array.

  extern virtual  function void print_value_array (string value="", 
                                                   int size=0);


  // Function: print_array_header
  //
  // Prints the header of an array. This function is called before each
  // individual element is printed. <print_array_footer> is called to mark the
  // completion of array printing.

  extern virtual  function void print_array_header(
                                         string name,
                                         int    size,     
                                         string arraytype="array",
                                         byte   scope_separator=".");


  // Function: print_array_range
  //
  // Prints a range using ellipses for values. This method is used when honoring
  // the array knobs for partial printing of large arrays, 
  // <ovm_printer_knobs::begin_elements> and <ovm_printer_knobs::end_elements>. 
  //
  // This function should be called after begin_elements have been printed
  // and after end_elements have been printed.

  extern virtual function void print_array_range (int min, int max);


  // Function: print_array_footer
  //
  // Prints the header of a footer. This function marks the end of an array
  // print. Generally, there is no output associated with the array footer, but
  // this method lets the printer know that the array printing is complete.

  extern virtual  function void print_array_footer (int size=0);



  extern virtual protected function void indent (int    depth, 
                                                 string indent_str="  ");



  extern virtual function void print_field_real (string  name, 
                                           real    value,
                                           byte    scope_separator=".");


  extern virtual function void print_generic (string  name, 
                                              string  type_name, 
                                              int     size, 
                                              string  value,
                                              byte    scope_separator=".");

  // Utility methods
  extern  function bit istop ();
  extern  function int index (string name);
  extern  function string index_string (int index, string name="");
  extern protected function void  write_stream (string str);

  protected bit m_array_stack[$];
  ovm_scope_stack m_scope = new;
  string m_string = "";

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_table_printer
//
// The table printer prints output in a tabular format.
//
// The following shows sample output from the table printer.
//
//|  ---------------------------------------------------
//|  Name        Type            Size        Value
//|  ---------------------------------------------------
//|  c1          container       -           @1013
//|  d1          mydata          -           @1022
//|  v1          integral        32          'hcb8f1c97
//|  e1          enum            32          THREE
//|  str         string          2           hi
//|  value       integral        12          'h2d
//|  ---------------------------------------------------
//
//------------------------------------------------------------------------------

class ovm_table_printer extends ovm_printer;

  // Variable: new
  //
  // Creates a new instance of ~ovm_table_printer~.

  extern  function new(); 

  // Variable: knobs
  //
  // An instance of <ovm_table_printer_knobs>, which govern the content
  // and format of the printed table.

  ovm_table_printer_knobs knobs = new;

  // Adds column headers
  extern virtual function void print_header       ();
  extern virtual function void print_footer       ();

  // Puts information in column format
  extern virtual function void print_id (string id, byte scope_separator=".");
  extern virtual function void print_size         (int         size=-1);
  extern virtual function void print_type_name    (string      name, bit is_object=0);
  extern virtual function void print_value (ovm_bitstream_t value, 
                                            int size, 
                                            ovm_radix_enum  radix=OVM_NORADIX);
  extern virtual function void print_value_object (ovm_object  value);
  extern virtual function void print_value_string (string      value);
  extern virtual function void print_value_array  (string      value="", 
                                        int         size=0);

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_tree_printer
//
// By overriding various methods of the <ovm_printer> super class,
// the tree printer prints output in a tree format.
//
// The following shows sample output from the tree printer.
//
//|  c1: (container@1013) {
//|    d1: (mydata@1022) {
//|         v1: 'hcb8f1c97
//|         e1: THREE
//|         str: hi
//|    }  
//|    value: 'h2d
//|  }
//
//------------------------------------------------------------------------------

class ovm_tree_printer extends ovm_printer;

  // Variable: new
  //
  // Creates a new instance of ~ovm_tree_printer~.

  extern function new(); 

  // Variable: knobs
  //
  // An instance of <ovm_tree_printer_knobs>, which govern the content
  // and format of the printed tree.

  ovm_tree_printer_knobs knobs = new;


  // Information to print at the opening/closing of a scope
  extern virtual function void print_scope_open   ();
  extern virtual function void print_scope_close  ();

  // Puts information in tree format
  extern virtual function void print_id           (string id,
                                        byte   scope_separator=".");
  extern virtual function void print_type_name    (string name, bit is_object=0);
  extern virtual function void print_object_header(string      name,
                                        ovm_object  value, 
                                        byte        scope_separator=".");
  extern virtual function void print_object       (string      name,
                                        ovm_object  value, 
                                        byte        scope_separator=".");
  extern virtual function void print_string       ( string      name,
                                        string      value, 
                                        byte        scope_separator=".");
  extern virtual function void print_value_object (ovm_object value);
  extern virtual function void print_value_array  (string      value="", 
                                        int         size=0);
  extern virtual function void print_array_footer (int         size=0);

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_line_printer
//
// The line printer prints output in a line format.
//
// The following shows sample output from the line printer.
//
//| c1: (container@1013) { d1: (mydata@1022) { v1: 'hcb8f1c97 e1: THREE str: hi } value: 'h2d } 
//------------------------------------------------------------------------------

class ovm_line_printer extends ovm_tree_printer;

  // Variable: new
  //
  // Creates a new instance of ~ovm_line_printer~.

  extern function new(); 

  // Function: print_newline
  //
  // Overrides <ovm_printer::print_newline> to not print a newline,
  // effectively making everything appear on a single line.

  extern virtual function void print_newline (bit do_global_indent=1);

endclass



//------------------------------------------------------------------------------
//
// CLASS: ovm_printer_knobs
//
// The ~ovm_printer_knobs~ class defines the printer settings available to all
// printer subtypes.  Printer subtypes may subtype this class to provide
// additional knobs for their specific format. For example, the
// <ovm_table_printer> uses the <ovm_table_printer_knobs>, which defines knobs
// for setting table column widths.
//
//------------------------------------------------------------------------------

class ovm_printer_knobs;

  // Variable: max_width
  //
  // The maximum with of a field. Any field that requires more characters will
  // be truncated.

  int max_width = 999;


  // Variable: truncation
  //
  // Specifies the character to use to indicate a field was truncated.

  string truncation = "+"; 


  // Variable: header
  //
  // Indicates whether the <print_header> function should be called when
  // printing an object.

  bit header = 1;


  // Variable: footer
  //
  // Indicates whether the <print_footer> function should be called when
  // printing an object. 

  bit footer = 1;


  // Variable: global_indent
  //
  // Specifies the number of spaces of indentation to add whenever a newline
  // is printed.

  int global_indent = 0;


  // Variable: full_name
  //
  // Indicates whether <print_id> should print the full name of an identifier
  // or just the leaf name. The line, table, and tree printers ignore this
  // bit and always print only the leaf name.

  bit full_name = 1;


  // Variable: identifier
  //
  // Indicates whether <print_id> should print the identifier. This is useful
  // in cases where you just want the values of an object, but no identifiers.

  bit identifier = 1;


  // Variable: depth
  //
  // Indicates how deep to recurse when printing objects. 
  // A depth of -1 means to print everything.

  int depth = -1;
  

  // Variable: reference
  //
  // Controls whether to print a unique reference ID for object handles.
  // The behavior of this knob is simulator-dependent.

  bit reference = 1;


  // Variable: type_name
  //
  // Controls whether to print a field's type name. 

  bit type_name = 1;


  // Variable: size
  //
  // Controls whether to print a field's size. 

  bit size = 1;


  // Variable: begin_elements
  //
  // Defines the number of elements at the head of a list to print.
  // Use -1 for no max.

  int begin_elements = 5;


  // Variable: end_elements
  //
  // This defines the number of elements at the end of a list that
  // should be printed.
  
  int end_elements = 5;


  // Variable: show_radix
  //
  // Indicates whether the radix string ('h, and so on) should be prepended to
  // an integral value when one is printed.

  bit show_radix = 1;


  // Variable: prefix
  //
  // Specifies the string prepended to each output line
  
  string prefix = ""; 


  // Variable: mcd
  //
  // This is a file descriptor, or multi-channel descriptor, that specifies
  // where the print output should be directed. 
  //
  // By default, the output goes to the standard output of the simulator.

  int mcd = OVM_STDOUT; 


  // Variable: default_radix
  //
  // This knob sets the default radix to use for integral values when no radix
  // enum is explicitly supplied to the print_field() method.

  ovm_radix_enum default_radix = OVM_HEX;

  
  // Variable: dec_radix
  //
  // This string should be prepended to the value of an integral type when a
  // radix of <OVM_DEC> is used for the radix of the integral object. 
  //
  // When a negative number is printed, the radix is not printed since only
  // signed decimal values can print as negative.

  string dec_radix = "'d";


  // Variable: bin_radix
  //
  // This string should be prepended to the value of an integral type when a
  // radix of <OVM_BIN> is used for the radix of the integral object.

  string bin_radix = "'b";


  // Variable: oct_radix
  //
  // This string should be prepended to the value of an integral type when a
  // radix of <OVM_OCT> is used for the radix of the integral object.

  string oct_radix = "'o";


  // Variable: unsigned_radix
  //
  // This is the string which should be prepended to the value of an integral
  // type when a radix of <OVM_UNSIGNED> is used for the radix of the integral
  // object. 

  string unsigned_radix = "'d";


  // Variable: hex_radix
  //
  // This string should be prepended to the value of an integral type when a
  // radix of <OVM_HEX> is used for the radix of the integral object.

  string hex_radix = "'h";


  // Function: get_radix_str
  //
  // Converts the radix from an enumerated to a printable radix according to
  // the radix printing knobs (bin_radix, and so on).

  extern function string get_radix_str (ovm_radix_enum radix);

  // For internal use

  int column = 0;
  bit sprint = 0; 
  bit print_fields = 1;

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_hier_printer_knobs
//
// The ~ovm_hier_printer_knobs~ is a simple container class that extends
// <ovm_printer::ovm_printer_knobs> with settings for printing information
// hierarchically.
//------------------------------------------------------------------------------

class ovm_hier_printer_knobs extends ovm_printer_knobs;

  // Variable: indent_str
  //
  // This knob specifies the string to use for level indentation. 
  // The default level indentation is two spaces.

  string indent_str = "  ";


  // Variable: show_root
  //
  // This setting indicates whether or not the initial object that is printed
  // (when current depth is 0) prints the full path name. By default, the first
  // object is treated like all other objects and only the leaf name is printed.

  bit show_root = 0;

  extern function new(); 

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_table_printer_knobs
//
// The ~ovm_table_printer_knobs~ is a simple container class that extends
// <ovm_printer::ovm_hier_printer_knobs> with settings specific to printing
// in table format.
//------------------------------------------------------------------------------

class ovm_table_printer_knobs extends ovm_hier_printer_knobs;

  // Variable: name_width
  //
  // Sets the width of the ~name~ column. If set to 0, the column is not printed.

  int name_width = 25;


  // Variable: type_width
  //
  // Sets the width of the ~type~ column. If set to 0, the column is not printed.

  int type_width = 20;


  // Variable: size_width
  //
  // Sets the width of the ~size~ column. If set to 0, the column is not printed.

  int size_width = 5;


  // Variable: value_width
  //
  // Sets the width of the ~value~ column. If set to 0, the column is not printed.

  int value_width = 20;

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_tree_printer_knobs
//
// The ~ovm_tree_printer_knobs~ is a simple container class that extends
// <ovm_printer::ovm_hier_printer_knobs> with settings specific to printing
// in tree format.
//------------------------------------------------------------------------------

class ovm_tree_printer_knobs extends ovm_hier_printer_knobs;

  // Variable: separator
  //
  // Determines the opening and closing separators used for
  // nested objects.

  string separator = "{}";

endclass


`endif // OVM_PRINTER_SVH


