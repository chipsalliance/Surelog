// $Id: //dvt/vtech/dev/main/ovm/src/compatibility/avm_compatibility.svh#18 $
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
`ifndef AVM_compatibility_SVH
`define AVM_compatibility_SVH

typedef ovm_object	       avm_transaction;
typedef ovm_env                avm_env;
typedef ovm_component          avm_threaded_component;
typedef ovm_component          avm_named_component;
typedef ovm_report_object      avm_report_client;
typedef ovm_report_handler     avm_report_handler;
typedef ovm_report_server      avm_report_server;
typedef ovm_reporter           avm_reporter;

typedef OVM_FILE FILE;

typedef enum
{
  MESSAGE,
  WARNING,
  ERROR,
  FATAL
} severity;

typedef bit [4:0] action;

typedef enum action
{
  NO_ACTION = 5'b00000,
  DISPLAY   = 5'b00001,
  LOG       = 5'b00010,
  COUNT     = 5'b00100,
  EXIT      = 5'b01000,
  CALL_HOOK = 5'b10000
} action_type;


// So that you can just change Avm_ to Ovm_
typedef ovm_component          ovm_named_component;
typedef ovm_report_object      ovm_report_client;

`ifndef INCA
`ifndef SVPP

`define avm_to_ovm_uni(kind) \
class avm_``kind``_port #(type T=int) extends ovm_``kind``_port #(T); \
function new( string name, ovm_component parent, int min_size = 1, int max_size = 1 ); \
      super.new( name, parent, min_size, max_size ); \
endfunction : new \
endclass \
class avm_``kind``_export #(type T=int) extends ovm_``kind``_export #(T); \
function new( string name, ovm_component parent, int min_size = 1, int max_size = 1 ); \
      super.new( name, parent, min_size, max_size ); \
endfunction : new \
endclass \
class avm_``kind``_imp #(type T=int,IMP=int) extends ovm_``kind``_imp #(T,IMP); \
function new( string name, IMP imp); \
      super.new( name, imp ); \
endfunction : new \
endclass \

`define avm_to_ovm_bidi(kind) \
class avm_``kind``_port #(type REQ=int,RSP=int) extends ovm_``kind``_port #(REQ,RSP); \
function new( string name, ovm_component parent, int min_size = 1, int max_size = 1 ); \
      super.new( name, parent, min_size, max_size ); \
endfunction : new \
endclass \
class avm_``kind``_export #(type REQ=int,RSP=int) extends ovm_``kind``_export #(REQ,RSP); \
function new( string name, ovm_component parent, int min_size = 1, int max_size = 1 ); \
      super.new( name, parent, min_size, max_size ); \
endfunction : new \
endclass \
class avm_``kind``_imp #( type REQ = int , type RSP = int ,\
				type IMP = int ,\
				type REQ_IMP = IMP ,\
				type RSP_IMP = IMP )\
  extends ovm_``kind``_imp #( REQ, RSP, IMP, REQ_IMP, RSP_IMP);\
   function new( string name , IMP imp ,\
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp );\
     super.new( name , imp , req_imp, rsp_imp);\
  endfunction \
endclass

`avm_to_ovm_uni(blocking_put)
`avm_to_ovm_uni(nonblocking_put)
`avm_to_ovm_uni(put)

`avm_to_ovm_uni(blocking_get)
`avm_to_ovm_uni(nonblocking_get)
`avm_to_ovm_uni(get)

`avm_to_ovm_uni(blocking_peek)
`avm_to_ovm_uni(nonblocking_peek)
`avm_to_ovm_uni(peek)

`avm_to_ovm_uni(blocking_get_peek)
`avm_to_ovm_uni(nonblocking_get_peek)
`avm_to_ovm_uni(get_peek)

`avm_to_ovm_bidi(blocking_master)
`avm_to_ovm_bidi(nonblocking_master)
`avm_to_ovm_bidi(master)

`avm_to_ovm_bidi(blocking_slave)
`avm_to_ovm_bidi(nonblocking_slave)
`avm_to_ovm_bidi(slave)

// Here we don't use the avm_to_ovm macro because we inherit
// avm_transport_* from ovm_blocking_transport_*.  AVM doesn't support
// nonblocking ad combined transport interface, only a blocking
// transport interface which is simply called "transport"

class avm_transport_port #(type REQ=int,RSP=int)
  extends ovm_blocking_transport_port #(REQ,RSP); 
  function new( string name, ovm_component parent,
                int min_size = 1, int max_size = 1 );
      super.new( name, parent, min_size, max_size );
  endfunction : new
endclass

class avm_transport_export #(type REQ=int,RSP=int)
  extends ovm_blocking_transport_export #(REQ,RSP);
  function new( string name, ovm_component parent,
                int min_size = 1, int max_size = 1 );
      super.new( name, parent, min_size, max_size );
  endfunction : new
endclass

`endif
`endif

`define avm_to_ovm_component(name) \
class avm_``name #(type T=int) extends ovm_``name#(T); \
function new(string name , ovm_component parent = null ); \
      super.new( name, parent ); \
endfunction : new \
endclass 

`define abstract_avm_to_ovm_component(name) \
virtual class avm_``name #(type T=int) extends ovm_``name#(T); \
function new(string name , ovm_component parent = null ); \
      super.new( name, parent ); \
endfunction : new \
endclass 


// TLM channels
`avm_to_ovm_component(analysis_port)
`avm_to_ovm_component(analysis_export)
`avm_to_ovm_component(random_stimulus)
`abstract_avm_to_ovm_component(subscriber)
//`avm_to_ovm_component(in_order_class_comparator)

// Policies
`define avm_to_ovm_policy(name) \
class avm_``name #(type T=int) extends ovm_``name#(T); \
endclass 

`avm_to_ovm_policy(built_in_comp)
`avm_to_ovm_policy(built_in_converter)
`avm_to_ovm_policy(built_in_clone)
`avm_to_ovm_policy(class_comp)
`avm_to_ovm_policy(class_converter)
`avm_to_ovm_policy(class_clone)

class avm_built_in_pair #( type T1 = int, type T2 = T1 )
  extends ovm_built_in_pair#(T1, T2);
  
  function new( input T1 f = null , input T2 s = null );
    super.new(f,s);
  endfunction  
endclass

class avm_class_pair #( type T1 = int, type T2 = T1 )
  extends ovm_class_pair#(T1,T2);

  function new( input T1 f = null , input T2 s = null );
	super.new(f,s);
  endfunction
endclass

class avm_in_order_comparator 
  #( type T = int ,
     type comp_type = avm_built_in_comp #( T ) ,
     type convert = avm_built_in_converter #( T ) , 
     type pair_type = avm_built_in_pair #( T ) )
  extends ovm_in_order_comparator#(T);

  function new(string name, avm_named_component parent);
    super.new(name, parent);
  endfunction
endclass

class avm_in_order_class_comparator #( type T = int )
  extends ovm_in_order_comparator #( T , 
                                     avm_class_comp #( T ) , 
                                     avm_class_converter #( T ) , 
                                     avm_class_pair #( T, T ) );
  function new( string name, avm_named_component parent);
    super.new( name, parent );
  endfunction
  
endclass : avm_in_order_class_comparator

class avm_in_order_built_in_comparator #( type T = int )
  extends ovm_in_order_comparator #( T );

  function new( string name ,
                ovm_component parent );
    super.new( name, parent );
  endfunction

endclass : avm_in_order_built_in_comparator

class avm_algorithmic_comparator #( type BEFORE = int ,
                                    type AFTER = int  ,
                                    type TRANSFORMER = int )
  extends ovm_algorithmic_comparator #(BEFORE,
                                       AFTER,
                                       TRANSFORMER);
   function new ( TRANSFORMER transformer ,
                string name ,
                ovm_component parent );
      super.new(transformer,name,parent);
   endfunction :  new
endclass : avm_algorithmic_comparator



// Provides a global reporter and a set of global reporting
// functions.  These can be use in modules or in any class
// not derived from avm_report_client.

//ovm_reporter _global_reporter = new();

function void avm_report_message(string id,
				 string message,
                                 int verbosity = 300,
				 string filename = "",
				 int line = 0);
  _global_reporter.ovm_report_info(id, message, verbosity, filename, line);
endfunction

function void avm_report_warning(string id,
                                 string message,
                                 int verbosity = 200,
				 string filename = "",
				 int line = 0);
  _global_reporter.ovm_report_warning(id, message, verbosity, filename, line);
endfunction

function void avm_report_error(string id,
                               string message,
                               int verbosity = 100,
			       string filename = "",
			       int line = 0);
  _global_reporter.ovm_report_error(id, message, verbosity, filename, line);
endfunction

function void avm_report_fatal(string id,
	                       string message,
                               int verbosity = 0,
			       string filename = "",
			       int line = 0);
  _global_reporter.ovm_report_fatal(id, message, verbosity, filename, line);
endfunction

class analysis_fifo #(type T = int)
  extends tlm_analysis_fifo #(T);
  function new (string name, ovm_component parent=null);
    super.new(name, parent);
  endfunction
endclass

class avm_transport_imp #(type REQ = int, type RSP = int, type IMP = int)
  extends ovm_blocking_transport_imp #(REQ, RSP, IMP);
  function new (string name, IMP imp);
    super.new(name, imp);
  endfunction
endclass // avm_transport_imp

class avm_analysis_imp #( type T = int , type IMP = int )
  extends ovm_analysis_imp #(T, IMP);
  function new( string name, IMP imp );
    super.new(name, imp);
  endfunction
endclass

virtual class avm_port_base #(type IF = ovm_object)
  extends ovm_port_base #(IF);

  function new( string name , ovm_component parent ,
        ovm_port_type_e port_type ,
        int min_size = 0 , int max_size = 1 );
    super.new(name, parent, port_type, min_size, max_size);
  endfunction
endclass


`endif

