//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

`ifndef VMM_DOSFILE_CHECK
`define VMM_DOSFILE_CHECK If you get a syntax error on this line, \
        the file is corrupt. Make sure you unpack the VMM distribution \
        file with gunzip then tar, not a Windows tool
`endif

//
// If you wish to use the parameterized classes version of vmm_channel
// (requires VCS 2008.03 or later), the symbol `VMM_PARAM_CHANNEL must
// be defined




//---------------------------------------------------------------------
// Enable temporary work-arounds for features not yet implemented,
// disable language features that may not be supported by other tools,
// or VCS-specific extensions
//

`ifdef VCS
//`define VCS2006_06   // Uncomment if using VCS 2006.06 (requires -SP2-9 or later)
//`define VCS2008_09   // Uncomment if using VCS 2008.09 (requires -4 or later)
//`define VCS2008_12   // Uncomment if using VCS 2008.12
`define VCS2009_06     // Uncomment if using VCS 2009.06

`define VMM_SOLVE_BEFORE_SIZE
`ifndef VMM_SOLVE_BEFORE_OPT
   `define VMM_SOLVE_BEFORE_OPT hard
`endif

`endif


`ifdef VCS2006_06
`define NO_STATIC_METHODS
`define NO_TYPED_AA_IDX
`define NO_STRING_CAST
`endif

`ifdef VCS2008_09
`define NO_STRING_CAST
`endif

`ifdef VCS2008_12
`define NO_STRING_CAST
`endif

// IUS work-arounds relating to foreach 
`ifdef INCA

`define foreach(var,idx) \
  for (int idx=0; idx<var.size(); ++idx)

`define foreach_str(var,idx) \
  for (int idx=0; idx<var.len(); ++idx)

`define foreach_sa(var,size,idx) \
    for(int idx=0; idx < size; ++idx)

`define foreach_aa(var,keytype,idx) \
  begin \
  keytype idx; \
  if (var.first(idx)) do

`define foreach_aa_end(var,idx) \
  while(var.next(idx)); end

`else // QUESTA

`define foreach(var,idx) \
  foreach (var[idx])

`define foreach_str(var,idx) \
  foreach (var[idx])

`define foreach_sa(var,size,idx) \
  foreach (var[idx])

`define foreach_aa(var,keytype,idx) \
  foreach (var[idx])

`define foreach_aa_end(var,idx) \
  /* */

`endif

// Workaround for IUS not allowing protected constructor
`ifdef INCA
  `define _protected
`else //Questa
  `define _protected protected
`endif


`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   `define vmm_delQ(_q) _q.delete()
`else
`ifdef INCA
   `define vmm_delQ(_q) _q.delete()
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   `define vmm_delQ(_q) _q = '{}
`endif
`endif

`ifndef vmm_vector_sformatf
`ifdef INCA
function bit [1027:0] vmm_string_to_vector(string str);
  $swrite(vmm_string_to_vector,"%s", str);
endfunction
`define vmm_vector_sformatf(A) vmm_string_to_vector($psprintf(A))
`else
`define vmm_vector_sformatf(A) $psprintf(A)
`endif
`endif



//---------------------------------------------------------------------
// Functionality that must be provided through DPI/System tasks
//

`ifndef VMM_DPI_
`define VMM_DPI_

//
// $sformatf()
//
// SV-2008 feature that may not be available. $sformat() could be used but
// with lower performance as formatted strings would be always created even
// if never used.
//
// VCS provides a precursor called $psprintf()
//
`ifndef vmm_sformatf
`define vmm_sformatf $psprintf
`endif

//
// String-matching pseudo methods.
//
// Those are built-in VCS and may eventually be part of a revision of the
// SV standard. In the meantime, they can be provided by DPI functions or
// their functionality be disabled. These DPIs are provided by the file
// $VMM_HOME/sv/std_lib/vmm_str_dpi.c
//
// Currently, they are used in vmm_log for name and instance name matching
// and in the XVCs for command parsing and interpretation.
//


`ifdef VCS
`define vmm_str_match(str, regex) str.match(regex)
`define vmm_str_prematch(str)     str.prematch()
`define vmm_str_postmatch(str)    str.postmatch()
`define vmm_str_backref(str, n)   str.backref(n)

`else

`endif


`endif // VMM_DPI_


//
// The macros must be defined in a separate guard block to enable
// separate compilation because `define symbols are compilation symbols,
// not SV symbols that end up in the VMM package
//

`ifndef VMM_MACRO_DEFINED
`define VMM_MACRO_DEFINED

`define VMM_MACRO_TO_STRING(x) `"x`"


//---------------------------------------------------------------------
// User customization macros
//


`ifdef VMM_PRE_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_PRE_INCLUDE)
`endif


`ifndef VMM_DATA
   `define VMM_DATA                 vmm_data
`endif
`ifndef VMM_DATA_NEW_ARGS
   `define VMM_DATA_NEW_ARGS
   `define VMM_DATA_NEW_EXTERN_ARGS
   `define VMM_DATA_NEW_CALL
`endif
`ifndef VMM_DATA_BASE_NEW_ARGS
   `define VMM_DATA_BASE_NEW_ARGS
   `define VMM_DATA_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_DATA_BASE
   `ifndef VMM_DATA_BASE_NEW_CALL
      `define VMM_DATA_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_DATA_BASE_METHODS
   `define VMM_DATA_BASE_METHODS
`endif

`ifndef VMM_SCENARIO
   `define VMM_SCENARIO                      vmm_scenario
`endif
`ifndef VMM_SCENARIO_NEW_ARGS
   `define VMM_SCENARIO_NEW_ARGS             `VMM_DATA_NEW_ARGS
   `define VMM_SCENARIO_NEW_EXTERN_ARGS      `VMM_DATA_NEW_EXTERN_ARGS
   `define VMM_SCENARIO_NEW_CALL             `VMM_DATA_NEW_CALL
`endif
`ifndef VMM_SCENARIO_BASE
   `define VMM_SCENARIO_BASE                 vmm_data
`endif
`ifndef VMM_SCENARIO_BASE_NEW_ARGS
   `define VMM_SCENARIO_BASE_NEW_ARGS        `VMM_DATA_NEW_ARGS
   `define VMM_SCENARIO_BASE_NEW_EXTERN_ARGS `VMM_DATA_NEW_EXTERN_ARGS
`endif
`ifndef VMM_SCENARIO_BASE_NEW_CALL
   `define VMM_SCENARIO_BASE_NEW_CALL        `VMM_DATA_NEW_CALL
`endif
`ifndef VMM_SCENARIO_BASE_METHODS
   `define VMM_SCENARIO_BASE_METHODS
`endif

`ifndef VMM_CHANNEL
   `define VMM_CHANNEL                vmm_channel
`endif
`ifdef VMM_CHANNEL_BASE
   `ifndef VMM_CHANNEL_BASE_NEW_CALL
      `define VMM_CHANNEL_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_CHANNEL_BASE_METHODS
   `define VMM_CHANNEL_BASE_METHODS
`endif

`ifndef VMM_CONSENSUS
   `define VMM_CONSENSUS                vmm_consensus
`endif
`ifdef VMM_CONSENSUS_BASE
   `ifndef VMM_CONSENSUS_BASE_NEW_CALL
      `define VMM_CONSENSUS_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_CONSENSUS_BASE_METHODS
   `define VMM_CONSENSUS_BASE_METHODS
`endif

`ifndef VMM_LOG
   `define VMM_LOG                 vmm_log
`endif
`ifdef VMM_LOG_BASE
   `ifndef VMM_LOG_BASE_NEW_CALL
      `define VMM_LOG_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_LOG_BASE_METHODS
   `define VMM_LOG_BASE_METHODS
`endif

`ifndef VMM_NOTIFY
   `define VMM_NOTIFY                 vmm_notify
`endif
`ifdef VMM_NOTIFY_BASE
   `ifndef VMM_NOTIFY_BASE_NEW_CALL
      `define VMM_NOTIFY_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_NOTIFY_BASE_METHODS
   `define VMM_NOTIFY_BASE_METHODS
`endif

`ifndef VMM_XACTOR
   `define VMM_XACTOR                 vmm_xactor
`endif
`ifndef VMM_XACTOR_NEW_ARGS
   `define VMM_XACTOR_NEW_ARGS
   `define VMM_XACTOR_NEW_EXTERN_ARGS
   `define VMM_XACTOR_NEW_CALL
`endif
`ifndef VMM_XACTOR_BASE_NEW_ARGS
   `define VMM_XACTOR_BASE_NEW_ARGS
   `define VMM_XACTOR_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_XACTOR_BASE
   `ifndef VMM_XACTOR_BASE_NEW_CALL
      `define VMM_XACTOR_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_XACTOR_BASE_METHODS
   `define VMM_XACTOR_BASE_METHODS
`endif

`ifndef VMM_SUBENV
   `define VMM_SUBENV                 vmm_subenv
`endif
`ifndef VMM_SUBENV_NEW_ARGS
   `define VMM_SUBENV_NEW_ARGS
   `define VMM_SUBENV_NEW_EXTERN_ARGS
   `define VMM_SUBENV_NEW_CALL
`endif
`ifndef VMM_SUBENV_BASE_NEW_ARGS
   `define VMM_SUBENV_BASE_NEW_ARGS
   `define VMM_SUBENV_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_SUBENV_BASE
   `ifndef VMM_SUBENV_BASE_NEW_CALL
      `define VMM_SUBENV_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_SUBENV_BASE_METHODS
   `define VMM_SUBENV_BASE_METHODS
`endif

// Define OVM_INTEROP to use any Accellera OVM-VMM Interoperability kit
// dated Jul 31, 2009 or earlier.
`ifdef OVM_INTEROP
`define VMM_OVM_INTEROP
`define VMM_LOG_FORMAT_FILE_LINE
`endif
`ifdef VMM_OVM_INTEROP
   `define VMM_PARAM_CHANNEL
   `ifndef AVT_VMM_OVM_ENV_BASE
      `define AVT_VMM_OVM_ENV_BASE vmm_env
   `endif
   `ifndef VMM_ENV
      `define VMM_ENV avt_vmm_ovm_env
   `endif
`endif

`ifndef VMM_ENV
   `define VMM_ENV                 vmm_env
`endif
`ifndef VMM_ENV_NEW_ARGS
   `define VMM_ENV_NEW_ARGS
   `define VMM_ENV_NEW_EXTERN_ARGS
   `define VMM_ENV_NEW_CALL
`endif
`ifndef VMM_ENV_BASE_NEW_ARGS
   `define VMM_ENV_BASE_NEW_ARGS
   `define VMM_ENV_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_ENV_BASE
   `ifndef VMM_ENV_BASE_NEW_CALL
      `define VMM_ENV_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_ENV_BASE_METHODS
   `define VMM_ENV_BASE_METHODS
`endif



//---------------------------------------------------------------------
// vmm_log ease-of-use macros
//
`ifdef VMM_LOG_FORMAT_FILE_LINE
   `ifndef __FILE__
   `define __FILE__ `"`"
   `endif
   `ifndef __LINE__
   `define __LINE__ -1
   `endif
`endif

`ifdef VMM_LOG_FORMAT_FILE_LINE
	`define vmm_warning(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while(0)

	`define vmm_error(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_fatal(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)
`else
	`define vmm_warning(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while(0)

	`define vmm_error(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_fatal(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)
`endif
//
// If it is necessary to compile-out debug messages to gain every
// milligram of performance, defining this macro will take them out.
//

`ifdef VMM_NULL_LOG_MACROS

`define vmm_trace(log, msg)
`define vmm_debug(log, msg)
`define vmm_verbose(log, msg)
`define vmm_note(log, msg)
`define vmm_report(log, msg)
`define vmm_command(log, msg)
`define vmm_protocol(log, msg)
`define vmm_transaction(log, msg)
`define vmm_cycle(log, msg)
`define vmm_user(n, log, msg)

`else

`ifdef VMM_LOG_FORMAT_FILE_LINE
	`define vmm_trace(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_debug(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_verbose(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV, `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_note(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::NOTE_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_report(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::REPORT_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_command(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::COMMAND_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_protocol(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::PROTOCOL_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_transaction(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::TRANSACTION_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_cycle(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::CYCLE_TYP, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_user(n, log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::USER_TYP_``n, , `__FILE__, `__LINE__)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)
`else
	`define vmm_trace(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_debug(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_verbose(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_note(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::NOTE_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_report(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::REPORT_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_command(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::COMMAND_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_protocol(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::PROTOCOL_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_transaction(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::TRANSACTION_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_cycle(log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::CYCLE_TYP)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)

	`define vmm_user(n, log, msg)  \
	do \
	   /* synopsys translate_off */ \
	   if (log.start_msg(vmm_log::USER_TYP_``n)) begin \
	      void'(log.text(msg)); \
	      log.end_msg(); \
	   end \
	   /* synopsys translate_on */ \
	while (0)
`endif

`endif



//---------------------------------------------------------------------
// Transactor callback and iterator ease-of-invocation macros
//

`define vmm_callback(facade, call) \
 \
do `foreach (this.callbacks,vmm_i) begin \
   facade cb; \
   if ($cast(cb, this.callbacks[vmm_i])) \
     cb.call; \
end while (0)


`define foreach_vmm_xactor(xactor, name, inst) \
   xactor xact; \
   vmm_xactor_iter xactor_iter = new(name, inst); \
   for (vmm_xactor _xact = xactor_iter.first(); \
        _xact != null; \
        _xact = xactor_iter.next()) \
     if ($cast(xact, _xact))


//---------------------------------------------------------------------
// Other macros
//

`ifndef VMM_OBJECT_SET_PARENT
   `define VMM_OBJECT_SET_PARENT(_child, _parent)
`endif

`include "std_lib/vmm_data_macros.sv"
`include "std_lib/vmm_scenario_macros.sv"
`include "std_lib/vmm_xactor_macros.sv"
`include "std_lib/vmm_subenv_macros.sv"
`include "std_lib/vmm_env_macros.sv"


`ifdef VMM_PARAM_CHANNEL

`define vmm_channel(T) typedef vmm_channel_typed#(T) T``_channel;

`else

`define vmm_channel_(T) T``_channel

`define vmm_channel(T) \
class `vmm_channel_(T) extends vmm_channel; \
 \
   function new(string name, \
                string inst, \
                int    full = 1, \
                int    empty = 0, \
                bit    fill_as_bytes = 0); \
      super.new(name, inst, full, empty, fill_as_bytes); \
   endfunction: new \
 \
   function T unput(int offset = -1); \
      $cast(unput, super.unput(offset)); \
   endfunction: unput \
 \
   task get(output T obj, input int offset = 0); \
      vmm_data o; \
      super.get(o, offset); \
      $cast(obj, o); \
   endtask: get \
 \
   task peek(output T obj, input int offset = 0); \
      vmm_data o; \
      super.peek(o, offset); \
      $cast(obj, o); \
   endtask: peek \
 \
   function T try_peek(int offset = 0); \
      vmm_data o; \
      o = super.try_peek(offset); \
      $cast(try_peek, o); \
   endfunction: try_peek \
 \
   task activate(output T obj, input int offset = 0); \
      vmm_data o; \
      super.activate(o, offset); \
      $cast(obj, o); \
   endtask: activate \
 \
   function T active_slot(); \
      $cast(active_slot, super.active_slot()); \
   endfunction: active_slot \
 \
   function T start(); \
      $cast(start, super.start()); \
   endfunction: start \
 \
   function T complete(vmm_data status = null); \
      $cast(complete, super.complete(status)); \
   endfunction: complete \
 \
   function T remove(); \
      $cast(remove, super.remove()); \
   endfunction: remove \
 \
   task tee(output T obj); \
      vmm_data o; \
      super.tee(o); \
      $cast(obj, o); \
   endtask: tee \
 \
   function T for_each(bit reset = 0); \
      $cast(for_each, super.for_each(reset)); \
   endfunction: for_each \
 \
endclass

`endif

`include "std_lib/vmm_atomic_gen.sv"

`ifndef VMM_SOLVE_BEFORE_OPT
   `define VMM_SOLVE_BEFORE_OPT
`endif
`include "std_lib/vmm_scenario_gen.sv"






//-------------------------------------------------------
// vmm_test shorthand macros
//

`define vmm_test_begin(testclassname, envclassname, doc) \
  class testclassname extends vmm_test; \
    envclassname env; \
    function new(); \
      super.new(`"testclassname`", doc); \
    endfunction \
    static testclassname testclassname``_inst = new(); \
    task run(vmm_env e); \
      $cast(env, e); \
      begin
     
`define vmm_test_end(testclassname) \
      end \
    endtask \
  endclass


//---------------------------------------------------------------------
// Work-arounds
//

`define NO_STATIC_METHODS 

`ifdef NO_STATIC_METHODS
   `define VMM_STATIC_M
`else
   `define VMM_STATIC_M static
`endif

`ifdef NO_TYPED_AA_IDX
   `define VMM_AA_INT *
`else
   `define VMM_AA_INT int
`endif


`endif // VMM_MACRO_DEFINED


//
// Detect improper definition of VMM_SB_DS_IN_STDLIB
// and cause a syntax error that will provide a clue
// about the actual cause of the problem
//
`ifdef VMM__SV
   `ifdef VMM_SB_DS_IN_STDLIB
      `ifndef VMM_SB_DS_IN_STDLIB_OK
         USAGE ERROR ERROR__Symbol_VMM_SB_DS_IN_STDLIB_defined_after_first_parsing_of_vmm_sv__Use_plus_define_plus_VMM_SB_DS_IN_STDLIB_command_line_option
      `endif
   `endif
`else
   `ifdef VMM_SB_DS_IN_STDLIB
      `define VMM_SB_DS_IN_STDLIB_OK
   `endif
`endif

//
// Protect against multiple inclusion of this file
//
`ifndef VMM__SV
`define VMM__SV
`define VMM_BEING_PARSED


`ifdef VMM_IN_PACKAGE


`ifdef VCS
(* _vcs_vmm_pkg = 1 *)
`endif
package vmm_std_lib;
`endif

`ifdef VMM_NO_STR_DPI

`define vmm_str_match(str, regex) 0
`define vmm_str_prematch(str)     `"`"
`define vmm_str_postmatch(str)    `"`"
`define vmm_str_backref(str, n)   `"`"

`else

import "DPI-C" function int vmm_str_match(input string str1, input string regex);
import "DPI-C" function string vmm_str_prematch();
import "DPI-C" function string vmm_str_postmatch();
import "DPI-C" function string vmm_str_backref(int n);

`define vmm_str_match(str, regex) vmm_str_match(str, regex)
`define vmm_str_prematch(str)     vmm_str_prematch()
`define vmm_str_postmatch(str)    vmm_str_postmatch()
`define vmm_str_backref(str, n)   vmm_str_backref(n+1)

`endif


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif

`include "std_lib/vmm_version.sv"

//---------------------------------------------------------------------
// Forward declarations
//

typedef class vmm_opts;
typedef class vmm_opts_info;
typedef class vmm_log;
typedef class vmm_data;
typedef class vmm_scenario;
typedef class vmm_channel;
typedef class vmm_xactor;
typedef class vmm_notify;
typedef class vmm_consensus;
typedef class vmm_voter;
typedef class vmm_subenv;
typedef class vmm_env;
typedef class vmm_test;
typedef class vmm_test_registry;


typedef class `VMM_DATA;
`ifdef VMM_DATA_BASE
typedef class `VMM_DATA_BASE;
`endif
`ifdef VMM_CHANNEL_BASE
typedef class `VMM_CHANNEL_BASE;
`endif
`ifdef VMM_CONSENSUS_BASE
typedef class `VMM_CONSENSUS_BASE;
`endif
`ifdef VMM_LOG_BASE
typedef class `VMM_LOG_BASE;
`endif
`ifdef VMM_NOTIFY_BASE
typedef class `VMM_NOTIFY_BASE;
`endif
typedef class `VMM_XACTOR;
`ifdef VMM_XACTOR_BASE
typedef class `VMM_XACTOR_BASE;
`endif
typedef class `VMM_SUBENV;
`ifdef VMM_SUBENV_BASE
typedef class `VMM_SUBENV_BASE;
`endif
`ifdef VMM_ENV_BASE
typedef class `VMM_ENV_BASE;
`endif


`ifdef VMM_POST_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_POST_INCLUDE)
`endif


//---------------------------------------------------------------------
// vmm_opts
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_opts;
   static local vmm_opts_info opts_info[string];
   static local bit           opts_extracted;
   static       vmm_log       log;
 
   extern `VMM_STATIC_M function bit    get_bit(string name,
                                                string doc = "");

   extern `VMM_STATIC_M function string get_string(string name,
                                                   string dflt = "",
                                                   string doc  = "");
   extern `VMM_STATIC_M function int    get_int(string  name,
                                                int     dflt = 0,
                                                string  doc  = "");

   extern `VMM_STATIC_M function void get_help();

   extern `VMM_STATIC_M local function bit extract_opts_info();

   extern `VMM_STATIC_M local function void add_specified_option(string frmt,
                                                                 string fname = "Command Line");

   extern `VMM_STATIC_M local function void parse_opts_file(string filename);

   extern `VMM_STATIC_M local function vmm_opts_info get_opts_by_name(string name);

   extern `VMM_STATIC_M local function bit split(string line,
                                                 output string argv[$]);
endclass


//---------------------------------------------------------------------
// vmm_log
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_log_format;
   extern virtual function string format_msg(string name,
                                             string inst,
                                             string msg_typ,
                                             string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                             string fname,
                                             int    line,
`endif
                                             ref string lines[$]);

   extern virtual function string continue_msg(string name,
                                               string inst,
                                               string msg_typ,
                                               string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                               string fname,
                                               int    line,
`endif
                                               ref string lines[$]);

   extern virtual function string abort_on_error(int count,
                                                 int limit);

   extern virtual function string pass_or_fail(bit    pass,
                                               string name,
                                               string inst,
                                               int    fatals,
                                               int    errors,
                                               int    warnings,
                                               int    dem_errs,
                                               int    dem_warns);
endclass: vmm_log_format


`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_callbacks;
   virtual function void pre_finish(vmm_log log,
                                    ref bit finished);
   endfunction

   virtual function void pre_abort(vmm_log log);
   endfunction

   virtual function void pre_stop(vmm_log log);
   endfunction

   virtual function void pre_debug(vmm_log log);
   endfunction
endclass: vmm_log_callbacks


typedef class vmm_log_below_iter;
typedef class vmm_log_msg;
typedef class vmm_log_modifier;
typedef class vmm_log_watchpoint;
typedef class vmm_log_catcher_descr;


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_log_catcher;
    /*local*/ bit issued = 0; //set to 1 if issue function is called
    /*local*/ bit thrown = 0 ; //set to 1 if throw function is called

    virtual function  void caught(vmm_log_msg msg);
        this.throw(msg);
    endfunction
    extern virtual protected function void throw(vmm_log_msg msg);
    extern virtual protected function void issue(vmm_log_msg msg);

endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_log
`ifdef VMM_LOG_BASE
   extends `VMM_LOG_BASE
`endif
;

   //
   // Symbolic constants shared by different contexts
   //
   typedef enum int {DEFAULT
                     = -1
                     , UNCHANGED
                     = -2
                     } symbols_e;

   //
   // Symbolic constants for message types
   //
   typedef enum int {FAILURE_TYP     = 'h0001,
                     NOTE_TYP        = 'h0002,
                     DEBUG_TYP       = 'h0004,
                     REPORT_TYP      = 'h0008,
                     NOTIFY_TYP      = 'h0010,
                     TIMING_TYP      = 'h0020,
                     XHANDLING_TYP   = 'h0040,
                     PROTOCOL_TYP    = 'h0080,
                     TRANSACTION_TYP = 'h0100,
                     COMMAND_TYP     = 'h0200,
                     CYCLE_TYP       = 'h0400,
                     USER_TYP_0      = 'h0800,
                     USER_TYP_1      = 'h1000,
                     USER_TYP_2      = 'h2000,
                     INTERNAL_TYP    = 'h4000,
                     DEFAULT_TYP     = -1,
                     ALL_TYPS        = 'hFFFF
                     } types_e;

   //
   // Symbolic values for message severity
   //
   typedef enum int {FATAL_SEV   = 'h0001,
                     ERROR_SEV   = 'h0002,
                     WARNING_SEV = 'h0004,
                     NORMAL_SEV  = 'h0008,
                     TRACE_SEV   = 'h0010,
                     DEBUG_SEV   = 'h0020,
                     VERBOSE_SEV = 'h0040,
                     HIDDEN_SEV  = 'h0080,
                     IGNORE_SEV  = 'h0100,
                     DEFAULT_SEV = -1,
                     ALL_SEVS    = 'hFFFF
                     } severities_e;

   //
   // Symbolic values for simulation handling
   //
   typedef enum int {CONTINUE         = 'h0001,
                     COUNT_ERROR      = 'h0002,
                     DEBUGGER         = 'h0004,
                     DUMP_STACK       = 'h0008,
                     STOP_PROMPT      = 'h0010,
                     ABORT_SIM        = 'h0020,
                     IGNORE           = 'h0040,
                     DEFAULT_HANDLING = -1
                     } handling_e;

   //
   // Pre-defined STDOUT in case the simulator does not already define it
   //
   typedef enum int {STDOUT = 32'h8000_0001} stdout_e;

   //
   // Global control parameters
   //
   static local int    error_count = 0;     // Stop when # of errs
   static local int    error_limit = 10;    // Stop when # of errs
   static local string msg_format[$];
   static local string prefix;

   //vmm log catcher data
   static local vmm_log_catcher_descr catcher_cache[`VMM_AA_INT];
          local int catcher_ids[$];
   static local bit in_catcher = 0;

   //
   // Local control parameters
   //
   static local int dflt_lvl  = NORMAL_SEV; // Default verbosity level
   static local int force_lvl = DEFAULT_SEV; // Forced (global) verbosity level
   static local bit plus_debug;     // +vmm_log_debug was specified!

   local string  name;            // Name for this object
   local string  inst;            // Instance name for this object
   local string  orig_inst;       // Original instance name for this object

   extern function bit uses_hier_inst_name();
   extern function void use_hier_inst_name();
   extern function void use_orig_inst_name();
   local static bit     is_orig = 1;      // Which one is being used?
   local int unsigned parent_count;
   extern local function void make_hier_inst_name(string prefix = "");

   local int n_msg[`VMM_AA_INT];            // # of messages, per severities
   local int n_demoted[`VMM_AA_INT];        // # of demoted messages

   //
   // Partial message
   //
   local vmm_log_msg msg;
   local string  msg_txt[$];

   static local int    type_list[$];
   static local string type_images[`VMM_AA_INT];

   static local int    sev_list[$];
   static local string sev_images[`VMM_AA_INT];

   static local vmm_log_modifier modifier_cache[`VMM_AA_INT];
          local int modifier_ids[$];
          local int has_text_modifiers;

   static local vmm_log_watchpoint watchpoint_cache[`VMM_AA_INT];
          local int watchpoint_ids[$];

          local int enabled_typs;  // Filter if type not enableds
          local int log_lvl;       // Filter trace messages > log_lvl

   //
   // Callbacks are global to all instances
   //
   static local vmm_log_format fmt = new;
   static local int in_callbacks = 0;
   static local vmm_log_callbacks callbacks[$];

   //
   // File logging
   //
   local int fp[$];

   //
   // Iterator
   //
   local int             is_self;  // Trivial iterator?
   local bit             is_all;   // Trivial iterator?
   static local vmm_log  known[$]; // List of known logs

      /*local*/ vmm_log  below[$]; // Known logs below this one
   static local int      recurse_id = 0;
          local int      visited    = 0;

   static local string pattern[2];
   static local bit    is_pattern[2];
   static local int    known_idx = 0;
   static local int    recurse;
   static local vmm_log_below_iter recurse_stack[$];

   static vmm_opts _vmm_opts = new;

`ifdef VMM_LOG_BASE_METHODS
   `VMM_LOG_BASE_METHODS
`endif

   extern function new(string name,
                       string inst,
                       vmm_log under = null);

   extern virtual function void is_above(vmm_log log);
   extern virtual function void is_not_above(vmm_log log);
   extern virtual function vmm_log copy(vmm_log to = null);

   extern virtual function void set_name(string name);
   extern virtual function string get_name();
   extern virtual function void set_instance(string inst);
   extern virtual function string get_instance();

   extern function void reset(string name    = "/./",
                              string inst    = "/./",
                              bit    recurse = 0);
   extern function vmm_log for_each();
   extern virtual function void list(string name     = "/./",
                                     string inst     = "/./",
                                     bit    recurse  = 0);

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function void kill();

   //
   // Formatting
   //
   extern virtual function vmm_log_format set_format(vmm_log_format fmt);
   extern virtual function string set_typ_image(int typ, string  image);
   extern virtual function string set_sev_image(int severity, string  image);

   extern /*local*/ function string typ_image(int typ);
   extern /*local*/ function string sev_image(int severity);
   extern /*local*/ function string handling_image(int handling);
   extern local function int default_handling(int severity);

   extern virtual function void report(string name     = "/./",
                                       string inst     = "/./",
                                       bit    recurse  = 0);


   //
   // Issue messages
   //
   extern virtual function bit start_msg(int typ,
                                         int severity = DEFAULT_SEV
`ifdef VMM_LOG_FORMAT_FILE_LINE 
                                         , string fname = ""
                                         , int    line  = -1
`endif
                                         );

   extern virtual function bit text(string msg = "");
   extern virtual function void end_msg();
   extern local function void flush_msg();

   //
   // Message management
   //
   extern virtual function void enable_types(int     typs,
                                             string  name      = "",
                                             string  inst      = "",
                                             bit     recursive = 0);
   extern virtual function void disable_types(int     typs,
                                              string  name      = "",
                                              string  inst      = "",
                                              bit     recursive = 0);
   extern virtual function int modify(string name         = "",
                                      string inst         = "",
                                      bit    recursive    = 0,
                                      int    typ          = ALL_TYPS,
                                      int    severity     = ALL_SEVS,
                                      string text         = "",
                                      int    new_typ      = UNCHANGED,
                                      int    new_severity = UNCHANGED,
                                      int    handling     = UNCHANGED);
   extern virtual function void unmodify(int    modification_id = -1,
                                         string name            = "",
                                         string inst            = "",
                                         bit    recursive       = 0);

   extern local function void promote();
   extern local function void filter();
   extern local function void notify();

   extern virtual function void set_verbosity(int    severity,
                                              string name      = "",
                                              string inst      = "",
                                              bit    recursive = 0);
   extern function int get_verbosity();

   //
   // File logging
   //
   extern virtual function void log_start(int    file,
                                          string name    = "",
                                          string inst    = "",
                                          bit    recurse = 0);
   extern virtual function void log_stop(int    file,
                                         string name    = "",
                                         string inst    = "",
                                         bit    recurse = 0);


   //
   // Manage error counts
   //
   extern virtual function void stop_after_n_errors(int n);
   extern virtual function int get_message_count(int    severity = ALL_SEVS,
                                                 string name     = "",
                                                 string inst     = "",
                                                 bit    recurse  = 0);

   //
   // Synchronize with messages
   //
   extern virtual task wait_for_msg(string name     = "",
                                    string inst     = "",
                                    bit    recurse  = 0,
                                    int    typs     = ALL_TYPS,
                                    int    severity = ALL_SEVS,
                                    string text     = "",
                                    logic  issued   = 1'bx,
                                    ref vmm_log_msg msg);

   extern virtual function int create_watchpoint(int    typs     = ALL_TYPS,
                                                 int    severity = ALL_SEVS,
                                                 string text     = "",
                                                 logic  issued   = 1'bx);
   extern virtual function void add_watchpoint(int    watchpoint_id,
                                               string name            = "",
                                               string inst            = "",
                                               bit    recurse         = 0);
   extern virtual function void remove_watchpoint(int    watchpoint_id = -1,
                                                  string name          = "",
                                                  string inst          = "",
                                                  bit    recurse       = 0);
   extern virtual task wait_for_watchpoint(int             watchpoint_id,
                                           ref vmm_log_msg msg);

   extern local function void process_catch(vmm_log_msg msg);
   extern function int catch(vmm_log_catcher catcher,
			     string name = "",
			     string inst = "",
			     bit    recurse = 0,
			     int    typs = ALL_TYPS,
			     int    severity = ALL_SEVS,
			     string text = "");
   extern function bit uncatch(int catcher_id);
   extern function void uncatch_all();

   //
   // Callback Management
   //
   extern virtual function void prepend_callback(vmm_log_callbacks cb);
   extern virtual function void append_callback(vmm_log_callbacks cb);
   extern virtual function void unregister_callback(vmm_log_callbacks cb);




endclass: vmm_log


`ifdef VMM_SB_DS_IN_STDLIB
`include "sb/vmm_sb.sv"
(* _vcs_vmm_class = 1 *)
class vmm_sb_ds_registration;
   vmm_sb_ds             sb;
   bit                   is_in;
   bit                   is_out;
   vmm_sb_ds::ordering_e order;
endclass
`endif


//---------------------------------------------------------------------
// vmm_notify
//

`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_notify_callbacks;
   virtual function void indicated(vmm_data status);
   endfunction
endclass

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
virtual class vmm_notification;


   virtual task indicate(ref vmm_data status);
      $write("FATAL: An instance of vmm_notification::indicate() was not overloaded or super.indicate() was called\n");
      $finish;
   endtask

   virtual task reset();
      $write("FATAL: An instance of vmm_notification::reset() was not overloaded or super.reset() was called\n");
      $finish;
   endtask

endclass


typedef class vmm_notification_config;


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_notify
`ifdef VMM_NOTIFY_BASE
   extends `VMM_NOTIFY_BASE
`endif
;
   `VMM_LOG log;

   typedef enum int {ONE_SHOT = 2,
                     BLAST    = 3,
                     ON_OFF   = 5
                     } sync_e;

   typedef enum bit {SOFT,
                     HARD} reset_e;


   local int last_notification_id = 1000000;
   local vmm_notification_config configs[`VMM_AA_INT];

   extern function new(`VMM_LOG log);

`ifdef VMM_NOTIFY_BASE_METHODS
   `VMM_NOTIFY_BASE_METHODS
`endif

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function vmm_notify copy(vmm_notify to = null);
   extern virtual function int configure(int notification_id = -1,
        			         sync_e sync = ONE_SHOT);
   extern virtual function int is_configured(int notification_id);

   extern virtual function bit is_on(int notification_id);

   extern virtual task wait_for(int notification_id);
   extern virtual task wait_for_off(int notification_id);

   extern virtual function bit is_waited_for(int notification_id);
   extern virtual function void terminated(int notification_id);

   extern virtual function vmm_data status(int notification_id);
   extern virtual function time timestamp(int notification_id);
   extern virtual function void indicate(int notification_id,
	            		         vmm_data status = null);

   extern virtual function void set_notification(int          notification_id,
    				                 vmm_notification ntfy = null);
   extern virtual function vmm_notification get_notification(int notification_id);
   extern virtual function void reset(int     notification_id = -1,
                                      reset_e rst_typ         = SOFT);

   extern function void append_callback(int                  notification_id,
                                        vmm_notify_callbacks cbs);
   extern function void unregister_callback(int                  notification_id,
                                            vmm_notify_callbacks cbs);




`ifdef VMM_SB_DS_IN_STDLIB
   extern function void register_vmm_sb_ds(int                   notification_id,
                                           vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(int       notification_id,
                                             vmm_sb_ds sb);
`endif

endclass


//---------------------------------------------------------------------
// vmm_data
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_data
`ifdef VMM_DATA_BASE
   extends `VMM_DATA_BASE
`endif
;

   int stream_id;
   int scenario_id;
   int data_id;

   `VMM_NOTIFY notify;
   typedef enum int {EXECUTE = 999_999,
                     STARTED = 999_998,
                     ENDED = 999_997
                     } notifications_e;

   extern function new(`VMM_LOG log = null
                       `VMM_DATA_BASE_NEW_ARGS);

`ifdef VMM_DATA_BASE_METHODS
   `VMM_DATA_BASE_METHODS
`endif

   extern function vmm_log set_log(`VMM_LOG log);

   extern local virtual function string this_class_name();
   extern local virtual function vmm_log get_vmm_log();

   extern function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);
   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);
   extern virtual protected function void copy_data(vmm_data to);

   extern virtual function bit compare(       vmm_data to,
                                       output string   diff,
                                       input  int      kind = -1);

   extern virtual function int unsigned byte_size(int kind = -1);
   extern virtual function int unsigned max_byte_size(int kind = -1);
   extern virtual function int unsigned byte_pack(ref   logic [7:0]  bytes[],
                                                  input int unsigned offset = 0,
                                                  input int          kind   = -1);
   extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                    input int unsigned    offset = 0,
                                                    input int             len    = -1,
                                                    input int             kind   = -1);
   extern virtual function bit load(int file);
   extern virtual function void save(int file);

   //
   // Methods and members to support the short-hand macros
   //
   protected static string       __vmm_prefix;
   protected static string       __vmm_image;
   protected static vmm_data     __vmm_rhs;
   protected static int          __vmm_kind;
   protected static int          __vmm_offset;
   protected static int          __vmm_len;
   protected static bit [4095:0] __vmm_maxbits;
   protected static bit          __vmm_status;
   protected static logic  [7:0] __vmm_bytes[];
   protected static bit          __vmm_done_user;
   extern virtual protected function int unsigned __vmm_byte_size(int kind = -1);

   typedef enum {DO_PRINT   ='h001,
                 DO_COPY    ='h002,
                 DO_COMPARE ='h004,
                 DO_PACK    ='h010,
                 DO_UNPACK  ='h020,
		 DO_ALL     ='hFFF} do_what_e;

   typedef enum {DO_NOCOPY      ='h001,
                 DO_REFCOPY     ='h002,
                 DO_DEEPCOPY    ='h004,
                 HOW_TO_COPY    ='h007, // OR of all DO_*COPY
                 DO_NOCOMPARE   ='h008,
                 DO_REFCOMPARE  ='h010,
                 DO_DEEPCOMPARE ='h020,
                 HOW_TO_COMPARE ='h038, // OR of all DO_*COMPARE
                 DO_NONE        ='h009, // OR of all DO_NO*
                 DO_REF         ='h012, // OR of all DO_REF*
                 DO_DEEP        ='h024, // OR of all DO_DEEP*
                 _DO_DUMMY} do_how_e;

   function void do_all(          do_what_e   what,
                              ref logic [7:0] pack[],
                        const ref logic [7:0] unpack[]);
   endfunction

   extern virtual function string do_psdisplay(string prefix = "");

   extern virtual function bit do_is_valid(bit silent = 1,
                                           int kind   = -1);
   extern virtual function vmm_data do_allocate();
   extern virtual function vmm_data do_copy(vmm_data to = null);

   extern virtual function bit do_compare(       vmm_data to,
                                          output string   diff,
                                          input  int      kind = -1);

   extern virtual function int unsigned do_byte_size(int kind = -1);
   extern virtual function int unsigned do_max_byte_size(int kind = -1);
   extern virtual function int unsigned do_byte_pack(ref   logic [7:0]  bytes[],
                                                     input int unsigned offset = 0,
                                                     input int          kind   = -1);
   extern virtual function int unsigned do_byte_unpack(const ref logic [7:0] bytes[],
                                                       input int unsigned    offset = 0,
                                                       input int             len    = -1,
                                                       input int             kind   = -1);


`ifdef VCS
   extern function int vmt_hook(vmm_xactor xactor = null,
			        vmm_data   obj    = null);


`endif
endclass: vmm_data


//---------------------------------------------------------------------
// vmm_scenario
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scenario extends `VMM_SCENARIO_BASE;

   local int    next_scenario_kind;
   local int    max_length;
   local string scenario_names[`VMM_AA_INT];
   local vmm_scenario parent;

   rand int unsigned scenario_kind;
   rand int unsigned length;
   rand int unsigned  repeated;
   static int unsigned repeat_thresh = 100;

   constraint vmm_scenario_valid {
      scenario_kind >= 0;
      scenario_kind < ((next_scenario_kind == 0) ? 1 : next_scenario_kind);

      length >= 0;
      length <= max_length;

      repeated >= 0;

      solve scenario_kind before length `VMM_SOLVE_BEFORE_OPT;
   }

   constraint repetition {
      repeated == 0;
   }

   extern function new(`VMM_SCENARIO parent = null
                       `VMM_SCENARIO_NEW_ARGS);

`ifdef VMM_SCENARIO_BASE_METHODS
   `VMM_SCENARIO_BASE_METHODS
`endif

   extern local virtual function string this_class_name();
   extern local virtual function vmm_log get_vmm_log();

   extern virtual function string psdisplay(string prefix = "");

   extern function int unsigned define_scenario(string name,
                                                int unsigned max_len = 0);
   extern function void redefine_scenario(int unsigned scenario_kind,
                                          string       name,
                                          int unsigned max_len = 0);
   extern function string scenario_name(int unsigned scenario_kind = 0);
   extern local virtual function string __default_name();

   extern protected function int unsigned get_max_length();

   extern function void set_parent_scenario(vmm_scenario parent);
   extern function vmm_scenario get_parent_scenario();

   extern virtual function vmm_data copy(vmm_data to = null);
endclass: vmm_scenario


//---------------------------------------------------------------------
// vmm_ms_scenario
//
typedef class vmm_ms_scenario_gen;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario extends `VMM_SCENARIO;
    static `VMM_LOG log = new("vmm_ms_scenario", "class");
    local vmm_ms_scenario_gen context_scenario_gen;

    extern function new(`VMM_SCENARIO parent = null
                        `VMM_SCENARIO_NEW_ARGS);
    extern local virtual function string this_class_name();
    extern local virtual function string __default_name();
    extern local virtual function vmm_log get_vmm_log();

    extern virtual task execute(ref int n);

    /*local*/ extern virtual function void Xset_context_genX(vmm_ms_scenario_gen gen);
    extern virtual function vmm_ms_scenario_gen get_context_gen();

    extern virtual function string psdisplay(string prefix = "");
    extern virtual function vmm_ms_scenario get_ms_scenario(string scenario,
                                                            string gen = "");
    extern virtual function vmm_channel get_channel(string name);
    extern virtual task grab_channels(ref vmm_channel channels[$]);

    extern virtual function vmm_data copy(vmm_data to = null);
endclass: vmm_ms_scenario


//---------------------------------------------------------------------
// vmm_ms_scenario_election
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_election;
    int stream_id;
    int scenario_id;
    int unsigned n_scenarios;
    int unsigned last_selected[$];
    int unsigned next_in_set;

    vmm_ms_scenario scenario_set[$];
    rand int select;

    constraint vmm_ms_scenario_election_valid {
        select >= 0;
        select < n_scenarios;
    }

    constraint round_robin {
        select == next_in_set;
    }
endclass: vmm_ms_scenario_election


//---------------------------------------------------------------------
// vmm_channel
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_channel
`ifdef VMM_CHANNEL_BASE
   extends `VMM_CHANNEL_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   // Predefined notifications
   typedef enum int unsigned {FULL          = 999_999,
                              EMPTY         = 999_998,
                              PUT           = 999_997,
                              GOT           = 999_996,
                              PEEKED        = 999_995,
                              ACTIVATED     = 999_994,
                              ACT_STARTED   = 999_993,
                              ACT_COMPLETED = 999_992,
                              ACT_REMOVED   = 999_991,
                              LOCKED        = 999_990,
                              UNLOCKED      = 999_989,
                              GRABBED       = 999_988,
                              UNGRABBED     = 999_987,
                              RECORDING     = 999_986,
                              PLAYBACK      = 999_985,
                              PLAYBACK_DONE = 999_984} notifications_e;

   // Arguments for lock methods
   typedef enum bit [1:0] {SOURCE = 2'b01,
                           SINK   = 2'b10
                           } endpoints_e;

   typedef enum int unsigned {INACTIVE  = 0,
                              PENDING   = 1,
                              STARTED   = 2,
                              COMPLETED = 3
                              } active_status_e;

   static vmm_opts       _vmm_opts  = new;
   static local bit      one_log;
   static local `VMM_LOG shared_log = null;

   local int full    = 0;
   local int empty   = 0;
   local bit is_sunk = 0;

   local vmm_data data[$];
   local vmm_data tee_data[$];
   local vmm_data active;
   local active_status_e active_status;
   local event teed;
   local vmm_channel downstream;
   local event       new_connection;
   local bit tee_on = 0;
   local bit [1:0] locks;

   local bit   full_chan;
   local event item_added;
   local event item_taken;

   local semaphore sem = new(1);

   local int iterator;

   local int record_fp;
   local time last_record_time;
   local bit is_put;
   local bit is_playback;
   local vmm_xactor producer;
   local vmm_xactor consumer;

   local `VMM_SCENARIO grab_owners[$];

   extern function new(string       name,
                       string       inst,
                       int unsigned full           = 1,
                       int unsigned empty          = 0,
                       bit          fill_as_bytes  = 1'b0);

`ifdef VMM_CHANNEL_BASE_METHODS
   `VMM_CHANNEL_BASE_METHODS
`endif

   extern function void reconfigure(int   full          = -1,
                                    int   empty         = -1,
                                    logic fill_as_bytes = 1'bx);
   extern function int unsigned full_level();
   extern function int unsigned empty_level();
   extern function int unsigned level();
   extern function int unsigned size();

   extern function bit is_full();
   extern function void flush();
   extern function void sink();
   extern function void flow();
   extern function void reset();

   extern function void lock(bit [1:0] who);
   extern function void unlock(bit [1:0] who);
   extern function bit  is_locked(bit [1:0] who);

   extern virtual task grab(`VMM_SCENARIO grabber);
   extern virtual function void ungrab(`VMM_SCENARIO grabber);
   extern virtual function bit is_grabbed();
   extern virtual function bit try_grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   // Define the methods for grabbing and releasing the channel
   extern local function bit check_grab_owners(`VMM_SCENARIO grabber);
   extern local function bit check_all_grab_owners(`VMM_SCENARIO grabber);
   extern local function void reset_grabbers();
   extern function void sneak(vmm_data obj, int offset = -1, `VMM_SCENARIO grabber = null);
   extern task put(vmm_data obj, int offset = -1, `VMM_SCENARIO grabber = null);
   extern task playback(output bit      success,
                        input  string   filename,
                        input  vmm_data factory,
                        input  bit      metered = 0,
                        `VMM_SCENARIO   grabber = null);
`else
   extern function void sneak(vmm_data obj, int offset = -1);
   extern task put(vmm_data obj, int offset = -1);
   extern task playback(output bit      success,
                        input  string   filename,
                        input  vmm_data factory,
                        input  bit      metered = 0);
`endif

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern function vmm_data unput(int offset = -1);

   extern task get(output vmm_data obj,
                   input  int      offset = 0);
   extern /*local*/ function void XgetX(output vmm_data obj,
                                        input  int      offset = 0);
   `ifdef OVM_INTEROP // OVM-VMM Interop v.Jul31'09
   /*local*/ function void get1(output vmm_data obj,
                                        input  int      offset = 0);
                                        XgetX(obj,offset);
   endfunction
   `endif
   extern local function void X_getX(output vmm_data obj,
                                     input  int      offset = 0);
   extern task peek(output vmm_data obj,
                    input  int      offset = 0);
   extern function vmm_data try_peek(int offset = 0);
   extern task activate(output vmm_data obj,
                        input  int      offset = 0);

   extern function vmm_data active_slot();
   extern function vmm_data start();
   extern function vmm_data complete(vmm_data status = null);
   extern function vmm_data remove();
   extern function active_status_e status();

   extern function bit tee_mode(bit is_on);
   extern task tee(output vmm_data obj);

   extern function void connect(vmm_channel downstream);
   extern function vmm_data for_each(bit reset = 0);
   extern function int unsigned for_each_offset();

   extern function bit record(string filename);

   extern local function int index(int offset, string from);

   /*local*/ extern function void Xrecord_to_fileX(bit [7:0] op_code,
                                                   int offset,
                                                   time diff_time);


   extern function void set_producer(vmm_xactor producer);
   extern function void set_consumer(vmm_xactor consumer);
   extern function vmm_xactor get_producer();
   extern function vmm_xactor get_consumer();
   extern function void kill();




`ifndef VMM_GRAB_DISABLED
   extern local task block_producer(`VMM_SCENARIO grabber);
`else
   extern local task block_producer();
`endif
   extern local task block_consumer();
   extern local function void unblock_producer();

`ifdef VMM_SB_DS_IN_STDLIB
   local     vmm_sb_ds_registration _vmm_sb_ds[$];

   extern function void register_vmm_sb_ds(vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(vmm_sb_ds sb);
`endif
endclass


`ifdef VMM_PARAM_CHANNEL

class vmm_channel_typed #(type T = vmm_data) extends vmm_channel;

   function new(string name,
                string inst,
                int    full = 1,
                int    empty = 0,
                bit    fill_as_bytes = 0);
      super.new(name, inst, full, empty, fill_as_bytes);
   endfunction: new

   function T unput(int offset = -1);
      $cast(unput, super.unput(offset));
   endfunction: unput

   task get(output T obj, input int offset = 0);
      vmm_data o;
      super.get(o, offset);
      $cast(obj, o);
   endtask: get

   task peek(output T obj, input int offset = 0);
      vmm_data o;
      super.peek(o, offset);
      $cast(obj, o);
   endtask: peek

   function T try_peek(int offset = 0);
      vmm_data o;
      o = super.try_peek(offset);
      $cast(try_peek, o);
   endfunction: try_peek

   task activate(output T obj, input int offset = 0);
      vmm_data o;
      super.activate(o, offset);
      $cast(obj, o);
   endtask: activate

   function T active_slot();
      $cast(active_slot, super.active_slot());
   endfunction: active_slot

   function T start();
      $cast(start, super.start());
   endfunction: start

   function T complete(vmm_data status = null);
      $cast(complete, super.complete(status));
   endfunction: complete

   function T remove();
      $cast(remove, super.remove());
   endfunction: remove

   task tee(output T obj);
      vmm_data o;
      super.tee(o);
      $cast(obj, o);
   endtask: tee

   function T for_each(bit reset = 0);
      $cast(for_each, super.for_each(reset));
   endfunction: for_each




endclass

`endif


//---------------------------------------------------------------------
// vmm_consensus
//

typedef class vmm_voter;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_consensus
`ifdef VMM_CONSENSUS_BASE
   extends `VMM_CONSENSUS_BASE
`endif
;

   `VMM_LOG log;

   typedef enum int { NEW_VOTE = 999_999 } notifications_e;
   `VMM_NOTIFY notify;

   local int n_dissenters;
   local int n_forcing;

   local vmm_voter voters[$];

   extern function new(string        name,
                       string        inst);

`ifdef VMM_CONSENSUS_BASE_METHODS
   `VMM_CONSENSUS_BASE_METHODS
`endif

   extern function vmm_voter register_voter(string name);
   extern function void register_xactor(vmm_xactor xact);
   extern function void register_channel(vmm_channel chan);
   extern function void register_notification(vmm_notify notify,
                                              int notification);
   extern function void register_no_notification(vmm_notify notify,
                                                 int notification);
   extern function void register_consensus(vmm_consensus vote,
                                           bit force_through = 0);

   extern function void unregister_voter(vmm_voter voter);
   extern function void unregister_xactor(vmm_xactor xact);
   extern function void unregister_channel(vmm_channel chan);
   extern function void unregister_notification(vmm_notify notify,
                                                int notification);
   extern function void unregister_consensus(vmm_consensus vote);
   extern function void unregister_all();

   extern task wait_for_consensus();
   extern task wait_for_no_consensus();
   extern function bit is_reached();
   extern function bit is_forced();

   extern virtual function string psdisplay(string prefix = "");
   extern function void yeas(ref string who[],
                             ref string why[]);
   extern function void nays(ref string who[],
                             ref string why[]);
   extern function void forcing(ref string who[],
                                ref string why[]);


   event new_results;
   extern /*local*/ function void XvoteX(bit was_agree,
                                         bit agree,
                                         bit was_forced,
                                         bit forced);
endclass: vmm_consensus

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_voter;
   local string name;
   local vmm_consensus consensus;
   local bit vote;
   local bit is_forced;
   local string why;
   local event killme;
   local vmm_xactor xactor_voter;
   local vmm_channel channel_voter;
   local vmm_notify  notify_voter;
   local int         notification;
   local vmm_consensus sub_vote;

   // Constructor is undocumented
   extern /*local*/ function new(string        name,
                                 vmm_consensus vote);

   extern function void oppose(string why = "No reason specified");
   extern function void consent(string why = "No reason specified");
   extern function void forced(string why = "No reason specified");

   // These methods are not documented either
   extern /*local*/ function string get_name();
   extern /*local*/ function bit    get_vote();
   extern /*local*/ function bit    get_forced();
   extern /*local*/ function string get_reason();
   extern /*local*/ function void xactor(vmm_xactor xact);
   extern /*local*/ function void channel(vmm_channel chan);
   extern /*local*/ function void notify(vmm_notify ntfy, int notification, bit is_on);
   extern /*local*/ function void sub_consensus(vmm_consensus vote, bit force_through);
   extern /*local*/ function void kill_voter();
   extern /*local*/ function vmm_xactor get_xactor();
   extern /*local*/ function vmm_channel get_channel();
   extern /*local*/ function vmm_notify  get_notify();
   extern /*local*/ function int         get_notification();
   extern /*local*/ function vmm_consensus get_consensus();
endclass


//---------------------------------------------------------------------
// vmm_env
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_env
`ifdef VMM_ENV_BASE
   extends `VMM_ENV_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   typedef enum int unsigned {GEN_CFG = 1,
                              BUILD,
                              RESET_DUT,
                              CFG_DUT,
                              START,
                              RESTART,
                              WAIT_FOR_END,
                              STOP,
                              CLEANUP,
                              REPORT,
                              RESTARTED} notifications_e;

   typedef enum int unsigned {HARD, SOFT, FIRM} restart_e;

   event          end_test;
   `VMM_CONSENSUS end_vote;

   protected int step;

   local bit             reset_rng_state;
   local string thread_rng_state_after_new;
   local string thread_rng_state_after_pre_test;
   local string thread_rng_state_before_start;

   local bit soft_restart;
   local bit soft_restartable;

   static vmm_opts _vmm_opts = new;
   static local vmm_env singleton = null;

   extern function new(string name = "Verif Env"
                       `VMM_ENV_BASE_NEW_ARGS);

`ifdef VMM_ENV_BASE_METHODS
   `VMM_ENV_BASE_METHODS
`endif

   extern virtual function string psdisplay(string prefix = "");

   extern task run();

   extern virtual protected task reset_env(restart_e kind);

   extern virtual protected task power_on_reset();
   extern virtual task hw_reset();

   extern virtual task power_up();

   extern task pre_test();
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   extern virtual task start();
   extern virtual task wait_for_end();
   extern virtual task stop();
   extern virtual task cleanup();
   extern virtual task restart(bit reconfig = 0);
   extern virtual task restart_test();
   extern virtual task report();

   extern virtual protected function void save_rng_state();
   extern virtual protected function void restore_rng_state();

   //
   // Methods and members to support the short-hand macros
   //
   protected static string    __vmm_prefix;
   protected static string    __vmm_image;
   protected        bit       __vmm_done_user;
   protected        int       __vmm_forks;
   protected        restart_e __vmm_restart;

   typedef enum {DO_PRINT   ='h001,
                 DO_START   ='h002,
                 DO_STOP    ='h004,
                 DO_RESET   ='h008,
                 DO_VOTE    ='h010,
		 DO_ALL     ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_env::restart_e restart_kind = vmm_env::FIRM);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual task do_vote();
   extern protected virtual task do_start();
   extern protected virtual task do_stop();
   extern protected virtual task do_reset(vmm_env::restart_e kind);

endclass


//---------------------------------------------------------------------
// vmm_subenv
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_subenv
`ifdef VMM_SUBENV_BASE
   extends `VMM_SUBENV_BASE
`endif
;
   `VMM_LOG    log;

   protected `VMM_CONSENSUS end_test;

   local enum {NEWED, CONFIGURED, STARTED, STOPPED, CLEANED} state = NEWED;

   extern function new(string         name,
                       string         inst,
                       `VMM_CONSENSUS end_test
                       `VMM_SUBENV_BASE_NEW_ARGS);

`ifdef VMM_SUBENV_BASE_METHODS
   `VMM_SUBENV_BASE_METHODS
`endif

   extern virtual function string psdisplay(string prefix = "");

   extern function vmm_consensus get_consensus();

   extern protected function void configured();

   extern virtual task start();
   extern virtual task stop();
   extern virtual task reset(vmm_env::restart_e kind = vmm_env::FIRM);
   extern virtual task cleanup();
   extern virtual function void report();

   //
   // Methods and members to support the short-hand macros
   //
   protected static string             __vmm_prefix;
   protected static string             __vmm_image;
   protected        bit                __vmm_done_user;
   protected        int                __vmm_forks;
   protected        vmm_env::restart_e __vmm_restart;

   typedef enum {DO_PRINT ='h001,
                 DO_START ='h002,
                 DO_STOP  ='h004,
                 DO_RESET ='h008,
                 DO_VOTE  ='h010,
		 DO_ALL   ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_env::restart_e restart_kind = vmm_env::FIRM);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual task do_vote();
   extern protected virtual task do_start();
   extern protected virtual task do_stop();
   extern protected virtual task do_reset(vmm_env::restart_e kind);

endclass: vmm_subenv


//---------------------------------------------------------------------
// vmm_xactor
//


`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_xactor_callbacks;
endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_xactor
`ifdef VMM_XACTOR_BASE
   extends `VMM_XACTOR_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   int stream_id;

   typedef enum int {XACTOR_IDLE        = 999999,
                     XACTOR_BUSY        = 999998,
                     XACTOR_STARTED     = 999997,
                     XACTOR_STOPPED     = 999996,
                     XACTOR_RESET       = 999995,
                     XACTOR_STOPPING    = 999994,
                     XACTOR_IS_STOPPED  = 999993
                     } notifications_e;

   local bit start_it;
   local bit stop_it;
   local bit reset_it;
   local event control_event;
   local int n_threads_to_stop;
   local int n_threads_stopped;
   local bit is_stopped;
   protected int reset_pending = 0;

   local bit main_running;

   local bit save_main_rng_state;
   local bit restore_main_rng_state;
   local string main_rng_state;
  
   /*local*/ vmm_channel Xinput_chansX[$];
   /*local*/ vmm_channel Xoutput_chansX[$];   
   /*local*/ static vmm_xactor _vmm_available_xactor[$];

   /*protected*/ vmm_xactor_callbacks callbacks[$];

   extern function new(string name,
	    	       string inst,
		       int    stream_id = -1
                       `VMM_XACTOR_BASE_NEW_ARGS);

   extern virtual function void kill();

`ifdef VMM_XACTOR_BASE_METHODS
   `VMM_XACTOR_BASE_METHODS
`endif




   typedef enum int {SOFT_RST,
                     PROTOCOL_RST,
                     FIRM_RST,
                     HARD_RST} reset_e;

   extern virtual function string get_name();
   extern virtual function string get_instance();

   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

   extern virtual function void save_rng_state();
   extern virtual function void restore_rng_state();

   extern virtual function string psdisplay(string prefix = "");
   extern virtual function void xactor_status(string prefix = "");

   extern virtual protected task main();
   extern local function void check_all_threads_stopped();
   extern protected task wait_if_stopped(int unsigned n_threads = 1);
   extern protected task wait_if_stopped_or_empty(vmm_channel  chan,
                                                  int unsigned n_threads = 1);

   extern virtual function void prepend_callback(vmm_xactor_callbacks cb);
   extern virtual function void append_callback(vmm_xactor_callbacks cb);
   extern virtual function void unregister_callback(vmm_xactor_callbacks cb);

   extern function void get_input_channels(ref vmm_channel chans[$]);
   extern function void get_output_channels(ref vmm_channel chans[$]);




`ifdef VMM_SB_DS_IN_STDLIB
   local     vmm_sb_ds_registration _vmm_sb_ds[$];

   extern protected function void inp_vmm_sb_ds(vmm_data tr);
   extern protected function void exp_vmm_sb_ds(vmm_data tr);
   extern function void register_vmm_sb_ds(vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(vmm_sb_ds sb);
`endif

   //
   // Methods and members to support the short-hand macros
   //
   protected static string  __vmm_prefix;
   protected static string  __vmm_image;
   protected static bit     __vmm_done_user;

   typedef enum {DO_PRINT   ='h001,
                 DO_START   ='h002,
                 DO_STOP    ='h004,
                 DO_RESET   ='h010,
                 DO_KILL    ='h020,
		 DO_ALL     ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_xactor::reset_e   rst_typ = SOFT_RST);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual function void do_start_xactor();
   extern protected virtual function void do_stop_xactor();
   extern protected virtual function void do_reset_xactor(vmm_xactor::reset_e rst_typ);
   extern protected virtual function void do_kill_xactor();
endclass


class vmm_xactor_iter;
  static `VMM_LOG log = new("vmm_xactor_iter", "class");

  string name;
  string inst;

`ifdef NO_STATIC_METHODS
  local static vmm_xactor _vmm_xactor = null;
`endif
  local int idx;

  extern function new(string  name = "",
                      string  inst = "");
  extern function vmm_xactor first();
  extern function vmm_xactor next();
  extern function vmm_xactor xactor();

  extern protected function void move_iterator();
endclass


//---------------------------------------------------------------------
// vmm_ms_scenario_gen
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_gen_callbacks extends vmm_xactor_callbacks;
   virtual task pre_scenario_randomize(vmm_ms_scenario_gen gen,
                                       ref vmm_ms_scenario scenario);
   endtask

   virtual task post_scenario_gen(vmm_ms_scenario_gen gen,
                                  vmm_ms_scenario     scenario,
                                  ref bit             dropped);
   endtask
endclass: vmm_ms_scenario_gen_callbacks


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_gen extends `VMM_XACTOR;
    local vmm_channel channel_registry[string];
    local vmm_ms_scenario mss_registry[string];
    local vmm_ms_scenario_gen mssg_registry[string];
    local int n_insts;

    int unsigned stop_after_n_insts;
    int unsigned stop_after_n_scenarios;

    typedef enum int {GENERATED, DONE} symbols_e;

    vmm_ms_scenario_election select_scenario;
    vmm_ms_scenario scenario_set[$];

    protected int scenario_count;
    protected int inst_count;

    extern function new(string inst, int stream_id=-1
                        `VMM_XACTOR_NEW_ARGS);
    extern virtual function string psdisplay(string prefix = "");

    extern function int unsigned get_n_insts();
    extern function int unsigned get_n_scenarios();
    extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

    extern virtual function void register_channel(string name,
                                                  vmm_channel chan);
    extern virtual function bit channel_exists(string name);
    extern virtual function void replace_channel(string name,
                                                 vmm_channel chan);
    extern virtual function void get_all_channel_names(ref string name[$]);
    extern virtual function void get_names_by_channel(vmm_channel chan,
                                                      ref string name[$]);
    extern virtual function string get_channel_name(vmm_channel chan);
    extern virtual function bit unregister_channel(vmm_channel chan);
    extern virtual function vmm_channel unregister_channel_by_name(string name);
    extern virtual function vmm_channel get_channel(string name);

    extern virtual function void register_ms_scenario(string name,
                                                      vmm_ms_scenario scenario);
    extern virtual function bit ms_scenario_exists(string name);
    extern virtual function void replace_ms_scenario(string name,
                                                     vmm_ms_scenario scenario);
    extern virtual function void get_all_ms_scenario_names(ref string name[$]);
    extern virtual function void get_names_by_ms_scenario(vmm_ms_scenario scenario,
                                                          ref string name[$]);
    extern virtual function string get_ms_scenario_name(vmm_ms_scenario scenario);
    extern virtual function int get_ms_scenario_index(vmm_ms_scenario scenario);
    extern virtual function bit unregister_ms_scenario(vmm_ms_scenario scenario);
    extern virtual function vmm_ms_scenario unregister_ms_scenario_by_name(string name);
    extern virtual function vmm_ms_scenario get_ms_scenario(string name);

    extern virtual function void register_ms_scenario_gen(string name,
                                                          vmm_ms_scenario_gen scenario_gen);
    extern virtual function bit ms_scenario_gen_exists(string name);
    extern virtual function void replace_ms_scenario_gen(string name,
                                                         vmm_ms_scenario_gen scenario_gen);
    extern virtual function void get_all_ms_scenario_gen_names(ref string name[$]);
    extern virtual function void get_names_by_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen,
                                                              ref string name[$]);
    extern virtual function string get_ms_scenario_gen_name(vmm_ms_scenario_gen scenario_gen);
    extern virtual function bit unregister_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen);
    extern virtual function vmm_ms_scenario_gen unregister_ms_scenario_gen_by_name(string name);
    extern virtual function vmm_ms_scenario_gen get_ms_scenario_gen(string name);

    extern virtual protected task main();
endclass: vmm_ms_scenario_gen


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_broadcast extends `VMM_XACTOR;

   typedef enum {AFAP = 1,
                 ALAP = 2
                 } bcast_mode_e;

   local vmm_channel in_chan;

   local int n_out_chans;
   local bit dflt_use_refs;
   local int mode;

   local bit          use_refs[$];
   local bit          is_on[$];
   local vmm_channel  out_chans[$];

   local event new_cycle;

   extern function new(string      name,
                       string      inst,
                       vmm_channel source,
                       bit         use_references = 1,
                       int         mode           = AFAP
                       `VMM_XACTOR_NEW_ARGS);
   extern virtual function string psdisplay(string prefix = "");

   extern virtual task broadcast_mode(bcast_mode_e mode);
   extern virtual function int new_output(vmm_channel channel,
                                          logic use_references = 1'bx);
   extern virtual function void bcast_on(int unsigned output_id);
   extern virtual function void bcast_off(int unsigned output_id);
   extern virtual protected function bit add_to_output(int unsigned decision_id,
                                                       int unsigned output_id,
                                                       vmm_channel       channel,
                                                       vmm_data          obj);
   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();

   extern local function void bcast_on_off(int channel_id,
                                           int on_off);
   extern virtual task bcast_to_output(int channel_id,
                                       int on_off);
   extern local task broadcast();
   extern local task sink_if_outs();
endclass : vmm_broadcast


//---------------------------------------------------------------------
// vmm_scheduler
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scheduler_election;
   int          instance_id;
   int unsigned election_id;

   int unsigned      n_sources;
   vmm_channel       sources[$];
   int unsigned      ids[$];
   int unsigned      id_history[$];
   vmm_data          obj_history[$];
   int unsigned      next_idx;

   rand int unsigned source_idx;
   rand int unsigned obj_offset;

   constraint vmm_scheduler_election_valid {
      obj_offset == 0;
      source_idx >= 0;
      source_idx < n_sources;
   }

   constraint default_round_robin {
      source_idx == next_idx;
   }
endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scheduler extends `VMM_XACTOR;

   vmm_scheduler_election randomized_sched;

   protected vmm_channel out_chan;

   local vmm_channel       sources[$];
   local int               is_on[$];
   local int               instance_id;
   local int               election_count;
   local event             next_cycle;

   extern function new(string       name,
                       string       inst,
                       vmm_channel  destination,
                       int          instance_id = -1
                       `VMM_XACTOR_NEW_ARGS);
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function int new_source(vmm_channel channel);
   extern virtual task sched_from_input(int channel_id,
                                        int on_off);
   extern virtual protected task schedule(output vmm_data     obj,
                                          input  vmm_channel  sources[$],
                                          input  int unsigned input_ids[$]);
   extern virtual protected task get_object(output vmm_data     obj,
                                            input  vmm_channel  source,
                                            input  int unsigned input_id,
                                            input  int          offset);
   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();

   extern local task schedule_cycle();
endclass


//---------------------------------------------------------------------
// XVC
//

typedef class xvc_xactor;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_action extends `VMM_DATA;
   local string name;

   vmm_xactor_callbacks callbacks[];

   extern function new(string name,
                       vmm_log log);

   extern function string get_name();

   extern virtual function xvc_action parse(string argv[]);
   extern virtual task execute(vmm_channel exec_chan,
                               xvc_xactor  xvc);

   extern virtual function string psdisplay(string prefix = "");
   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);

   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);
   extern virtual protected function void copy_data(vmm_data to);

   extern virtual function bit compare(input  vmm_data to,
                                       output string   diff,
                                       input  int      kind = -1);

   extern virtual function int unsigned byte_size(int kind = -1);
   extern virtual function int unsigned max_byte_size(int kind = -1);
   extern virtual function int unsigned byte_pack(ref logic [7:0]    bytes[],
                                                  input int unsigned offset = 0,
                                                  input int          kind   = -1);
   extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                    input int unsigned    offset = 0,
                                                    input int             len    = -1,
                                                    input int             kind   = -1);
endclass: xvc_action

`vmm_channel(xvc_action)


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_xactor extends `VMM_XACTOR;

   `VMM_LOG trace;

   xvc_action_channel action_chan;
   xvc_action_channel interrupt_chan;

   protected vmm_channel exec_chan;
   protected vmm_xactor  xactors[];

   local xvc_action known_actions[$];
   local xvc_action idle;

   local bit interrupt;
   local bit interrupted;
   local event interrupted_event;
   local event rte;
   local xvc_action executing;
   local xvc_action suspended;

   extern function new(string             name,
                       string             inst,
                       int                stream_id = -1,
                       xvc_action_channel action_chan = null,
                       xvc_action_channel interrupt_chan = null
                       `VMM_XACTOR_NEW_ARGS);

   extern function void add_action(xvc_action action);
   extern function xvc_action parse(string argv[]);

   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

   extern virtual function void xactor_status(string prefix = "");

   extern virtual task main();

   extern task wait_if_interrupted();

   extern local task execute_actions();
   extern local task execute_interruptions();
   extern local task execute_action(xvc_action_channel chan,
                                    string             descr);

   extern virtual function void save_rng_state();
   extern virtual function void restore_rng_state();
endclass: xvc_xactor


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_manager;

   `VMM_LOG    log;
   `VMM_LOG    trace;

   `VMM_NOTIFY notify;

   protected xvc_xactor xvcQ[$];

   extern function new(string inst = "Main");

   extern function bit add_xvc(xvc_xactor xvc);
   extern function bit remove_xvc(xvc_xactor xvc);

   extern function bit split(string     command,
                             ref string argv[]);

endclass: xvc_manager


//------------------------------------------------------------
// vmm_test
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_test;
   local string name;
   local string doc;
   vmm_log log;

   static vmm_test_registry registry = new;

   extern function new(string name,
                       string doc = "");

   extern virtual task run(vmm_env e);

   extern virtual function string get_name();
   extern virtual function string get_doc();

   extern /*local*/ function void Xset_log_instanceX(string inst);
endclass


`include "std_lib/vmm_opts.sv"
`include "std_lib/vmm_log.sv"
`include "std_lib/vmm_notify.sv"
`include "std_lib/vmm_data.sv"
`include "std_lib/vmm_scenario.sv"
`include "std_lib/vmm_channel.sv"
`include "std_lib/vmm_consensus.sv"
`include "std_lib/vmm_subenv.sv"
`include "std_lib/vmm_env.sv"
`include "std_lib/vmm_xactor.sv"
`include "std_lib/vmm_broadcast.sv"
`include "std_lib/vmm_scheduler.sv"
`include "std_lib/vmm_ms_scenario_gen.sv"
`include "std_lib/xvc_action.sv"
`include "std_lib/xvc_xactor.sv"
`include "std_lib/xvc_manager.sv"
`ifdef VMM_XVC_MANAGER
`include "std_lib/vmm_xvc_manager.sv"
`endif
`include "std_lib/vmm_test.sv"


`ifdef VMM_IN_PACKAGE
endpackage: vmm_std_lib
`endif

`undef VMM_BEING_PARSED

`endif

`ifdef VMM_IN_PACKAGE
import vmm_std_lib::*;
`endif
