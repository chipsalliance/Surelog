//dvt/vtech/dev/main/ovm/src/macros/ovm_callback_defines.svh#4 - edit change 2173693 (text)
//-----------------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corp.
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
//-----------------------------------------------------------------------------

`ifndef OVM_CB_MACROS_SVH
`define OVM_CB_MACROS_SVH


//-----------------------------------------------------------------------------
// Group: Callback Macros
//-----------------------------------------------------------------------------


//-----------------------------------------------------------------------------
// MACRO: `ovm_do_callbacks
//
// Calls the given ~METHOD~ of all callbacks of type ~CB~ registered with
// the calling object (i.e. ~this~ object), which is or is based on type ~T~.
//
// This macro executes all of the callbacks associated with the calling
// object (i.e. ~this~ object). The macro takes three arguments:
//
// - CB is the class type of the callback objects to execute. The class
//   type must have a function signature that matches the FNC argument.
//
// - T is the type associated with the callback. Typically, an instance
//   of type T is passed as one the arguments in the ~METHOD~ call.
//
// - METHOD is the method call to invoke, with all required arguments as
//   if they were invoked directly.
//
// For example, given the following callback class definition:
//
//| virtual class mycb extends ovm_cb;
//|   pure function void my_function (mycomp comp, int addr, int data);
//| endclass
//
// A component would invoke the macro as
//
//| task mycomp::run(); 
//|    int curr_addr, curr_data;
//|    ...
//|    `ovm_do_callbacks(mycb, mycomp, my_function(this, curr_addr, curr_data)
//|    ...
//| endtask
//-----------------------------------------------------------------------------


`define ovm_do_callbacks(CB,T,METHOD_CALL) \
  `ovm_do_obj_callbacks(CB,T,this,METHOD_CALL)


//-----------------------------------------------------------------------------
// MACRO: `ovm_do_obj_callbacks
//
// Calls the given ~METHOD~ of all callbacks based on type ~CB~ registered with
// the given object, ~OBJ~, which is or is based on type ~T~.
//
// This macro is identical to <ovm_do_callbacks (CB,T,METHOD)> macro,
// but it has an additional ~OBJ~ argument to allow the specification of an
// external object to associate the callback with. For example, if the
// callbacks are being applied in a sequence, ~OBJ~ could be specified
// as the associated sequencer or parent sequence.
//-----------------------------------------------------------------------------

`define ovm_do_obj_callbacks(CB,T,OBJ,METHOD_CALL) \
   begin \
     ovm_callbacks #(T,CB) cbs = ovm_callbacks #(T,CB)::get_global_cbs(); \
     ovm_queue #(CB) cbq; \
     if (cbs.exists(OBJ)) begin \
     /* Make a copy of the queue in case the user tries changing the queue */ \
     /* inside the callback. For example, for a one-shot callback. */ \
     cbq = cbs.get(OBJ); \
     cbq = new cbq; \
     for (int i=0; i<cbq.size();i++) begin \
       CB cb = cbq.get(i); \
       if (cb.is_enabled()) \
         cb.METHOD_CALL; \
     end \
     end \
   end




//-----------------------------------------------------------------------------
// MACRO: `ovm_do_callbacks_exit_on
//
// Calls the given ~METHOD~ of all callbacks of type ~CB~ registered with
// the calling object (i.e. ~this~ object), which is or is based on type ~T~,
// returning upon the first callback returning the bit value given by ~VAL~.
//
// This macro executes all of the callbacks associated with the calling
// object (i.e. ~this~ object). The macro takes three arguments:
//
// - CB is the class type of the callback objects to execute. The class
//   type must have a function signature that matches the FNC argument.
//
// - T is the type associated with the callback. Typically, an instance
//   of type T is passed as one the arguments in the ~METHOD~ call.
//
// - METHOD is the method call to invoke, with all required arguments as
//   if they were invoked directly.
//
// - VAL, if 1, says return upon the first callback invocation that
//   returns 1. If 0, says return upon the first callback invocation that
//   returns 0.
//
// For example, given the following callback class definition:
//
//| virtual class mycb extends ovm_cb;
//|   pure function bit drop_trans (mycomp comp, my_trans trans);
//| endclass
//
// A component would invoke the macro as
//
//| task mycomp::run(); 
//|    my_trans trans;
//|    forever begin
//|      get_port.get(trans);
//|      if (`ovm_do_callbacks_exit_on(mycb, mycomp, extobj, drop_trans(this,trans), 1)
//|        ovm_report_info("DROPPED",{"trans dropped: %s",trans.convert2string()});
//|      // execute transaction
//|    end
//| endtask
//-----------------------------------------------------------------------------


`define ovm_do_callbacks_exit_on(CB,T,METHOD_CALL,VAL) \
  `ovm_do_obj_callbacks_exit_on(CB,T,this,METHOD_CALL,VAL) \


//-----------------------------------------------------------------------------
// MACRO: `ovm_do_obj_callbacks_exit_on
//
// Calls the given ~METHOD~ of all callbacks of type ~CB~ registered with
// the given object ~OBJ~, which must be or be based on type ~T~, and returns
// upon the first callback that returns the bit value given by ~VAL~.
//-----------------------------------------------------------------------------

`define ovm_do_obj_callbacks_exit_on(CB,T,OBJ,METHOD_CALL,VAL) \
   begin \
     ovm_callbacks #(T,CB) cbs = ovm_callbacks #(T,CB)::get_global_cbs(); \
     ovm_queue #(CB) cbq; \
     if (cbs == null || !cbs.exists(OBJ)) \
       return 1-VAL; \
     cbq = cbs.get(OBJ); \
     cbq = new cbq; \
     for (int i=0; i<cbq.size();i++) begin \
       CB cb = cbq.get(i); \
       if (cb.is_enabled() && cb.METHOD_CALL == VAL) \
         return VAL; \
     end \
     return 1-VAL; \
   end


//-----------------------------------------------------------------------------
// MACRO: `ovm_do_task_callbacks
//
// Calls the given ~METHOD~ of all callbacks of type ~CB~ registered with
// the calling object (i.e. ~this~ object), which is or is based on type ~T~.
//
// This macro is the same as the <ovm_do_callbacks> macro except that each
// callback is executed inside of its own thread. The threads are concurrent,
// but the execution order of the threads is simulator dependent. The macro
// does not return until all forked callbacks have completed.
//
//| virtual class mycb extends ovm_cb;
//|   pure task my_task(mycomp, int addr, int data);
//| endclass
//
//| task mycomp::run(); 
//|    int curr_addr, curr_data;
//|    ...
//|    `ovm_callback(mycb, mycomp, my_task(this, curr_addr, curr_data))
//|    ...
//| endtask
//-----------------------------------------------------------------------------

`define ovm_do_task_callbacks(CB,T,METHOD_CALL) \
  `ovm_do_obj_task_callbacks(CB,T,this,METHOD_CALL)


//-----------------------------------------------------------------------------
// MACRO: `ovm_do_ext_task_callbacks
//
// This macro is identical to <ovm_do_task_callbacks> macro except there is an
// additional ~OBJ~ argument that allows the user to execute callbacks associated
// with an external object instance ~OBJ~ instead of the calling (~this~) object.
//-----------------------------------------------------------------------------

`define ovm_do_obj_task_callbacks(CB,T,OBJ,METHOD_CALL) \
  begin \
     ovm_callbacks #(T,CB) cbs = ovm_callbacks #(T,CB)::get_global_cbs(); \
     ovm_queue #(CB) cbq; \
     cbq = new cbq; \
     if (cbs.exists(OBJ)) begin\
       cbq = cbs.get(OBJ); \
       fork begin \
         for (int i=0; i<cbq.size();i++) begin \
           CB cb = cbq.get(i); \
           if (cb.is_enabled()) begin \
             fork begin \
               `ovm_cb_trace(cb,OBJ,`"fork/join_none METHOD_CALL`") \
               cb.METHOD_CALL; \
             end join_none \
           end \
         end \
         wait fork; \
       end join \
     end \
   end




// callback trace macros can be turned on via +define+OVM_CB_TRACE_ON

`ifdef OVM_CB_TRACE_ON

`define ovm_cb_trace(OBJ,CB,OPER) \
  if(reporter.get_report_action(OVM_INFO,"OVMCB_TRC") & OVM_DISPLAY) begin \
    string msg; \
    msg = (OBJ == null) ? "null" : $sformatf("%s (%s@%0d)", \
      OBJ.get_full_name(), OBJ.get_type_name(), OBJ.get_inst_id()); \
    reporter.ovm_report_info("OVMCB_TRC", $sformatf("%s: callback %s (%s@%0d) : to object %s",  \
       OPER, CB.get_name(), CB.get_type_name(), CB.get_inst_id(), msg), OVM_NONE); \
  end

`define ovm_cb_trace_noobj(CB,OPER) \
  if(reporter.get_report_action(OVM_INFO,"OVMCB_TRC") & OVM_DISPLAY) \
    reporter.ovm_report_info("OVMCB_TRC", $sformatf("%s: callback %s (%s@%0d)" ,  \
       OPER, CB.get_name(), CB.get_type_name(), CB.get_inst_id()), OVM_NONE);

`else

`define ovm_cb_trace_noobj(CB,OPER) /* null */
`define ovm_cb_trace(OBJ,CB,OPER) /* null */

`endif


`endif
