// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
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


//
// This file needs to be included at the 'VMM_POST_INCLUDE' point
//

`ifndef VMM_OBJECT
   `define VMM_OBJECT                 vmm_object
`endif
`ifndef VMM_OBJECT_NEW_ARGS
   `define VMM_OBJECT_NEW_ARGS
   `define VMM_OBJECT_NEW_EXTERN_ARGS
   `define VMM_OBJECT_NEW_CALL
`endif
`ifndef VMM_OBJECT_BASE_NEW_ARGS
   `define VMM_OBJECT_BASE_NEW_ARGS
   `define VMM_OBJECT_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_OBJECT_BASE
   `ifndef VMM_OBJECT_BASE_NEW_CALL
      `define VMM_OBJECT_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_OBJECT_BASE_METHODS
   `define VMM_OBJECT_BASE_METHODS
`endif


typedef class `VMM_OBJECT;
`ifdef VMM_OBJECT_BASE
typedef class `VMM_OBJECT_BASE;
`endif


//---------------------------------------------------------------------
// vmm_object
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
virtual class vmm_object
`ifdef VMM_OBJECT_BASE
   extends `VMM_OBJECT_BASE
`endif
;

   typedef enum {VMM_UNKNOWN, VMM_OBJECT, VMM_DATA, VMM_SCENARIO,
		 VMM_MS_SCENARIO, VMM_CHANNEL, VMM_NOTIFY,
                 VMM_XACTOR, VMM_SUBENV, VMM_ENV,
                 VMM_CONSENSUS, VMM_TEST} type_e;

   local vmm_object parent;
   local type_e typ;

   extern function new(vmm_object parent = null
                       `VMM_OBJECT_BASE_NEW_ARGS);

`ifdef VMM_OBJECT_BASE_METHODS
   `VMM_OBJECT_BASE_METHODS
`endif

   extern function void       set_parent(vmm_object parent);
   extern function vmm_object get_parent(type_e typ = VMM_OBJECT);
   extern function type_e     get_type();
   extern function string     get_hier_inst_name();

`ifndef VMM_OBJECT_NO_DISPLAY
   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");
`endif

   extern local function vmm_log get_child_log(vmm_object child);
   extern local function vmm_log get_parent_log(vmm_object parent);
endclass: vmm_object


function vmm_object::new(vmm_object parent
                         `VMM_OBJECT_BASE_NEW_ARGS);
   this.typ = VMM_UNKNOWN; // Find out type only if needed
   this.set_parent(parent);
endfunction


function void vmm_object::set_parent(vmm_object parent);
   vmm_log par;
   vmm_log log = null;

   if (parent == null && this.parent != null) begin
      // Break the existing parent/child relationship
      par = this.get_parent_log(this.parent);
      log = this.get_child_log(this);
      if (par != null && log != null) par.is_not_above(log);
   end

   this.parent = parent;
   if (parent == null) return;

   // If both this and the parent have a vmm_log instance
   // make this log below the parent's log
   par = this.get_parent_log(this.parent);
   if (log == null) log = this.get_child_log(this);
   if (par != null && log != null) par.is_above(log);
endfunction


function vmm_log vmm_object::get_child_log(vmm_object child);
   // Note: only SOME of the VMM objects have their own log instances
   begin
      vmm_channel obj;
      if ($cast(obj, child)) begin
         // If is a shared instance, abort
         if (obj.log.get_instance() == "[shared]") return null;
         return obj.log;
      end
   end
   begin
      vmm_xactor obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_consensus obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
`endif

  return null;
endfunction: get_child_log


function vmm_log vmm_object::get_parent_log(vmm_object parent);
   // Only some kind of objects can be hierarhical parents
   begin
      vmm_xactor obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
`endif

   // if the parent is unsuitable, nothing to do
   return null;
endfunction: get_parent_log


function vmm_object vmm_object::get_parent(type_e typ);
   vmm_object obj = this;

   while (obj.parent != null) begin
      if (typ == VMM_OBJECT ||
          obj.parent.get_type() == typ) return obj.parent;

      obj = obj.parent;
   end
   return null;
endfunction


function vmm_object::type_e vmm_object::get_type();
   if (this.typ != VMM_UNKNOWN) return this.typ;

   // Find out -- and cache -- the object type
   begin
      vmm_scenario obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_SCENARIO;
         return this.typ;
      end
   end
   begin
      vmm_data obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_DATA;
         return this.typ;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_ms_scenario obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_MS_SCENARIO;
         return this.typ;
      end
   end
`endif
   begin
      vmm_channel obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_CHANNEL;
         return this.typ;
      end
   end
   begin
      vmm_notify obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_NOTIFY;
         return this.typ;
      end
   end
   begin
      vmm_xactor obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_XACTOR;
         return this.typ;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_SUBENV;
         return this.typ;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_ENV;
         return this.typ;
      end
   end
   begin
      vmm_consensus obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_CONSENSUS;
         return this.typ;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_TEST;
         return this.typ;
      end
   end
`endif

   // I give up!
   this.typ = VMM_OBJECT;
   return this.typ;
endfunction


function string vmm_object::get_hier_inst_name();
   vmm_xactor xact;
   vmm_subenv sub;
   vmm_env    env;
   vmm_log    log;
   string     name;

   log  = null;
   name = "[unkown]";

   case (this.get_type())

   VMM_DATA:        name = "[vmm_data]";
   VMM_SCENARIO:    name = "[vmm_scenario]";
   VMM_MS_SCENARIO: name = "[vmm_ms_scenario]";
   VMM_NOTIFY:      name = "[vmm_notify]";

   VMM_CHANNEL:     begin
      vmm_channel obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_XACTOR: begin
      vmm_xactor obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_SUBENV: begin
      vmm_subenv obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_ENV: begin
      vmm_env obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_CONSENSUS: begin
      vmm_consensus obj;
      $cast(obj, this);
      log = obj.log;
   end

`ifdef NOT_YET_IMPLEMENTED
   VMM_TEST: begin
      vmm_test obj;
      $cast(obj, this);
      log = obj.log;
   end
`endif
   endcase

   // Unamed object?
   if (log == null) begin
      if (this.parent == null) return name;
      return {this.parent.get_hier_inst_name(), ".", name};
   end

   name = log.get_instance();

   // If named using hierarchical names, that's it!
   if (log.uses_hier_inst_name()) return name;

   // If the log instance does not have an instance name...
   if (name == "") name = log.get_name();
   if (name == "") name = "[Anonymous]";

   // If no parent, that's it.
   if (this.parent == null) return name;

   return {this.parent.get_hier_inst_name(), ".", name};
endfunction


`ifndef VMM_OBJECT_NO_DISPLAY
function void vmm_object::display(string prefix);
   $write("%s\n", this.psdisplay(prefix));
endfunction


function string vmm_object::psdisplay(string prefix);
   return "";
endfunction
`endif
