// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_factory.sv#31 $
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

`include "base/ovm_factory.svh"

//------------------------------------------------------------------------------
//
// CLASS- ovm_factory
//
//------------------------------------------------------------------------------

// get
// ---

function ovm_factory ovm_factory::get();
  if (m_inst == null) begin
    m_inst = new();
  end
  return m_inst;
endfunction

// new
// ---

function ovm_factory::new ();
endfunction


// auto_register (static)
// -------------

function void ovm_factory::auto_register (ovm_object_wrapper obj);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::auto_register() has been deprecated and replaced by ",
      "factory.register()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  m_inst.register(obj);
endfunction


// register
// --------

function void ovm_factory::register (ovm_object_wrapper obj);

  if (obj == null) begin
    ovm_report_fatal ("NULLWR", "Attempting to register a null object with the factory", OVM_NONE);
  end
  if (obj.get_type_name() == "" || obj.get_type_name() == "<unknown>") begin
    //ovm_report_warning("EMPTNM", {"Factory registration with ",
    //  "unknown type name prevents name-based operations. "});
  end
  else begin
    if (m_type_names.exists(obj.get_type_name()))
      ovm_report_warning("TPRGED", {"Type name '",obj.get_type_name(),
        "' already registered with factory. No string-based lookup ",
        "support for multiple types with the same type name."}, OVM_NONE);
    else 
      m_type_names[obj.get_type_name()] = obj;
  end

  if (m_types.exists(obj)) begin
    if (obj.get_type_name() != "" && obj.get_type_name() != "<unknown>")
      ovm_report_warning("TPRGED", {"Object type '",obj.get_type_name(),
                         "' already registered with factory. "}, OVM_NONE);
  end
  else begin
    m_types[obj] = 1;
    // If a named override happens before the type is registered, need to copy
    // the override queue.
    if(m_inst_override_name_queues.exists(obj.get_type_name())) begin
       m_inst_override_queues[obj] = new;
       m_inst_override_queues[obj].queue = m_inst_override_name_queues[obj.get_type_name()].queue;
       m_inst_override_name_queues.delete(obj.get_type_name());
    end
    if(m_wildcard_inst_overrides.size()) begin
       if(! m_inst_override_queues.exists(obj)) 
            m_inst_override_queues[obj] = new;
       foreach (m_wildcard_inst_overrides[i]) begin
         if(ovm_is_match(obj.get_type_name(), m_wildcard_inst_overrides[i].orig_type_name))
            m_inst_override_queues[obj].queue.push_back(m_wildcard_inst_overrides[i]);
       end
    end

  end

endfunction



// set_type_override (static)
// -----------------

function void ovm_factory::set_type_override (string original_type_name,
                                              string override_type_name,
                                              bit replace=1);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::set_type_override() has been deprecated and replaced by ",
      "factory.set_type_override_by_name()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  m_inst.set_type_override_by_name (original_type_name, override_type_name, replace);
endfunction


// set_type_override_by_type
// -------------------------

function void ovm_factory::set_type_override_by_type (ovm_object_wrapper original_type,
                                                      ovm_object_wrapper override_type,
                                                      bit replace=1);
  bit replaced;

  // check that old and new are not the same
  if (original_type == override_type) begin
    if (original_type.get_type_name() == "" || original_type.get_type_name() == "<unknown>")
      ovm_report_warning("TYPDUP", {"Original and override type ",
                                    "arguments are identical"}, OVM_NONE);
    else
      ovm_report_warning("TYPDUP", {"Original and override type ",
                                    "arguments are identical: ",
                                    original_type.get_type_name()}, OVM_NONE);
    return;
  end

  // register the types if not already done so, for the benefit of string-based lookup
  if (!m_types.exists(original_type))
    register(original_type); 

  if (!m_types.exists(override_type))
    register(override_type); 


  // check for existing type override
  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type == original_type ||
        (m_type_overrides[index].orig_type_name != "<unknown>" &&
         m_type_overrides[index].orig_type_name != "" &&
         m_type_overrides[index].orig_type_name == original_type.get_type_name())) begin
      string msg;
      msg = {"Original object type '",original_type.get_type_name(),
             "' already registered to produce '",
             m_type_overrides[index].ovrd_type_name,"'"};
      if (!replace) begin
        msg = {msg, ".  Set 'replace' argument to replace the existing entry."};
        ovm_report_info("TPREGD", msg, OVM_MEDIUM);
        return;
      end
      msg = {msg, ".  Replacing with override to produce type '",
                  override_type.get_type_name(),"'."};
      ovm_report_info("TPREGR", msg, OVM_MEDIUM);
      replaced = 1;
      m_type_overrides[index].orig_type = original_type; 
      m_type_overrides[index].orig_type_name = original_type.get_type_name(); 
      m_type_overrides[index].ovrd_type = override_type; 
      m_type_overrides[index].ovrd_type_name = override_type.get_type_name(); 
    end
  end

  // make a new entry
  if (!replaced) begin
    ovm_factory_override override;
    override = new(.orig_type(original_type),
                   .orig_type_name(original_type.get_type_name()),
                   .full_inst_path("*"),
                   .ovrd_type(override_type));

    m_type_overrides.push_back(override);
  end

endfunction


// set_type_override_by_name
// -------------------------

function void ovm_factory::set_type_override_by_name (string original_type_name,
                                                      string override_type_name,
                                                      bit replace=1);
  bit replaced;
  
  ovm_object_wrapper original_type=null;
  ovm_object_wrapper override_type=null;

  if(m_type_names.exists(original_type_name))
    original_type = m_type_names[original_type_name];

  if(m_type_names.exists(override_type_name))
    override_type = m_type_names[override_type_name];

  // check that type is registered with the factory
  if (override_type == null) begin
      ovm_report_error("TYPNTF", {"Cannot register override for original type '",
      original_type_name,"' because the override type '",
      override_type_name, "' is not registered with the factory."}, OVM_NONE);
    return;
  end

  // check that old and new are not the same
  if (original_type_name == override_type_name) begin
      ovm_report_warning("TYPDUP", {"Requested and actual type name ",
      " arguments are identical: ",original_type_name,". Ignoring this override."}, OVM_NONE);
    return;
  end

  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type_name == original_type_name) begin
      if (!replace) begin
        ovm_report_info("TPREGD", {"Original type '",original_type_name,
          "' already registered to produce '",m_type_overrides[index].ovrd_type_name,
          "'.  Set 'replace' argument to replace the existing entry."}, OVM_MEDIUM);
        return;
      end
      ovm_report_info("TPREGR", {"Original object type '",original_type_name,
        "' already registered to produce '",m_type_overrides[index].ovrd_type_name,
        "'.  Replacing with override to produce type '",override_type_name,"'."}, OVM_MEDIUM);
      replaced = 1;
      m_type_overrides[index].ovrd_type = override_type; 
      m_type_overrides[index].ovrd_type_name = override_type_name; 
    end
  end

  if (original_type == null)
    m_lookup_strs[original_type_name] = 1;

  if (!replaced) begin
    ovm_factory_override override;
    override = new(.orig_type(original_type),
                   .orig_type_name(original_type_name),
                   .full_inst_path("*"),
                   .ovrd_type(override_type));

    m_type_overrides.push_back(override);
//    m_type_names[original_type_name] = override.ovrd_type;
  end

endfunction


// set_inst_override (static)
// -----------------

function void ovm_factory::set_inst_override (string full_inst_path,
                                              string original_type_name,
                                              string override_type_name);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::set_inst_override() has been deprecated and replaced by ",
      "factory.set_inst_override_by_name()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  m_inst.set_inst_override_by_name (original_type_name, override_type_name, full_inst_path);
endfunction


// check_inst_override_exists
// --------------------------
function bit ovm_factory::check_inst_override_exists (ovm_object_wrapper original_type,
                                      ovm_object_wrapper override_type,
                                      string full_inst_path);
  ovm_factory_override override;
  ovm_factory_queue_class qc;

  if (m_inst_override_queues.exists(original_type))
    qc = m_inst_override_queues[original_type];
  else
    return 0;

  for (int index=0; index<qc.queue.size(); ++index) begin

    override = qc.queue[index]; 
    if (override.full_inst_path == full_inst_path &&
        override.orig_type == original_type &&
        override.ovrd_type == override_type &&
        override.orig_type_name == original_type.get_type_name()) begin
    ovm_report_info("DUPOVRD",{"Instance override for '",
       original_type.get_type_name(),"' already exists: override type '",
       override_type.get_type_name(),"' with full_inst_path '",
       full_inst_path,"'"},OVM_HIGH);
      return 1;
    end
  end
  return 0;
endfunction

// set_inst_override_by_type
// -------------------------

function void ovm_factory::set_inst_override_by_type (ovm_object_wrapper original_type,
                                                      ovm_object_wrapper override_type,
                                                      string full_inst_path);
  
  ovm_factory_override override;

  // register the types if not already done so
  if (!m_types.exists(original_type))
    register(original_type); 

  if (!m_types.exists(override_type))
    register(override_type); 

  if (check_inst_override_exists(original_type,override_type,full_inst_path))
    return;

  if(!m_inst_override_queues.exists(original_type))
    m_inst_override_queues[original_type] = new;

  override = new(.full_inst_path(full_inst_path),
                 .orig_type(original_type),
                 .orig_type_name(original_type.get_type_name()),
                 .ovrd_type(override_type));


  m_inst_override_queues[original_type].queue.push_back(override);

endfunction


// set_inst_override_by_name
// -------------------------

function void ovm_factory::set_inst_override_by_name (string original_type_name,
                                                      string override_type_name,
                                                      string full_inst_path);
  
  ovm_factory_override override;
  ovm_object_wrapper original_type=null;
  ovm_object_wrapper override_type=null;

  if(m_type_names.exists(original_type_name))
    original_type = m_type_names[original_type_name];

  if(m_type_names.exists(override_type_name))
    override_type = m_type_names[override_type_name];

  // check that type is registered with the factory
  if (override_type == null) begin
    ovm_report_error("TYPNTF", {"Cannot register instance override with type name '",
    original_type_name,"' and instance path '",full_inst_path,"' because the type it's supposed ",
    "to produce, '",override_type_name,"', is not registered with the factory."}, OVM_NONE);
    return;
  end

  if (original_type == null)
      m_lookup_strs[original_type_name] = 1;

  override = new(.full_inst_path(full_inst_path),
                 .orig_type(original_type),
                 .orig_type_name(original_type_name),
                 .ovrd_type(override_type));

  if(original_type != null) begin
    if (check_inst_override_exists(original_type,override_type,full_inst_path))
      return;
    if(!m_inst_override_queues.exists(original_type))
      m_inst_override_queues[original_type] = new;
    m_inst_override_queues[original_type].queue.push_back(override);
  end 
  else begin
    if(m_has_wildcard(original_type_name)) begin
       foreach(m_type_names[i]) begin
         if(ovm_is_match(original_type_name,i)) begin
           this.set_inst_override_by_name(i, override_type_name, full_inst_path);
         end
       end
       m_wildcard_inst_overrides.push_back(override);
    end
    else begin
      if(!m_inst_override_name_queues.exists(original_type_name))
        m_inst_override_name_queues[original_type_name] = new;
      m_inst_override_name_queues[original_type_name].queue.push_back(override);
    end
  end

endfunction

function bit ovm_factory::m_has_wildcard(string nm);
  foreach (nm[i]) 
    if(nm[i] == "*" || nm[i] == "?") return 1;
  return 0;
endfunction

// create_object (static)
// -------------

function ovm_object ovm_factory::create_object (string requested_type_name,  
                                                string parent_inst_path="", 
                                                string name="");
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::create_object() has been deprecated and replaced by ",
      "factory.create_object_by_name()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  return m_inst.create_object_by_name(requested_type_name, parent_inst_path, name);
endfunction


// create_object_by_name
// ---------------------

function ovm_object ovm_factory::create_object_by_name (string requested_type_name,  
                                                        string parent_inst_path="",  
                                                        string name=""); 

  ovm_object_wrapper wrapper;
  string inst_path;

  if (parent_inst_path == "")
    inst_path = name;
  else if (name != "")
    inst_path = {parent_inst_path,".",name};
  else
    inst_path = parent_inst_path;

  `ovm_clear_queue(m_override_info)

  wrapper = find_override_by_name(requested_type_name, inst_path);

  // if no override exists, try to use requested_type_name directly
  if (wrapper==null) begin
    if(!m_type_names.exists(requested_type_name)) begin
      ovm_report_warning("BDTYP",{"Cannot create an object of type '",
      requested_type_name,"' because it is not registered with the factory."}, OVM_NONE);
      return null;
    end
    wrapper = m_type_names[requested_type_name];
  end

  return wrapper.create_object(name);

endfunction


// create_object_by_type
// ---------------------

function ovm_object ovm_factory::create_object_by_type (ovm_object_wrapper requested_type,  
                                                        string parent_inst_path="",  
                                                        string name=""); 

  string full_inst_path;

  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  `ovm_clear_queue(m_override_info)

  requested_type = find_override_by_type(requested_type, full_inst_path);

  return requested_type.create_object(name);

endfunction


// create_component (static)
// ----------------

function ovm_component ovm_factory::create_component (string requested_type_name,  
                                                      string parent_inst_path="", 
                                                      string name, 
                                                      ovm_component parent);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::create_component() has been deprecated and replaced by ",
      "factory.create_component_by_name()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  return m_inst.create_component_by_name(requested_type_name, parent_inst_path, name, parent);
endfunction


// create_component_by_name
// ------------------------

function ovm_component ovm_factory::create_component_by_name (string requested_type_name,  
                                                              string parent_inst_path="",  
                                                              string name, 
                                                              ovm_component parent);
  ovm_object_wrapper wrapper;
  string inst_path;

  if (parent_inst_path == "")
    inst_path = name;
  else if (name != "")
    inst_path = {parent_inst_path,".",name};
  else
    inst_path = parent_inst_path;

  `ovm_clear_queue(m_override_info)

  wrapper = find_override_by_name(requested_type_name, inst_path);

  // if no override exists, try to use requested_type_name directly
  if (wrapper == null) begin
    if(!m_type_names.exists(requested_type_name)) begin 
      ovm_report_warning("BDTYP",{"Cannot create a component of type '",
      requested_type_name,"' because it is not registered with the factory."}, OVM_NONE);
      return null;
    end
    wrapper = m_type_names[requested_type_name];
  end

  return wrapper.create_component(name, parent);

endfunction


// create_component_by_type
// ------------------------

function ovm_component ovm_factory::create_component_by_type (ovm_object_wrapper requested_type,  
                                                            string parent_inst_path="",  
                                                            string name, 
                                                            ovm_component parent);
  string full_inst_path;

  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  `ovm_clear_queue(m_override_info)

  requested_type = find_override_by_type(requested_type, full_inst_path);

  return requested_type.create_component(name, parent);

endfunction



// find_by_name
// ------------

function ovm_object_wrapper ovm_factory::find_by_name(string type_name);

  if (m_type_names.exists(type_name))
    return m_type_names[type_name];

  ovm_report_warning("UnknownTypeName", {"find_by_name: Type name '",type_name,
      "' not registered with the factory."}, OVM_NONE);
  
endfunction


// find_override_by_name
// ---------------------

function ovm_object_wrapper ovm_factory::find_override_by_name (string requested_type_name,
                                                                string full_inst_path);
  ovm_object_wrapper rtype = null;
  ovm_factory_queue_class qc;

  ovm_object_wrapper override;

  if (m_type_names.exists(requested_type_name))
    rtype = m_type_names[requested_type_name];

/***
  if(rtype == null) begin
    if(requested_type_name != "") begin
      ovm_report_warning("TYPNTF", {"Requested type name ",
         requested_type_name, " is not registered with the factory. The instance override to ",
         full_inst_path, " is ignored"}, OVM_NONE);
    end
    m_lookup_strs[requested_type_name] = 1;
    return null;
  end
***/

  if (full_inst_path != "") begin
    if(rtype == null) begin
      if(m_inst_override_name_queues.exists(requested_type_name))
        qc = m_inst_override_name_queues[requested_type_name];
    end
    else begin
      if(m_inst_override_queues.exists(rtype))
        qc = m_inst_override_queues[rtype];
    end
    if(qc != null)
      for(int index = 0; index<qc.queue.size(); ++index) begin
        if (ovm_is_match(qc.queue[index].orig_type_name, requested_type_name) &&
            ovm_is_match(qc.queue[index].full_inst_path, full_inst_path)) begin
          m_override_info.push_back(qc.queue[index]);
          if (m_debug_pass) begin
            if (override == null) begin
              override = qc.queue[index].ovrd_type;
              qc.queue[index].selected = 1;
            end
          end
          else begin
            if (qc.queue[index].ovrd_type.get_type_name() == requested_type_name)
              return qc.queue[index].ovrd_type;
            else
              return find_override_by_type(qc.queue[index].ovrd_type,full_inst_path);
          end
        end
      end
  end

  if(rtype != null && !m_inst_override_queues.exists(rtype) && m_wildcard_inst_overrides.size()) begin
     m_inst_override_queues[rtype] = new;
     foreach (m_wildcard_inst_overrides[i]) begin
       if(ovm_is_match(m_wildcard_inst_overrides[i].orig_type_name, requested_type_name))
         m_inst_override_queues[rtype].queue.push_back(m_wildcard_inst_overrides[i]);
     end
  end

  // type override - exact match
  foreach (m_type_overrides[index])
    if (m_type_overrides[index].orig_type_name == requested_type_name) begin
      m_override_info.push_back(m_type_overrides[index]);
      if (m_debug_pass) begin
        if (override == null) begin
          override = m_type_overrides[index].ovrd_type;
          m_type_overrides[index].selected = 1;
        end
      end
      else begin
        return find_override_by_type(m_type_overrides[index].ovrd_type,full_inst_path);
      end
    end


  if (m_debug_pass && override != null)
    return find_override_by_type(override, full_inst_path);

  // No override found
  return null;


endfunction


// find_override_by_type
// ---------------------

function ovm_object_wrapper ovm_factory::find_override_by_type(ovm_object_wrapper requested_type,
                                                               string full_inst_path);

  ovm_object_wrapper override;
  ovm_factory_queue_class qc = null;
  if (m_inst_override_queues.exists(requested_type))
    qc = m_inst_override_queues[requested_type];

  foreach (m_override_info[index]) begin
    if ( //index != m_override_info.size()-1 &&
       m_override_info[index].orig_type == requested_type) begin
      ovm_report_error("OVRDLOOP", "Recursive loop detected while finding override.", OVM_NONE);
      if (!m_debug_pass)
        debug_create_by_type (requested_type, full_inst_path);

      return requested_type;
    end
  end

  // inst override; return first match; takes precedence over type overrides
  if (full_inst_path != "" && qc != null)
    for (int index = 0; index < qc.queue.size(); ++index) begin
      if ((qc.queue[index].orig_type == requested_type ||
           (qc.queue[index].orig_type_name != "<unknown>" &&
            qc.queue[index].orig_type_name != "" &&
            qc.queue[index].orig_type_name == requested_type.get_type_name())) &&
          ovm_is_match(qc.queue[index].full_inst_path, full_inst_path)) begin
        m_override_info.push_back(qc.queue[index]);
        if (m_debug_pass) begin
          if (override == null) begin
            override = qc.queue[index].ovrd_type;
            qc.queue[index].selected = 1;
          end
        end
        else begin
          if (qc.queue[index].ovrd_type == requested_type)
            return requested_type;
          else
            return find_override_by_type(qc.queue[index].ovrd_type,full_inst_path);
        end
      end
    end

  // type override - exact match
  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type == requested_type ||
        (m_type_overrides[index].orig_type_name != "<unknown>" &&
         m_type_overrides[index].orig_type_name != "" &&
         requested_type != null &&
         m_type_overrides[index].orig_type_name == requested_type.get_type_name())) begin
      m_override_info.push_back(m_type_overrides[index]);
      if (m_debug_pass) begin
        if (override == null) begin
          override = m_type_overrides[index].ovrd_type;
          m_type_overrides[index].selected = 1;
        end
      end
      else begin
        if (m_type_overrides[index].ovrd_type == requested_type)
          return requested_type;
        else
          return find_override_by_type(m_type_overrides[index].ovrd_type,full_inst_path);
      end
    end
  end

  // type override with wildcard match
  //foreach (m_type_overrides[index])
  //  if (ovm_is_match(index,requested_type.get_type_name())) begin
  //    m_override_info.push_back(m_inst_overrides[index]);
  //    return find_override_by_type(m_type_overrides[index],full_inst_path);
  //  end

  if (m_debug_pass && override != null)
    if (override == requested_type)
      return requested_type;
    else
      return find_override_by_type(override,full_inst_path);

  return requested_type;

endfunction


// print_all_overrides (static)
// -------------------

function void  ovm_factory::print_all_overrides (int all_types=0);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::print_all_overrides() has been deprecated and replaced by ",
      "factory.print()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  m_inst.print(all_types);
endfunction


// print
// -----

function void ovm_factory::print (int all_types=1);

  string key;
  ovm_factory_queue_class sorted_override_queues[string];

  string tmp;
  int id=0;
  ovm_object_wrapper obj;

  //sort the override queues
  foreach (m_inst_override_queues[i]) begin
    obj = i;
    tmp = obj.get_type_name();
    if(tmp == "") $swrite(tmp, "__unnamed_id_%0d", id++);
    sorted_override_queues[tmp] = m_inst_override_queues[i];

  end
  foreach (m_inst_override_name_queues[i]) begin
    sorted_override_queues[i] = m_inst_override_name_queues[i];
  end

  $display("\n#### Factory Configuration (*)\n");

  // print instance overrides
  if(!m_type_overrides.size() && !sorted_override_queues.num())
    $display("  No instance or type overrides are registered with this factory");
  else begin
    int max1,max2,max3;
    string dash = "---------------------------------------------------------------------------------------------------";
    string space= "                                                                                                   ";

    // print instance overrides
    if(!sorted_override_queues.num())
      $display("No instance overrides are registered with this factory");
    else begin
      foreach(sorted_override_queues[j]) begin
        ovm_factory_queue_class qc = sorted_override_queues[j];
        for (int i=0; i<qc.queue.size(); ++i) begin
          if (qc.queue[i].orig_type_name.len() > max1)
            max1=qc.queue[i].orig_type_name.len();
          if (qc.queue[i].full_inst_path.len() > max2)
            max2=qc.queue[i].full_inst_path.len();
          if (qc.queue[i].ovrd_type_name.len() > max3)
            max3=qc.queue[i].ovrd_type_name.len();
        end
      end
      if (max1 < 14) max1 = 14;
      if (max2 < 13) max2 = 13;
      if (max3 < 13) max3 = 13;

      $display("Instance Overrides:\n");
      $display("  %0s%0s  %0s%0s  %0s%0s","Requested Type",space.substr(1,max1-14),
                                          "Override Path", space.substr(1,max2-13),
                                          "Override Type", space.substr(1,max3-13));
      $display("  %0s  %0s  %0s",dash.substr(1,max1),
                                 dash.substr(1,max2),
                                 dash.substr(1,max3));

      foreach(sorted_override_queues[j]) begin
        ovm_factory_queue_class qc = sorted_override_queues[j];
        for (int i=0; i<qc.queue.size(); ++i) begin
          $write("  %0s%0s",qc.queue[i].orig_type_name,
                 space.substr(1,max1-qc.queue[i].orig_type_name.len()));
          $write("  %0s%0s",  qc.queue[i].full_inst_path,
                 space.substr(1,max2-qc.queue[i].full_inst_path.len()));
          $display("  %0s",     qc.queue[i].ovrd_type_name);
        end
      end
    end

    // print type overrides
    if (!m_type_overrides.size())
      $display("\nNo type overrides are registered with this factory");
    else begin
      foreach (m_type_overrides[i]) begin
        if (m_type_overrides[i].orig_type_name.len() > max1)
          max1=m_type_overrides[i].orig_type_name.len();
        if (m_type_overrides[i].ovrd_type_name.len() > max3)
          max2=m_type_overrides[i].ovrd_type_name.len();
      end
      if (max1 < 14) max1 = 14;
      if (max2 < 13) max2 = 13;
      $display("\nType Overrides:\n");
      $display("  %0s%0s  %0s%0s","Requested Type",space.substr(1,max1-14),
                                  "Override Type", space.substr(1,max2-13));
      $display("  %0s  %0s",dash.substr(1,max1),
                            dash.substr(1,max2));
      foreach (m_type_overrides[index]) 
        $display("  %0s%0s  %0s",
                 m_type_overrides[index].orig_type_name,
                 space.substr(1,max1-m_type_overrides[index].orig_type_name.len()),
                 m_type_overrides[index].ovrd_type_name);
    end
  end

  // print all registered types, if all_types >= 1 
  if (all_types >= 1 && m_type_names.first(key)) begin
    bit banner;
    $display("\nAll types registered with the factory: %0d total",m_types.num());
    $display("(types without type names will not be printed)\n");
    do begin
      // filter out ovm_ classes (if all_types<2) and non-types (lookup strings)
      if (!(all_types < 2 && ovm_is_match("ovm_*",
           m_type_names[key].get_type_name())) &&
           key == m_type_names[key].get_type_name()) begin
        if (!banner) begin
          $display("  Type Name");
          $display("  ---------");
          banner=1;
        end
        $display("  ", m_type_names[key].get_type_name());
      end
    end while(m_type_names.next(key));
  end

  $display("(*) Types with no associated type name will be printed as <unknown>");

  $display("\n####\n");

endfunction


// print_override_info (static)
// -------------------

function void  ovm_factory::print_override_info (string requested_type_name,
                                                 string parent_inst_path="",
                                                 string name="");
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_factory::print_override_info() has been deprecated and replaced by ",
      "factory.debug_create_by_name()"}, OVM_NONE);
  end
  m_inst = ovm_factory::get();
  m_inst.m_debug_create(requested_type_name, null, parent_inst_path, name);
endfunction


// debug_create_by_name
// --------------------

function void  ovm_factory::debug_create_by_name (string requested_type_name,
                                                  string parent_inst_path="",
                                                  string name="");
  m_debug_create(requested_type_name, null, parent_inst_path, name);
endfunction


// debug_create_by_type
// --------------------

function void  ovm_factory::debug_create_by_type (ovm_object_wrapper requested_type,
                                                  string parent_inst_path="",
                                                  string name="");
  m_debug_create("", requested_type, parent_inst_path, name);
endfunction


// m_debug_create
// --------------

function void  ovm_factory::m_debug_create (string requested_type_name,
                                            ovm_object_wrapper requested_type,
                                            string parent_inst_path,
                                            string name);

  string full_inst_path;
  ovm_object_wrapper result;
  
  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  `ovm_clear_queue(m_override_info)

  if (requested_type == null) begin
    if (!m_type_names.exists(requested_type_name) &&
      !m_lookup_strs.exists(requested_type_name)) begin
      ovm_report_warning("Factory Warning", {"The factory does not recognize '",
        requested_type_name,"' as a registered type."}, OVM_NONE);
      return;
    end
    m_debug_pass = 1;
    
    result = find_override_by_name(requested_type_name,full_inst_path);
  end
  else begin
    m_debug_pass = 1;
    if (!m_types.exists(requested_type))
      register(requested_type); 
    result = find_override_by_type(requested_type,full_inst_path);
    if (requested_type_name == "")
      requested_type_name = requested_type.get_type_name();
  end

  m_debug_display(requested_type_name, result, full_inst_path);
  m_debug_pass = 0;

  foreach (m_override_info[index])
    m_override_info[index].selected = 0;

endfunction


// m_debug_display
// ---------------

function void  ovm_factory::m_debug_display (string requested_type_name,
                                             ovm_object_wrapper result,
                                             string full_inst_path);

  int    max1,max2,max3;
  string dash = "---------------------------------------------------------------------------------------------------";
  string space= "                                                                                                   ";

  $display("\n#### Factory Override Information (*)\n");
  $write("Given a request for an object of type '",requested_type_name,
         "' with an instance\npath of '",full_inst_path,
         "', the factory encountered\n");

  if (m_override_info.size() == 0)
    $display("no relevant overrides.\n");
  else begin

    $display("the following relevant overrides. An 'x' next to a match indicates a",
             "\nmatch that was ignored.\n");

    foreach (m_override_info[i]) begin
      if (m_override_info[i].orig_type_name.len() > max1)
        max1=m_override_info[i].orig_type_name.len();
      if (m_override_info[i].full_inst_path.len() > max2)
        max2=m_override_info[i].full_inst_path.len();
      if (m_override_info[i].ovrd_type_name.len() > max3)
        max3=m_override_info[i].ovrd_type_name.len();
    end

    if (max1 < 13) max1 = 13;
    if (max2 < 13) max2 = 13;
    if (max3 < 13) max3 = 13;

    $display("  %0s%0s", "Original Type", space.substr(1,max1-13),
             "  %0s%0s", "Instance Path", space.substr(1,max2-13),
             "  %0s%0s", "Override Type", space.substr(1,max3-13));

    $display("  %0s  %0s  %0s",dash.substr(1,max1),
                               dash.substr(1,max2),
                               dash.substr(1,max3));

    foreach (m_override_info[i]) begin
      $write("%s%0s%0s",
             m_override_info[i].selected ? "  " : "x ",
             m_override_info[i].orig_type_name,
             space.substr(1,max1-m_override_info[i].orig_type_name.len()));
      $write("  %0s%0s", m_override_info[i].full_inst_path,
             space.substr(1,max2-m_override_info[i].full_inst_path.len()));
      $write("  %0s%0s", m_override_info[i].ovrd_type_name,
             space.substr(1,max3-m_override_info[i].ovrd_type_name.len()));
      if (m_override_info[i].full_inst_path == "*")
        $display("  <type override>");
      else
        $display();
    end
    $display();
  end


  $display("Result:\n");
  $display("  The factory will produce an object of type '%0s'", 
           result == null ? requested_type_name : result.get_type_name());

  $display("\n(*) Types with no associated type name will be printed as <unknown>");

  $display("\n####\n");

endfunction


