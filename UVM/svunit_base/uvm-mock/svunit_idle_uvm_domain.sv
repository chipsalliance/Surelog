//###############################################################
//
//  Licensed to the Apache Software Foundation (ASF) under one
//  or more contributor license agreements.  See the NOTICE file
//  distributed with this work for additional information
//  regarding copyright ownership.  The ASF licenses this file
//  to you under the Apache License, Version 2.0 (the
//  "License"); you may not use this file except in compliance
//  with the License.  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing,
//  software distributed under the License is distributed on an
//  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
//  KIND, either express or implied.  See the License for the
//  specific language governing permissions and limitations
//  under the License.
//
//###############################################################

`ifndef __SVUNIT_UVM_DOMAIN_SV__
`define __SVUNIT_UVM_DOMAIN_SV__

import uvm_pkg::*;

typedef class svunit_idle_uvm_component;
typedef class svunit_idle_uvm_domain;


//----------------------------------------------------
// global helper functions to activate and deactivate
// components
//----------------------------------------------------
function void svunit_activate_uvm_component(uvm_component c);
  c.set_domain(uvm_domain::get_uvm_domain(), 1);
endfunction

function void svunit_deactivate_uvm_component(uvm_component c);
  c.set_domain(svunit_idle_uvm_domain::get_svunit_domain(), 1);
endfunction

//---------------------------------------------------
// this is the idle domain that where components are
// assigned for deactivation
//---------------------------------------------------

class svunit_idle_uvm_domain extends uvm_domain;
  //-------------------------------------------
  // new svunit domain and scheduler instances
  //-------------------------------------------
  static local uvm_domain m_svunit_domain;
  static local uvm_phase  m_svunit_schedule;

  //--------------------------------------------
  // override the get_common_domain to register
  // the svunit_domain
  //--------------------------------------------
  static function uvm_domain get_common_domain();
    uvm_domain common;
    uvm_domain domain;

    common = uvm_domain::get_common_domain();

    domain = get_svunit_domain();
    common.add(domain,
               .with_phase(common.find(uvm_run_phase::get())));

    return common;
  endfunction

  //----------------------------------------------
  // static function that returns a handle to the
  // new svunit domain
  //----------------------------------------------
  static function uvm_domain get_svunit_domain();
    if (m_svunit_domain == null) begin
      svunit_idle_uvm_component master_idle_component;

      m_svunit_domain = new("svunit_domain");
      m_svunit_schedule = new("svunit_sched", UVM_PHASE_SCHEDULE);
      add_uvm_phases(m_svunit_schedule);
      m_svunit_domain.add(m_svunit_schedule);

      master_idle_component = svunit_idle_uvm_component::type_id::create("svunit_idle_uvm_component", null);
      master_idle_component.set_domain(m_svunit_domain);
    end
    return m_svunit_domain;
  endfunction

  function new(string name);
    super.new(name);
  endfunction
endclass

const uvm_domain _idle_domain = svunit_idle_uvm_domain::get_svunit_domain();

//---------------------------------------------------------
// the purpose of this component is to raise an objections
// at pre_reset so that other components registered to the
// same domain never proceed beyond that point
//---------------------------------------------------------
class svunit_idle_uvm_component extends uvm_component;
  `uvm_component_utils(svunit_idle_uvm_component)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void phase_started(uvm_phase phase);
    if (phase.get_name() == "pre_reset") begin
      phase.raise_objection(null);
    end
  endfunction
endclass


`endif
