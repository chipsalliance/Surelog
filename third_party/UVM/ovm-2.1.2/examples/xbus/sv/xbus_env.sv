// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus_env.sv#1 $
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

`ifndef XBUS_ENV_SV
`define XBUS_ENV_SV

//------------------------------------------------------------------------------
//
// CLASS: xbus_env
//
//------------------------------------------------------------------------------

class xbus_env extends ovm_env;

  // Virtual Interface variable
  protected virtual interface xbus_if xi0;

  // Control properties
  protected bit has_bus_monitor = 1;
  protected int unsigned num_masters = 0;
  protected int unsigned num_slaves = 0;

  // The following two bits are used to control whether checks and coverage are
  // done both in the bus monitor class and the interface.
  bit intf_checks_enable = 1; 
  bit intf_coverage_enable = 1;

  // Components of the environment
  xbus_bus_monitor bus_monitor;
  xbus_master_agent masters[];
  xbus_slave_agent slaves[];

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils_begin(xbus_env)
    `ovm_field_int(has_bus_monitor, OVM_ALL_ON)
    `ovm_field_int(num_masters, OVM_ALL_ON)
    `ovm_field_int(num_slaves, OVM_ALL_ON)
    `ovm_field_int(intf_checks_enable, OVM_ALL_ON)
    `ovm_field_int(intf_coverage_enable, OVM_ALL_ON)
  `ovm_component_utils_end

  // new - constructor
  function new(string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  // build
  function void build();
    string inst_name;
    super.build();
    if(has_bus_monitor == 1) begin
      bus_monitor = xbus_bus_monitor::type_id::create("bus_monitor", this);
    end
    masters = new[num_masters];
    for(int i = 0; i < num_masters; i++) begin
      $sformat(inst_name, "masters[%0d]", i);
      masters[i] = xbus_master_agent::type_id::create(inst_name, this);
      set_config_int({inst_name, "*"}, "master_id", i);
    end
    slaves = new[num_slaves];
    for(int i = 0; i < num_slaves; i++) begin
      $sformat(inst_name, "slaves[%0d]", i);
      slaves[i] = xbus_slave_agent::type_id::create(inst_name, this);
    end
  endfunction : build

  // set_slave_address_map
  function void set_slave_address_map(string slave_name, 
    int min_addr, int max_addr);
    xbus_slave_monitor tmp_slave_monitor;
    if( bus_monitor != null ) begin
      // Set slave address map for bus monitor
      bus_monitor.set_slave_configs(slave_name, min_addr, max_addr);
    end
    // Set slave address map for slave monitor
    $cast(tmp_slave_monitor, lookup({slave_name, ".monitor"}));
    tmp_slave_monitor.set_addr_range(min_addr, max_addr);
  endfunction : set_slave_address_map

  // Function to assign the virtual intf for all components in this env
  function void assign_vi(virtual interface xbus_if xi);
    xi0 = xi;
    if( bus_monitor != null) begin
      bus_monitor.assign_vi(xi);
    end
    for(int i = 0; i < num_masters; i++) begin
      masters[i].assign_vi(xi);
    end
    for(int i = 0; i < num_slaves; i++) begin
      slaves[i].assign_vi(xi);
    end
  endfunction : assign_vi

  // update_vif_enables
  protected task update_vif_enables();
    forever begin
      @(intf_checks_enable || intf_coverage_enable);
      xi0.has_checks <= intf_checks_enable;
      xi0.has_coverage <= intf_coverage_enable;
    end
  endtask : update_vif_enables

  // implement run task
  task run;
    fork
      update_vif_enables();
    join
  endtask : run

endclass : xbus_env

`endif // XBUS_ENV_SVH

