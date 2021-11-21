//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TUE_COMPONENT_BASE_SVH
`define TUE_COMPONENT_BASE_SVH
virtual class tue_component_base #(
  type  BASE          = uvm_component,
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends BASE;
  protected CONFIGURATION configuration;
  protected STATUS        status;

  function void apply_config_settings(bit verbose = 0);
    super.apply_config_settings(verbose);
    m_get_configuration();
    m_get_status();
  endfunction

  virtual function void set_configuration(tue_configuration configuration);
    if (!$cast(this.configuration, configuration)) begin
      `uvm_fatal(get_name(), "Error casting configuration object")
    end
  endfunction

  virtual function CONFIGURATION get_configuration();
    return configuration;
  endfunction

  virtual function void set_status(tue_status status);
    if (!$cast(this.status, status)) begin
      `uvm_fatal(get_name(), "Error casting status object")
    end
  endfunction

  virtual function STATUS get_status();
    return status;
  endfunction

  virtual function void set_context(tue_configuration configuration, tue_status status);
    set_configuration(configuration);
    set_status(status);
  endfunction

  virtual protected function void m_get_configuration();
    if (configuration != null) begin
      return;
    end
    if (tue_check_type(CONFIGURATION::get_type(), tue_configuration_dummy::get_type())) begin
      return;
    end

    void'(uvm_config_db#(CONFIGURATION)::get(this, "", "configuration", configuration));
    if (configuration == null) begin
      void'(uvm_config_db#(CONFIGURATION)::get(null, "", "configuration", configuration));
    end
    if (configuration == null) begin
      create_configuration();
    end
    if (configuration == null) begin
      `uvm_fatal(get_name(), "Configuration object is not set")
    end
  endfunction

  virtual protected function void create_configuration();
    return;
  endfunction

  virtual protected function void m_get_status();
    if (status != null) begin
      return;
    end
    if (tue_check_type(STATUS::get_type(), tue_status_dummy::get_type())) begin
      return;
    end

    void'(uvm_config_db#(STATUS)::get(this, "", "status", status));
    if (status == null) begin
      void'(uvm_config_db#(STATUS)::get(null, "", "status", status));
    end
    if (status == null) begin
      create_status();
    end
    if (status == null) begin
      `uvm_fatal(get_name(), "Status object is not set")
    end
  endfunction

  virtual protected function void create_status();
    status  = STATUS::type_id::create("status");
  endfunction

  `tue_component_default_constructor(tue_component_base)
endclass
`endif
