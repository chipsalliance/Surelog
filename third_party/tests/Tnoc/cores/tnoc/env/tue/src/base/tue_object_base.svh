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
`ifndef TUE_OBJECT_BASE_SVH
`define TUE_OBJECT_BASE_SVH
virtual class tue_object_base #(
  type  BASE          = uvm_object,
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends BASE;
  protected CONFIGURATION configuration;
  protected STATUS        status;

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

  `tue_object_default_constructor(tue_object_base)
  `uvm_field_utils_begin(tue_object_base #(BASE, CONFIGURATION, STATUS))
    `uvm_field_object(configuration, UVM_REFERENCE | UVM_PACK | UVM_NOCOMPARE | UVM_NOPRINT | UVM_NORECORD)
    `uvm_field_object(status, UVM_REFERENCE | UVM_PACK | UVM_NOCOMPARE | UVM_NOPRINT | UVM_NORECORD)
  `uvm_field_utils_end
endclass
`endif
