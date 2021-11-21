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
`ifndef TUE_CONFIGURATION_SVH
`define TUE_CONFIGURATION_SVH
virtual class tue_configuration extends uvm_object;
  `tue_object_default_constructor(tue_configuration)
endclass

class tue_configuration_dummy extends tue_configuration;
  `tue_object_default_constructor(tue_configuration_dummy)
  `uvm_object_utils(tue_configuration_dummy)
endclass
`endif
