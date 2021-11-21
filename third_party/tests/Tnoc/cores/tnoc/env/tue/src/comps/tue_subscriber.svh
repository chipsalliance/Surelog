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
`ifndef TUE_SUBSCRIBER_SVH
`define TUE_SUBSCRIBER_SVH
virtual class tue_subscriber #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  T             = int
) extends tue_component_base #(uvm_subscriber #(T), CONFIGURATION, STATUS);
  `tue_component_default_constructor(tue_subscriber)
endclass
`endif
