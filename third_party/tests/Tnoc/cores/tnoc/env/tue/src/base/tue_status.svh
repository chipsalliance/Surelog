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
`ifndef TUE_STATUS_SVH
`define TUE_STATUS_SVH
virtual class tue_status extends uvm_object;
  `tue_object_default_constructor(tue_status)
endclass

class tue_status_dummy extends tue_status;
  `tue_object_default_constructor(tue_status_dummy)
  `uvm_object_utils(tue_status_dummy)
endclass
`endif
