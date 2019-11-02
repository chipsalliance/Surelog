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

//------------------------------------------------------------------------------
//
// MACRO- apply_request_with
//
//------------------------------------------------------------------------------

`define apply_request_with(OVM_DATA_REQ, CONSTRAINTS) \
  wait_for_grant();\
  pre_apply(); \
  if (! OVM_DATA_REQ.randomize() with CONSTRAINTS ) begin \
    ovm_report_warning("ovm_scenario", "Randomization failed in apply_request_with"); \
  end\
  mid_apply();

//------------------------------------------------------------------------------
//
// MACRO- apply_with
//
//------------------------------------------------------------------------------

`define apply_with(OVM_DATA_REQ, OVM_DATA_RSP, CONSTRAINTS) \
  `apply_request_with(OVM_DATA_REQ, CONSTRAINTS) \
  send_request(OVM_DATA_REQ); \
  get_response(OVM_DATA_RSP); \
  post_apply();

//------------------------------------------------------------------------------
//
// MACRO- apply_send_with
//
//------------------------------------------------------------------------------

`define apply_send_with(OVM_DATA_REQ, CONSTRAINTS) \
  `apply_request_with(OVM_DATA_REQ, CONSTRAINTS); \
  send_request(OVM_DATA_REQ); \
  post_apply();

  
