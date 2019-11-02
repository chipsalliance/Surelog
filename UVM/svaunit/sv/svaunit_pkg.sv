/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        svaunit_pkg.sv
 * PROJECT:     svaunit
 * Description: SVAUnit PACKAGE
 *******************************************************************************/

`ifndef SVAUNIT_PKG_SV
`define SVAUNIT_PKG_SV

package svaunit_pkg;
   // UVM package
   import uvm_pkg::*;

// Defines UVM macros
`include  "uvm_macros.svh"

// Define SVAUnit reporter
`include  "svaunit_reporter.svh"

// Definitions of SVAUnit macros
`include  "svaunit_defines.svh"

// Definitions of SVAUnit versions macros
`include  "svaunit_version_defines.svh"

// Definitions of SVAUnit types
`include  "svaunit_types.svh"

// Definition of immediate assertion details
`include  "svaunit_concurrent_assertion_details.svh"

// Definition of immediate assertion info
`include  "svaunit_concurrent_assertion_info.svh"

// Definition of SVA details
`include  "svaunit_immediate_assertion_details.svh"

// Definition of SVA info
`include  "svaunit_immediate_assertion_info.svh"

// Definition of SVAUnit VPI wrapper class
`include  "svaunit_vpi_wrapper.svh"

// Definition of SVAUnit base class
`include  "svaunit_base.svh"

// Definition of SVAUnit virtual sequencer class and definition of SVAUnit base sequence class
`include  "svaunit_sequence.svh"

// Definition of SVAUnit test class
`include  "svaunit_test.svh"

// Definition of SVAUnit test class which starts a sequence
`include  "svaunit_sequence_test.svh"

// Definition of SVAUnit test suite class
`include  "svaunit_test_suite.svh"

endpackage

`endif
