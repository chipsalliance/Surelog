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
 * NAME:        svaunit_ts.sv
 * PROJECT:     __if_svaunit__
 * Description: SVAUnit test suite template
 *******************************************************************************/

`ifndef ____IF_SVAUNIT___TS_SV
`define ____IF_SVAUNIT___TS_SV

`include  "sv/svaunit_pkg.sv"
import svaunit_pkg::*;

// Unit test suite for those tests which verify after reset SVA
class svaunit_ts extends svaunit_test_suite;
    `uvm_component_utils(svaunit_ts)

    /* Constructor for svaunit_ts
     * @param name   : instance name for svaunit_ts object
     * @param parent : hierarchical parent for svaunit_ts
     */
    function new(input string name = "svaunit_ts", input uvm_component parent);
        super.new(name, parent);
    endfunction

    /* Build phase method used to instantiate components
     * @param phase : the phase scheduled for build_phase method
     */
    function void build_phase(input uvm_phase phase);
        super.build_phase(phase);

        // TODO : Register unit tests or sequences to test suite using `add_test(test_or_seq_type) macro
    endfunction
endclass

`endif
