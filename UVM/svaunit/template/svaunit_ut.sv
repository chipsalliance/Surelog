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
 * NAME:        svaunit_ut.sv
 * PROJECT:     __if_svaunit__
 * Description: SVAUnit test template
 *******************************************************************************/

`ifndef ____IF_SVAUNIT___SV
//protection against multiple includes
`define ____IF_SVAUNIT___SV

`include  "sv/svaunit_pkg.sv"
import svaunit_pkg::*;

// SVAUnit test template
class svaunit_ut extends svaunit_test;
    `uvm_component_utils(svaunit_ut)

    // TODO : Add virtual interface

    /* Constructor for svaunit_ut
     * @param name   : instance name for svaunit_ut object
     * @param parent : hierarchical parent for svaunit_ut
     */
    function new(string name = "svaunit_ut", uvm_component parent);
        super.new(name, parent);
    endfunction

    /* Build phase method used to instantiate components
     * @param phase : the phase scheduled for build_phase method
     */
    function void build_phase(input uvm_phase phase);
        super.build_phase(phase);

        // TODO : Get the virtual interface from UVM config db
    endfunction

    task test();
        // TODO : Create scenarios for an SVA
    endtask
endclass

`endif
