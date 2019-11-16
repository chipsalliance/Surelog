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
 * NAME:        svaunit_seq.sv
 * PROJECT:     __if_svaunit__
 * Description: SVAUnit test template
 *******************************************************************************/

`ifndef ____IF_SVAUNIT___SEQ_SV
`define ____IF_SVAUNIT___SEQ_SV

`include  "sv/svaunit_pkg.sv"
import svaunit_pkg::*;

// SVAUnit test template
class svaunit_seq extends svaunit_base_sequence;
   `uvm_object_utils(svaunit_seq)

   // TODO : Add virtual interface

   /* Constructor for an svaunit_seq
    * @param name   : instance name for svaunit_seq object
    */
   function new(string name = "svaunit_seq");
      super.new(name);

   // TODO : Get the virtual interface from UVM config db
   endfunction

   virtual task pre_body();
      super.pre_body();

   // TODO : Initialize signals
   endtask

   virtual task body();
   // TODO : Create scenarios for an SVA
   endtask
endclass

`endif

