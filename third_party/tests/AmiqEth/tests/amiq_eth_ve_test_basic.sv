/******************************************************************************
 * (C) Copyright 2014 AMIQ Consulting
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
 * NAME:        amiq_eth_ve_test_basic.sv
 * PROJECT:     amiq_eth
 * Description: This file declares the basic test class from which all tests will inherit.
 *******************************************************************************/

`ifndef __AMIQ_ETH_VE_TEST_BASIC
    //protection against multiple includes
    `define __AMIQ_ETH_VE_TEST_BASIC
   
//basic test class for running the tests of amiq_eth package
class amiq_eth_ve_test_basic extends uvm_test;
    `uvm_component_utils(amiq_eth_ve_test_basic)
    
    //ethernet verification environment
    amiq_eth_ve_env env;
    
    //constructor
    //@param name - name of the component instance
    //@param parent - parent of the component instance
    function new(string name = "", uvm_component parent);
        super.new(name, parent);    
    endfunction
    
    //UVM build phase
    //@param phase - current phase
    function void build_phase(uvm_phase phase);
        env = amiq_eth_ve_env::type_id::create("env", this);
    endfunction
endclass

`endif
    