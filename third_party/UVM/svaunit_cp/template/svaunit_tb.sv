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
 * NAME:        svaunit_tb.sv
 * PROJECT:     __if_svaunit__
 * Description: SVAUnit testbench template
 *******************************************************************************/

`ifndef ____IF_SVAUNIT___TB
`define ____IF_SVAUNIT___TB

// SVAUnit testbench template
module __if_svaunit___tb;
    // Enable SVAUNIT
    `SVAUNIT_UTILS

    reg clock;

    // TODO : Instantiate interface here

    initial begin
        // TODO : Register virtual interface to config_db
    end

    initial begin
        // Start test specified with UVM_TESTNAME
        run_test();
    end

    // Set clock initial values
    initial begin
        clock = 1'b0;
    end

    // Clock generation
    always #1 clock = ~clock;

endmodule

`endif
