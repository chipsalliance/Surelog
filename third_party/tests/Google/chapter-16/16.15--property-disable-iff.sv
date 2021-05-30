// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: property_disable_iff_test
:description: property with disable iff
:type: simulation parsing
:tags: 16.15
*/

module clk_gen(
    input      rst,
    input      clk,
    output reg out
);

    initial begin
        out = 0;
    end

    always @(posedge clk or posedge rst) begin
        if (rst)
            out <= 0;
        else
            out <= 1;
    end

endmodule: clk_gen

module top();

    logic rst;
    logic clk;
    logic out;

    clk_gen dut(.rst(rst), .clk(clk), .out(out));

    initial begin
        clk   = 0;
        rst   = 1;
    end

    property prop;
        @(posedge clk) disable iff (rst) out;
    endproperty

    assert property (prop) else $error($sformatf("property check failed :assert: (False)"));

    initial begin
        forever begin
            #(50) clk = ~clk;
        end
    end

    initial #1000 $finish;

endmodule
