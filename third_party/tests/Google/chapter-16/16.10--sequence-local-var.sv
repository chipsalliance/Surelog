// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sequence_local_var_test
:description: sequence with local variables
:type: simulation parsing
:tags: 16.10
*/

module clk_gen(
    input            valid,
    input            clk,
    output reg [7:0] out,
    input      [7:0] in
);

    reg [7:0] data_reg_0;
    reg [7:0] data_reg_1;
    reg [7:0] data_reg_2;

    initial begin
        data_reg_0 = 0;
        data_reg_1 = 0;
        data_reg_2 = 0;
        out        = 0;
    end

    always @(posedge clk) begin
        if (valid) begin
            data_reg_0 <= in + 1;
            data_reg_1 <= data_reg_0 + 1;
            data_reg_2 <= data_reg_1 + 1;
            out        <= data_reg_2 + 1;
        end
    end

endmodule: clk_gen

module top();

    int         cycle;
    logic       valid;
    logic       clk;
    logic [7:0] out;
    logic [7:0] in;

    clk_gen dut(.valid(valid), .clk(clk), .out(out), .in(in));

    initial begin
        cycle = 0;
        clk   = 0;
        valid = 1;
    end

    sequence seq;
        int x;
        @(posedge clk) (valid, x = in) ##4 (out == x + 4);
    endsequence

    assert property (seq) else $error($sformatf("sequence check failed :assert: (False)"));

    assign in = cycle;

    always @(posedge clk)
        cycle = cycle + 1;

    initial begin
        forever begin
            #(50) clk = ~clk;
        end
    end

    initial #1000 $finish;

endmodule
