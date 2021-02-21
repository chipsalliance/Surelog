
/*============================================================================

This Verilog source file is part of the Berkeley HardFloat IEEE Floating-Point
Arithmetic Package, Release 1, by John R. Hauser.

Copyright 2019 The Regents of the University of California.  All rights
reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice,
    this list of conditions, and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions, and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 3. Neither the name of the University nor the names of its contributors may
    be used to endorse or promote products derived from this software without
    specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS", AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE
DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

=============================================================================*/

`include "HardFloat_consts.vi"
`include "HardFloat_specialize.vi"

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module test_compareRecFN#(parameter expWidth = 3, parameter sigWidth = 3);

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    parameter maxNumErrors = 20;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam formatWidth = expWidth + sigWidth;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg signaling;
    reg [1:0] op;
    reg [2*8:1] opName;
    reg [(formatWidth - 1):0] a, b;
    reg expectOut;
    reg [4:0] expectExceptionFlags;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recA, recB;
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_a(a, recA);
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_b(b, recB);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire lt, eq, gt, unordered;
    wire [4:0] exceptionFlags;
    compareRecFN#(expWidth, sigWidth)
        compareRecFN(
            recA, recB, signaling, lt, eq, gt, unordere, exceptionFlags);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount, out;
    initial begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fwrite('h80000002, "Testing 'compareRecF%0d'", formatWidth);
        if (
            ($fscanf('h80000000, "%h %h", signaling, op) < 2) || (op == 3)
        ) begin
            $fdisplay('h80000002, ".\n--> Invalid test-cases input.");
            `finish_fail;
        end
        if (op == 0) begin
            opName = "lt";
        end else if (op == 1) begin
            opName = "le";
        end else begin
            opName = "eq";
        end
        $fdisplay('h80000002, ", signaling %0d, op %s:", signaling, opName);
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        errorCount = 0;
        count = 0;
        partialCount = 0;
        begin :TestLoop
            while (
                $fscanf(
                    'h80000000,
                    "%h %h %h %h",
                    a,
                    b,
                    expectOut,
                    expectExceptionFlags
                ) == 4
            ) begin
                #1;
                partialCount = partialCount + 1;
                if (partialCount == 10000) begin
                    count = count + 10000;
                    $fdisplay('h80000002, "%0d...", count);
                    partialCount = 0;
                end
                out =
                       ((op == 0) && lt)
                    || ((op == 1) && (lt || eq))
                    || ((op == 2) && eq);
                if (
                    (out != expectOut)
                        || (exceptionFlags !== expectExceptionFlags)
                ) begin
                    if (errorCount == 0) begin
                        $display(
                     "Errors found in 'compareRecF%0d', signaling %0d, op %s:",
                            formatWidth,
                            signaling,
                            opName
                        );
                    end
                    $write(
                        "%H %H  => %0d %H", recA, recB, out, exceptionFlags);
                    if (formatWidth > 64) begin
                        $write("\n\t");
                    end else begin
                        $write("  ");
                    end
                    $display(
                        "expected %0d %H", expectOut, expectExceptionFlags);
                    errorCount = errorCount + 1;
                    if (errorCount == maxNumErrors) disable TestLoop;
                end
                #1;
            end
        end
        count = count + partialCount;
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        if (errorCount) begin
            $fdisplay(
                'h80000002,
                "--> In %0d tests, %0d errors found.",
                count,
                errorCount
            );
            `finish_fail;
        end else if (count == 0) begin
            $fdisplay('h80000002, "--> Invalid test-cases input.");
            `finish_fail;
        end else begin
            $display(
    "In %0d tests, no errors found in 'compareRecF%0d', signaling %0d, op %s.",
                count,
                formatWidth,
                signaling,
                opName
            );
        end
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $finish;
    end

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module test_compareRecF16;

    test_compareRecFN#(5, 11) test_compareRecF16();

endmodule

module test_compareRecF32;

    test_compareRecFN#(8, 24) test_compareRecF32();

endmodule

module test_compareRecF64;

    test_compareRecFN#(11, 53) test_compareRecF64();

endmodule

module test_compareRecF128;

    test_compareRecFN#(15, 113) test_compareRecF128();

endmodule

