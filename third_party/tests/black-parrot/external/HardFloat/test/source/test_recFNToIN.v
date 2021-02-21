
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

module
    test_recFNToIN#(
        parameter expWidth = 3, parameter sigWidth = 3, parameter intWidth = 1
    );

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    parameter maxNumErrors = 20;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam formatWidth = expWidth + sigWidth;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg [(`floatControlWidth - 1):0] control;
    reg [2:0] roundingMode;
    reg signedOut;
    reg [(formatWidth - 1):0] in;
    reg [(intWidth - 1):0] expectOut;
    reg [4:0] expectExceptionFlags;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recIn;
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_in(in, recIn);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [(intWidth - 1):0] out;
    wire [2:0] intExceptionFlags;
    recFNToIN#(expWidth, sigWidth, intWidth)
        recFNToIN(
            control, recIn, roundingMode, signedOut, out, intExceptionFlags);
    wire [4:0] exceptionFlags =
        {|intExceptionFlags[2:1], 3'b0, intExceptionFlags[0]};
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount;
    initial begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fwrite('h80000002, "Testing 'recF%0dToI%0d'", formatWidth, intWidth);
        if (
            $fscanf('h80000000, "%h %h %h", control, signedOut, roundingMode)
                < 3
        ) begin
            $fdisplay('h80000002, ".\n--> Invalid test-cases input.");
            `finish_fail;
        end
        $fdisplay(
            'h80000002,
            "control %H, signed %0d, rounding mode %0d:",
            control,
            signedOut,
            roundingMode
        );
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        errorCount = 0;
        count = 0;
        partialCount = 0;
        begin :TestLoop
            while (
                $fscanf(
                    'h80000000, "%h %h %h", in, expectOut, expectExceptionFlags
                ) == 3
            ) begin
                #1;
                partialCount = partialCount + 1;
                if (partialCount == 10000) begin
                    count = count + 10000;
                    $fdisplay('h80000002, "%0d...", count);
                    partialCount = 0;
                end
                if (
                    (out != expectOut)
                        || (exceptionFlags !== expectExceptionFlags)
                ) begin
                    if (errorCount == 0) begin
                        $display(
 "Errors found in 'recF%0dToI%0d', control %H, signed %0d, rounding mode %0d:",
                            formatWidth,
                            intWidth,
                            control,
                            signedOut,
                            roundingMode
                        );
                    end
                    $write("%H  => %H %H", recIn, out, exceptionFlags);
                    if (formatWidth + intWidth > 160) begin
                        $write("\n\t");
                    end else begin
                        $write("  ");
                    end
                    $display(
                        "expected %H %H", expectOut, expectExceptionFlags);
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
"In %0d tests, no errors found in 'recF%0dToI%0d', control %H, signed %0d, rounding mode %0d.",
                count,
                formatWidth,
                intWidth,
                control,
                signedOut,
                roundingMode
            );
        end
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $finish;
    end

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module test_recF16ToI32;

    test_recFNToIN#(5, 11, 32) test_recF16ToI32();

endmodule

module test_recF32ToI32;

    test_recFNToIN#(8, 24, 32) test_recF32ToI32();

endmodule

module test_recF64ToI32;

    test_recFNToIN#(11, 53, 32) test_recF64ToI32();

endmodule

module test_recF128ToI32;

    test_recFNToIN#(15, 113, 32) test_recF128ToI32();

endmodule

module test_recF16ToI64;

    test_recFNToIN#(5, 11, 64) test_recF16ToI64();

endmodule

module test_recF32ToI64;

    test_recFNToIN#(8, 24, 64) test_recF32ToI64();

endmodule

module test_recF64ToI64;

    test_recFNToIN#(11, 53, 64) test_recF64ToI64();

endmodule

module test_recF128ToI64;

    test_recFNToIN#(15, 113, 64) test_recF128ToI64();

endmodule

