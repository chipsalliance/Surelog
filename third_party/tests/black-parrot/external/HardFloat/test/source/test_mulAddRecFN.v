
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

module test_mulAddRecFN#(parameter expWidth = 3, parameter sigWidth = 3);

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
    reg [(formatWidth - 1):0] a, b, c, expectOut;
    reg [4:0] expectExceptionFlags;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recA, recB, recC, recExpectOut;
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_a(a, recA);
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_b(b, recB);
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_c(c, recC);
    fNToRecFN#(expWidth, sigWidth)
        fNToRecFN_expectOut(expectOut, recExpectOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recOut;
    wire [4:0] exceptionFlags;
    reg int_mul;
    integer i;
    wire [expWidth + sigWidth-1:0] out_imul;
    mulAddRecFN#(expWidth, sigWidth)
        mulAddRecFN(
            control,
            {int_mul, 2'b00},
            recA,
            recB,
            recC,
            roundingMode,
            recOut,
            exceptionFlags,
            out_imul
        );
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire sameOut;
    sameRecFN#(expWidth, sigWidth) sameRecFN(recOut, recExpectOut, sameOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount;
    initial begin
        errorCount = 0;
        // We generate 1000 examples to test the function.
        int_mul = 1'b1;
        begin:int_loop
            for(i = 0; i < 1000; i = i + 1) begin
                a = $random;
                b = $random;
                if(out_imul != a * b)begin
                    errorCount = errorCount + 1;
                    if (errorCount == maxNumErrors) disable int_loop;
                end
            end
        end
        int_mul = 1'b0;
        $fwrite('h80000002, "Testing Integer Multiply Done. Error: %d\n", errorCount);
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fwrite('h80000002, "Testing 'mulAddRecF%0d'", formatWidth);
        if ($fscanf('h80000000, "%h %h", control, roundingMode) < 2) begin
            $fdisplay('h80000002, ".\n--> Invalid test-cases input.");
            `finish_fail;
        end
        $fdisplay(
            'h80000002,
            ", control %H, rounding mode %0d:",
            control,
            roundingMode
        );
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        count = 0;
        partialCount = 0;
        begin :TestLoop
            while (
                $fscanf(
                    'h80000000,
                    "%h %h %h %h %h",
                    a,
                    b,
                    c,
                    expectOut,
                    expectExceptionFlags
                ) == 5
            ) begin
                #1;
                partialCount = partialCount + 1;
                if (partialCount == 10000) begin
                    count = count + 10000;
                    $fdisplay('h80000002, "%0d...", count);
                    partialCount = 0;
                end
                if (
                    !sameOut || (exceptionFlags !== expectExceptionFlags)
                ) begin
                    if (errorCount == 0) begin
                        $display(
             "Errors found in 'mulAddRecF%0d', control %H, rounding mode %0d:",
                            formatWidth,
                            control,
                            roundingMode
                        );
                    end
                    $write("%H %H", recA, recB);
                    if (formatWidth > 64) begin
                        $write("\n\t");
                    end else begin
                        $write(" ");
                    end
                    $write("%H", recC);
                    if (formatWidth > 64) begin
                        $write("\n\t");
                    end else begin
                        $write("  ");
                    end
                    $write("=> %H %H", recOut, exceptionFlags);
                    if (formatWidth > 32) begin
                        $write("\n\t");
                    end else begin
                        $write("  ");
                    end
                    $display(
                        "expected %H %H", recExpectOut, expectExceptionFlags);
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
"In %0d tests, no errors found in 'mulAddRecF%0d', control %H, rounding mode %0d.",
                count,
                formatWidth,
                control,
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

module test_mulAddRecF16;

    test_mulAddRecFN#(5, 11) test_mulAddRecF16();

endmodule

module test_mulAddRecF32;

    test_mulAddRecFN#(8, 24) test_mulAddRecF32();

endmodule

module test_mulAddRecF64;

    test_mulAddRecFN#(11, 53) test_mulAddRecF64();

endmodule

module test_mulAddRecF128;

    test_mulAddRecFN#(15, 113) test_mulAddRecF128();

endmodule

