
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
    test_recFNToRecFN#(
        parameter inExpWidth = 3,
        parameter inSigWidth = 3,
        parameter outExpWidth = 3,
        parameter outSigWidth = 3
    );

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    parameter maxNumErrors = 20;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam inFormatWidth  = inExpWidth  + inSigWidth;
    localparam outFormatWidth = outExpWidth + outSigWidth;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg [(`floatControlWidth - 1):0] control;
    reg [2:0] roundingMode;
    reg [(inFormatWidth - 1):0] in;
    reg [(outFormatWidth - 1):0] expectOut;
    reg [4:0] expectExceptionFlags;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [inFormatWidth:0] recIn;
    fNToRecFN#(inExpWidth, inSigWidth) fNToRecFN_in(in, recIn);
    wire [outFormatWidth:0] recExpectOut;
    fNToRecFN#(outExpWidth, outSigWidth)
        fNToRecFN_expectOut(expectOut, recExpectOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [outFormatWidth:0] recOut;
    wire [4:0] exceptionFlags;
    recFNToRecFN#(inExpWidth, inSigWidth, outExpWidth, outSigWidth)
        recFNToRecFN(control, recIn, roundingMode, recOut, exceptionFlags);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire sameOut;
    sameRecFN#(outExpWidth, outSigWidth)
        same_recOut(recOut, recExpectOut, sameOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount;
    initial begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fwrite(
            'h80000002,
            "Testing 'recF%0dToRecF%0d'",
            inFormatWidth,
            outFormatWidth
        );
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
                    !sameOut || (exceptionFlags !== expectExceptionFlags)
                ) begin
                    if (errorCount == 0) begin
                        $display(
          "Errors found in 'recF%0dToRecF%0d', control %H, rounding mode %0d:",
                            inFormatWidth,
                            outFormatWidth,
                            control,
                            roundingMode
                        );
                    end
                    $write("%H  => %H %H", recIn, recOut, exceptionFlags);
                    if (
                        (outFormatWidth > 64)
                            || (inFormatWidth + outFormatWidth > 160)
                    ) begin
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
"In %0d tests, no errors found in 'recF%0dToRecF%0d', control %H, rounding mode %0d.",
                count,
                inFormatWidth,
                outFormatWidth,
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

module test_recF16ToRecF32;

    test_recFNToRecFN#(5, 11, 8, 24) test_recF16ToRecF32();

endmodule

module test_recF16ToRecF64;

    test_recFNToRecFN#(5, 11, 11, 53) test_recF16ToRecF64();

endmodule

module test_recF16ToRecF128;

    test_recFNToRecFN#(5, 11, 15, 113) test_recF16ToRecF128();

endmodule

module test_recF32ToRecF16;

    test_recFNToRecFN#(8, 24, 5, 11) test_recF32ToRecF16();

endmodule

module test_recF32ToRecF64;

    test_recFNToRecFN#(8, 24, 11, 53) test_recF32ToRecF64();

endmodule

module test_recF32ToRecF128;

    test_recFNToRecFN#(8, 24, 15, 113) test_recF32ToRecF128();

endmodule

module test_recF64ToRecF16;

    test_recFNToRecFN#(11, 53, 5, 11) test_recF64ToRecF16();

endmodule

module test_recF64ToRecF32;

    test_recFNToRecFN#(11, 53, 8, 24) test_recF64ToRecF32();

endmodule

module test_recF64ToRecF128;

    test_recFNToRecFN#(11, 53, 15, 113) test_recF64ToRecF128();

endmodule

module test_recF128ToRecF16;

    test_recFNToRecFN#(15, 113, 5, 11) test_recF128ToRecF16();

endmodule

module test_recF128ToRecF32;

    test_recFNToRecFN#(15, 113, 8, 24) test_recF128ToRecF32();

endmodule

module test_recF128ToRecF64;

    test_recFNToRecFN#(15, 113, 11, 53) test_recF128ToRecF64();

endmodule

