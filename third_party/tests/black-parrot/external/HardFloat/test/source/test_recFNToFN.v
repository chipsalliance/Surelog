
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
    test_recFNToFN#(
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
    reg [(formatWidth - 1):0] in;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recIn;
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_in(in, recIn);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [(formatWidth - 1):0] out;
    recFNToFN#(expWidth, sigWidth) recFNToFN(recIn, out);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount;
    initial begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fdisplay(
            'h80000002, "Testing 'recF%0dToF%0d':", formatWidth, formatWidth);
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        errorCount = 0;
        count = 0;
        partialCount = 0;
        begin :TestLoop
            while ($fscanf('h80000000, "%h", in) == 1) begin
                #1;
                partialCount = partialCount + 1;
                if (partialCount == 10000) begin
                    count = count + 10000;
                    $fdisplay('h80000002, "%0d...", count);
                    partialCount = 0;
                end
                if (out != in) begin
                    if (errorCount == 0) begin
                        $display(
                            "Errors found in 'recF%0dToF%0d':",
                            formatWidth,
                            formatWidth
                        );
                    end
                    $write("%H  => %H", recIn, out);
                    if (formatWidth > 64) begin
                        $write("\n\t");
                    end else begin
                        $write("  ");
                    end
                    $display("expected %H", in);
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
                "In %0d tests, no errors found in 'recF%0dToF%0d'.",
                count,
                formatWidth,
                formatWidth
            );
        end
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $finish;
    end

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module test_recF16ToF16;

    test_recFNToFN#(5, 11) test_recF16ToF16();

endmodule

module test_recF32ToF32;

    test_recFNToFN#(8, 24) test_recF32ToF32();

endmodule

module test_recF64ToF64;

    test_recFNToFN#(11, 53) test_recF64ToF64();

endmodule

module test_recF128ToF128;

    test_recFNToFN#(15, 113) test_recF128ToF128();

endmodule

