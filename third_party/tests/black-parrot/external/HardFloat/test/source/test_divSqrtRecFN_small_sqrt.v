
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
    test_divSqrtRecFN_small_sqrt#(
        parameter expWidth = 3, parameter sigWidth = 3);

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    parameter maxNumErrors = 20;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam formatWidth = expWidth + sigWidth;
    localparam maxNumCyclesToDelay = sigWidth + 10;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer errorCount, count, partialCount, moreIn, queueCount;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg nReset, clock;
    initial begin
        clock = 1;
        forever #5 clock = !clock;
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg inValid;
    wire inReady;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg integer delay;
    always @(negedge nReset, posedge clock) begin
        if (!nReset) begin
            delay <= 0;
        end else begin
            delay <=
                inValid && inReady ? {$random} % maxNumCyclesToDelay
                    : delay ? delay - 1 : 0;
        end
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg [(`floatControlWidth - 1):0] control;
    reg [2:0] roundingMode;
    reg [(formatWidth - 1):0] a, expectOut;
    reg [4:0] expectExceptionFlags;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recA;
    fNToRecFN#(expWidth, sigWidth) fNToRecFN_a(a, recA);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg [formatWidth:0] queue_recA[1:5];
    reg [(formatWidth - 1):0] queue_expectOut[1:5];
    reg [4:0] queue_expectExceptionFlags[1:5];
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    initial begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        $fwrite(
            'h80000002, "Testing 'divSqrtRecF%0d_small_sqrt'", formatWidth);
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
        moreIn = 1;
        queueCount = 0;
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        inValid = 0;
        nReset = 0;
        #21;
        nReset = 1;
        while (
            $fscanf(
                'h80000000, "%h %h %h", a, expectOut, expectExceptionFlags)
                == 3
        ) begin
            while (delay != 0) #10;
            inValid = 1;
            while (!inReady) #10;
            #10;
            inValid = 0;
            queueCount = queueCount + 1;
            queue_recA[5] = queue_recA[4];
            queue_recA[4] = queue_recA[3];
            queue_recA[3] = queue_recA[2];
            queue_recA[2] = queue_recA[1];
            queue_recA[1] = recA;
            queue_expectOut[5] = queue_expectOut[4];
            queue_expectOut[4] = queue_expectOut[3];
            queue_expectOut[3] = queue_expectOut[2];
            queue_expectOut[2] = queue_expectOut[1];
            queue_expectOut[1] = expectOut;
            queue_expectExceptionFlags[5] = queue_expectExceptionFlags[4];
            queue_expectExceptionFlags[4] = queue_expectExceptionFlags[3];
            queue_expectExceptionFlags[3] = queue_expectExceptionFlags[2];
            queue_expectExceptionFlags[2] = queue_expectExceptionFlags[1];
            queue_expectExceptionFlags[1] = expectExceptionFlags;
        end
        moreIn = 0;
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] recExpectOut;
    fNToRecFN#(expWidth, sigWidth)
        fNToRecFN_expectOut(queue_expectOut[queueCount], recExpectOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [formatWidth:0] b = 0;
    wire outValid, sqrtOpOut;
    wire [formatWidth:0] recOut;
    wire [4:0] exceptionFlags;
    divSqrtRecFN_small#(expWidth, sigWidth, 0)
        sqrtRecFN(
            nReset,
            clock,
            control,
            inReady,
            inValid,
            1'b1,
            recA,
            b,
            roundingMode,
            outValid,
            sqrtOpOut,
            recOut,
            exceptionFlags
        );
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire sameOut;
    sameRecFN#(expWidth, sigWidth) sameRecFN(recOut, recExpectOut, sameOut);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    integer doExit;
    always @(posedge clock) begin
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        doExit = 0;
        if (outValid) begin
            if (!queueCount) begin
                $fdisplay('h80000002, "--> Spurious 'outValid'.");
                `finish_fail;
            end
            partialCount = partialCount + 1;
            if (partialCount == 10000) begin
                count = count + 10000;
                $fdisplay('h80000002, "%0d...", count);
                partialCount = 0;
            end
            if (
                   !sameOut
                || (exceptionFlags !== queue_expectExceptionFlags[queueCount])
            ) begin
                if (errorCount == 0) begin
                    $display(
 "Errors found in 'divSqrtRecF%0d_small_sqrt', control %H, rounding mode %0d:",
                        formatWidth,
                        control,
                        roundingMode
                    );
                end
                $write(
                    "%H  => %H %H",
                    queue_recA[queueCount],
                    recOut,
                    exceptionFlags
                );
                if (formatWidth > 64) begin
                    $write("\n\t");
                end else begin
                    $write("  ");
                end
                $display(
                    "expected %H %H",
                    recExpectOut,
                    queue_expectExceptionFlags[queueCount]
                );
                errorCount = errorCount + 1;
                doExit = (errorCount == maxNumErrors);
            end
            queueCount = queueCount - 1;
        end else begin
            doExit = !moreIn && !queueCount;
        end
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        if (doExit) begin
            count = count + partialCount;
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
"In %0d tests, no errors found in 'divSqrtRecF%0d_small_sqrt', control %H, rounding mode %0d.",
                    count,
                    formatWidth,
                    control,
                    roundingMode
                );
            end
            $finish;
        end
    end

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module test_divSqrtRecF16_small_sqrt;

    test_divSqrtRecFN_small_sqrt#(5, 11) test_sqrtRecF16();

endmodule

module test_divSqrtRecF32_small_sqrt;

    test_divSqrtRecFN_small_sqrt#(8, 24) test_sqrtRecF32();

endmodule

module test_divSqrtRecF64_small_sqrt;

    test_divSqrtRecFN_small_sqrt#(11, 53) test_sqrtRecF64();

endmodule

module test_divSqrtRecF128_small_sqrt;

    test_divSqrtRecFN_small_sqrt#(15, 113) test_sqrtRecF128();

endmodule

