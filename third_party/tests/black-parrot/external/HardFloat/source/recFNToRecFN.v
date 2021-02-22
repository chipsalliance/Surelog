
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
    recFNToRecFN#(
        parameter inExpWidth = 3,
        parameter inSigWidth = 3,
        parameter outExpWidth = 3,
        parameter outSigWidth = 3
    ) (
        input [(`floatControlWidth - 1):0] control,
        input [(inExpWidth + inSigWidth):0] in,
        input [2:0] roundingMode,
        output [(outExpWidth + outSigWidth):0] out,
        output [4:0] exceptionFlags
    );

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isNaN, isInf, isZero, sign;
    wire signed [(inExpWidth + 1):0] sExpIn;
    wire [inSigWidth:0] sigIn;
    recFNToRawFN#(inExpWidth, inSigWidth)
        inToRawIn(in, isNaN, isInf, isZero, sign, sExpIn, sigIn);
    wire isSigNaN;
    isSigNaNRecFN#(inExpWidth, inSigWidth) isSigNaNIn(in, isSigNaN);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    generate
        if ((inExpWidth == outExpWidth) && (inSigWidth <= outSigWidth)) begin
            /*----------------------------------------------------------------
            *----------------------------------------------------------------*/
            wire [(outExpWidth + outSigWidth):0] tentativeOut =
                in<<(outSigWidth - inSigWidth);
`ifdef HardFloat_propagateNaNPayloads
            assign out = tentativeOut | isNaN<<(outSigWidth - 2);
`else
            assign out =
                isNaN
                    ? {`HardFloat_signDefaultNaN, 3'b111}
                          <<(outExpWidth + outSigWidth - 3)
                          | `HardFloat_fractDefaultNaN(outSigWidth)
                    : tentativeOut;
`endif
            assign exceptionFlags = {isSigNaN, 4'b0000};
        end else begin
            /*----------------------------------------------------------------
            *----------------------------------------------------------------*/
            roundAnyRawFNToRecFN#(
                inExpWidth,
                inSigWidth,
                outExpWidth,
                outSigWidth,
                `flRoundOpt_sigMSBitAlwaysZero
            ) roundRawInToOut(
                    control,
                    isSigNaN,
                    1'b0,
                    isNaN,
                    isInf,
                    isZero,
                    sign,
                    sExpIn,
                    sigIn,
                    roundingMode,
                    out,
                    exceptionFlags
                );
        end
    endgenerate

endmodule

