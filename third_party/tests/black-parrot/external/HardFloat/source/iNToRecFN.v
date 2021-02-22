
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
    iNToRawFN#(parameter intWidth = 1) (signedIn, in, isZero, sign, sExp, sig);
`include "HardFloat_localFuncs.vi"
    localparam expWidth = clog2(intWidth) + 1;
    input signedIn;
    input [(intWidth - 1):0] in;
    output isZero;
    output sign;
    output signed [(expWidth + 1):0] sExp;
    output [intWidth:0] sig;

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam extIntWidth = 1<<(expWidth - 1);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    assign sign = signedIn && in[intWidth - 1];
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [(intWidth - 1):0] absIn = sign ? -in : in;
    wire [(extIntWidth - 1):0] extAbsIn = absIn;
    wire [(expWidth - 2):0] adjustedNormDist;
    countLeadingZeros#(extIntWidth, expWidth - 1)
        countLeadingZeros(extAbsIn, adjustedNormDist);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    assign sig = (extAbsIn<<adjustedNormDist)>>(extIntWidth - intWidth);
    assign isZero = !sig[intWidth - 1];
    assign sExp = {2'b10, ~adjustedNormDist};

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module
    iNToRecFN#(
        parameter intWidth = 1, parameter expWidth = 3, parameter sigWidth = 3
    ) (
        input [(`floatControlWidth - 1):0] control,
        input signedIn,
        input [(intWidth - 1):0] in,
        input [2:0] roundingMode,
        output [(expWidth + sigWidth):0] out,
        output [4:0] exceptionFlags
    );
`include "HardFloat_localFuncs.vi"

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam intExpWidth = clog2(intWidth) + 1;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isZero, sign;
    wire signed [(intExpWidth + 1):0] sExp;
    wire [intWidth:0] sig;
    iNToRawFN#(intWidth) iNToRawFN(signedIn, in, isZero, sign, sExp, sig);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    roundAnyRawFNToRecFN#(
        intExpWidth,
        intWidth,
        expWidth,
        sigWidth,
        `flRoundOpt_sigMSBitAlwaysZero | `flRoundOpt_neverUnderflows
    ) roundRawToOut(
            control,
            1'b0,
            1'b0,
            1'b0,
            1'b0,
            isZero,
            sign,
            sExp,
            sig,
            roundingMode,
            out,
            exceptionFlags
        );

endmodule

