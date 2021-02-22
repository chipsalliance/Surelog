
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
    recFNToIN#(
        parameter expWidth = 3, parameter sigWidth = 3, parameter intWidth = 1
    ) (
        input [(`floatControlWidth - 1):0] control,
        input [(expWidth + sigWidth):0] in,
        input [2:0] roundingMode,
        input signedOut,
        output [(intWidth - 1):0] out,
        output [2:0] intExceptionFlags
    );
`include "HardFloat_localFuncs.vi"

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam intExpWidth = clog2(intWidth);
    localparam boundedIntExpWidth =
        (expWidth <= intExpWidth) ? expWidth - 1 : intExpWidth;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isNaN, isInf, isZero, sign;
    wire signed [(expWidth + 1):0] sExp;
    wire [sigWidth:0] sig;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN(in, isNaN, isInf, isZero, sign, sExp, sig);
    wire magGeOne = sExp[expWidth];
    wire [(expWidth - 1):0] posExp = sExp[(expWidth - 1):0];
    wire magJustBelowOne = !magGeOne && (&posExp);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire roundingMode_near_even   = (roundingMode == `round_near_even);
    wire roundingMode_minMag      = (roundingMode == `round_minMag);
    wire roundingMode_min         = (roundingMode == `round_min);
    wire roundingMode_max         = (roundingMode == `round_max);
    wire roundingMode_near_maxMag = (roundingMode == `round_near_maxMag);
    wire roundingMode_odd         = (roundingMode == `round_odd);
    /*------------------------------------------------------------------------
    | Assuming the input floating-point value is not a NaN, its magnitude is
    | at least 1, and it is not obviously so large as to lead to overflow,
    | convert its significand to fixed-point (i.e., with the binary point in a
    | fixed location).  For a non-NaN input with a magnitude less than 1, this
    | expression contrives to ensure that the integer bits of 'alignedSig'
    | will all be zeros.
    *------------------------------------------------------------------------*/
    wire [(intWidth + sigWidth - 1):0] shiftedSig =
        {magGeOne, sig[(sigWidth - 2):0]}
            <<(magGeOne ? sExp[(boundedIntExpWidth - 1):0] : 0);
    wire [(intWidth + 1):0] alignedSig =
        {shiftedSig>>(sigWidth - 2), |shiftedSig[(sigWidth - 3):0]};
    wire [(intWidth - 1):0] unroundedInt = alignedSig>>2;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire common_inexact = magGeOne ? |alignedSig[1:0] : !isZero;
    wire roundIncr_near_even =
           (magGeOne        && ((&alignedSig[2:1]) || (&alignedSig[1:0])))
        || (magJustBelowOne && (|alignedSig[1:0])                        );
    wire roundIncr_near_maxMag =
        (magGeOne && alignedSig[1]) || magJustBelowOne;
    wire roundIncr =
           (roundingMode_near_even                 && roundIncr_near_even     )
        || (roundingMode_near_maxMag               && roundIncr_near_maxMag   )
        || ((roundingMode_min || roundingMode_odd) && (sign && common_inexact))
        || (roundingMode_max                     && (!sign && common_inexact));
    wire [(intWidth - 1):0] complUnroundedInt =
        sign ? ~unroundedInt : unroundedInt;
    wire [(intWidth - 1):0] roundedInt =
        (roundIncr ^ sign ? complUnroundedInt + 1 : complUnroundedInt)
            | (roundingMode_odd && common_inexact);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire magGeOne_atOverflowEdge = (posExp == intWidth - 1);
    wire roundCarryBut2 = (&unroundedInt[(intWidth - 3):0]) && roundIncr;
    wire common_overflow =
        magGeOne
            ? (posExp >= intWidth)
                  || (signedOut
                          ? (sign ? magGeOne_atOverflowEdge
                                        && ((|unroundedInt[(intWidth - 2):0])
                                                || roundIncr)
                                 : magGeOne_atOverflowEdge
                                       || ((posExp == intWidth - 2)
                                               && roundCarryBut2))
                          : sign || (magGeOne_atOverflowEdge
                                         && unroundedInt[intWidth - 2]
                                         && roundCarryBut2))
            : !signedOut && sign && roundIncr;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire invalidExc = isNaN || isInf;
    wire overflow = !invalidExc && common_overflow;
    wire inexact  = !invalidExc && !common_overflow && common_inexact;
    wire [(intWidth - 1):0] excOut;
    iNFromException#(intWidth) iNFromException(signedOut, isNaN, sign, excOut);
    assign out = invalidExc || common_overflow ? excOut : roundedInt;
    assign intExceptionFlags = {invalidExc, overflow, inexact};

endmodule

