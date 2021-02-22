
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
    mulAddRecFNToRaw_preMul#(
        parameter expWidth = 3, parameter sigWidth = 3, parameter imulEn = 1
    ) (
        control,
        op,
        a,
        b,
        c,
        roundingMode,
        mulAddA,
        mulAddB,
        mulAddC,
        intermed_compactState,
        intermed_sExp,
        intermed_CDom_CAlignDist,
        intermed_highAlignedSigC
    );
`include "HardFloat_localFuncs.vi"
    input [(`floatControlWidth - 1):0] control;
    input [2:0] op;
    input [(expWidth + sigWidth):0] a;
    input [(expWidth + sigWidth):0] b;
    input [(expWidth + sigWidth):0] c;
    input [2:0] roundingMode;
    output [(sigWidth - 1):0] mulAddA;
    output [(sigWidth - 1):0] mulAddB;
    output [(sigWidth*2 - 1):0] mulAddC;
    output [5:0] intermed_compactState;
    output signed [(expWidth + 1):0] intermed_sExp;
    output [(clog2(sigWidth + 1) - 1):0] intermed_CDom_CAlignDist;
    output [(sigWidth + 1):0] intermed_highAlignedSigC;

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam prodWidth = sigWidth*2;
    localparam sigSumWidth = sigWidth + prodWidth + 3;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isNaNA, isInfA, isZeroA, signA;
    wire signed [(expWidth + 1):0] sExpA;
    wire [sigWidth:0] sigA;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN_a(a, isNaNA, isInfA, isZeroA, signA, sExpA, sigA);
    wire isSigNaNA;
    isSigNaNRecFN#(expWidth, sigWidth) isSigNaN_a(a, isSigNaNA);
    wire isNaNB, isInfB, isZeroB, signB;
    wire signed [(expWidth + 1):0] sExpB;
    wire [sigWidth:0] sigB;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN_b(b, isNaNB, isInfB, isZeroB, signB, sExpB, sigB);
    wire isSigNaNB;
    isSigNaNRecFN#(expWidth, sigWidth) isSigNaN_b(b, isSigNaNB);
    wire isNaNC, isInfC, isZeroC, signC;
    wire signed [(expWidth + 1):0] sExpC;
    wire [sigWidth:0] sigC;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN_c(c, isNaNC, isInfC, isZeroC, signC, sExpC, sigC);
    wire isSigNaNC;
    isSigNaNRecFN#(expWidth, sigWidth) isSigNaN_c(c, isSigNaNC);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire signProd = signA ^ signB ^ op[1];
    wire signed [(expWidth + 2):0] sExpAlignedProd =
        sExpA + sExpB + (-(1<<expWidth) + sigWidth + 3);
    wire doSubMags = signProd ^ signC ^ op[0];
    wire opSignC = signProd ^ doSubMags;
    wire roundingMode_min = (roundingMode == `round_min);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire signed [(expWidth + 2):0] sNatCAlignDist = sExpAlignedProd - sExpC;
    wire [(expWidth + 1):0] posNatCAlignDist =
        sNatCAlignDist[(expWidth + 1):0];
    wire isMinCAlign = isZeroA || isZeroB || (sNatCAlignDist < 0);
    wire CIsDominant =
        !isZeroC && (isMinCAlign || (posNatCAlignDist <= sigWidth));
    wire signed [(expWidth + 1):0] sExpSum =
        CIsDominant ? sExpC : sExpAlignedProd - sigWidth;
    wire [(clog2(sigSumWidth) - 1):0] CAlignDist =
        isMinCAlign ? 0
            : (posNatCAlignDist < sigSumWidth - 1)
                  ? posNatCAlignDist[(clog2(sigSumWidth) - 1):0]
                  : sigSumWidth - 1;
    wire signed [(sigSumWidth + 2):0] extComplSigC =
        {doSubMags ? ~sigC : sigC, {(sigSumWidth - sigWidth + 2){doSubMags}}};
    wire [(sigSumWidth + 1):0] mainAlignedSigC = extComplSigC>>>CAlignDist;
    localparam CGrainAlign = (sigSumWidth - sigWidth - 1) & 3;
    wire [(sigWidth + CGrainAlign):0] grainAlignedSigC = sigC<<CGrainAlign;
    wire [(sigWidth + CGrainAlign)/4:0] reduced4SigC;
    compressBy4#(sigWidth + 1 + CGrainAlign)
        compressBy4_sigC(grainAlignedSigC, reduced4SigC);
    localparam CExtraMaskHiBound = (sigSumWidth - 1)/4;
    localparam CExtraMaskLoBound = (sigSumWidth - sigWidth - 1)/4;
    wire [(CExtraMaskHiBound - CExtraMaskLoBound - 1):0] CExtraMask;
    lowMaskHiLo#(clog2(sigSumWidth) - 2, CExtraMaskHiBound, CExtraMaskLoBound)
        lowMask_CExtraMask(CAlignDist[(clog2(sigSumWidth) - 1):2], CExtraMask);
    wire reduced4CExtra = |(reduced4SigC & CExtraMask);
    wire [(sigSumWidth - 1):0] alignedSigC =
        {mainAlignedSigC>>3,
         doSubMags ? (&mainAlignedSigC[2:0]) && !reduced4CExtra
             : (|mainAlignedSigC[2:0]) || reduced4CExtra};
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isNaNAOrB = isNaNA || isNaNB;
    wire isNaNAny = isNaNAOrB || isNaNC;
    wire isInfAOrB = isInfA || isInfB;
    wire invalidProd = (isInfA && isZeroB) || (isZeroA && isInfB);
    wire notSigNaN_invalidExc =
        invalidProd || (!isNaNAOrB && isInfAOrB && isInfC && doSubMags);
    wire invalidExc =
        isSigNaNA || isSigNaNB || isSigNaNC || notSigNaN_invalidExc;
    wire notNaN_addZeros = (isZeroA || isZeroB) && isZeroC;
    wire specialCase = isNaNAny || isInfAOrB || isInfC || notNaN_addZeros;
    wire specialNotNaN_signOut =
        (isInfAOrB && signProd) || (isInfC && opSignC)
            || (notNaN_addZeros && !roundingMode_min && signProd && opSignC)
            || (notNaN_addZeros && roundingMode_min && (signProd || opSignC));
`ifdef HardFloat_propagateNaNPayloads
    wire signNaN;
    wire [(sigWidth - 2):0] fractNaN;
    propagateFloatNaN_mulAdd#(sigWidth)
        propagateNaN(
            control,
            op[1:0],
            isNaNA,
            signA,
            sigA[(sigWidth - 2):0],
            isNaNB,
            signB,
            sigB[(sigWidth - 2):0],
            invalidProd,
            isNaNC,
            signC,
            sigC[(sigWidth - 2):0],
            signNaN,
            fractNaN
        );
    wire isNaNOut = isNaNAny || notSigNaN_invalidExc;
    wire special_signOut =
        isNaNAny || notSigNaN_invalidExc ? signNaN : specialNotNaN_signOut;
`else
    wire special_signOut = specialNotNaN_signOut;
`endif
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    if(imulEn) begin: fi1
        // This part has been modified so that we can support RISC-V integer multiply instruction MUL.
        // Please refer to the document for detailed implementation.
        assign mulAddA = op[2] ? a[sigWidth-1:0] : sigA;
        assign mulAddB = op[2] ? b[sigWidth-1:0] : sigB;
        // Generate modification bits
        wire [expWidth-1:0] aux_part = a[expWidth-1:0] * b[sigWidth+:expWidth] + a[sigWidth+:expWidth] * b[expWidth-1:0];
        assign mulAddC = op[2] ? {{(sigWidth - expWidth){1'b0}}, aux_part, {sigWidth{1'b0}}} : alignedSigC[prodWidth:1];
    end
    else begin: fi2
        assign mulAddA = sigA;
        assign mulAddB = sigB;
        assign mulAddC = alignedSigC[prodWidth:1];
    end
    assign intermed_compactState =
        {specialCase,
         invalidExc          || (!specialCase && signProd      ),
`ifdef HardFloat_propagateNaNPayloads
         isNaNOut            || (!specialCase && doSubMags     ),
`else
         isNaNAny            || (!specialCase && doSubMags     ),
`endif
         isInfAOrB || isInfC || (!specialCase && CIsDominant   ),
         notNaN_addZeros     || (!specialCase && alignedSigC[0]),
         special_signOut};
    assign intermed_sExp = sExpSum;
    assign intermed_CDom_CAlignDist = CAlignDist[(clog2(sigWidth + 1) - 1):0];
    assign intermed_highAlignedSigC =
`ifdef HardFloat_propagateNaNPayloads
         isNaNOut ? fractNaN :
`endif
          alignedSigC[(sigSumWidth - 1):(prodWidth + 1)];

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module
    mulAddRecFNToRaw_postMul#(parameter expWidth = 3, parameter sigWidth = 3) (
        intermed_compactState,
        intermed_sExp,
        intermed_CDom_CAlignDist,
        intermed_highAlignedSigC,
        mulAddResult,
        roundingMode,
        invalidExc,
        out_isNaN,
        out_isInf,
        out_isZero,
        out_sign,
        out_sExp,
        out_sig
    );
`include "HardFloat_localFuncs.vi"
    input [5:0] intermed_compactState;
    input signed [(expWidth + 1):0] intermed_sExp;
    input [(clog2(sigWidth + 1) - 1):0] intermed_CDom_CAlignDist;
    input [(sigWidth + 1):0] intermed_highAlignedSigC;
    input [sigWidth*2:0] mulAddResult;
    input [2:0] roundingMode;
    output invalidExc;
    output out_isNaN;
    output out_isInf;
    output out_isZero;
    output out_sign;
    output signed [(expWidth + 1):0] out_sExp;
    output [(sigWidth + 2):0] out_sig;

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    localparam prodWidth = sigWidth*2;
    localparam sigSumWidth = sigWidth + prodWidth + 3;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire specialCase     = intermed_compactState[5];
    assign invalidExc    = specialCase && intermed_compactState[4];
    assign out_isNaN     = specialCase && intermed_compactState[3];
    assign out_isInf     = specialCase && intermed_compactState[2];
    wire notNaN_addZeros = specialCase && intermed_compactState[1];
    wire signProd        = intermed_compactState[4];
    wire doSubMags       = intermed_compactState[3];
    wire CIsDominant     = intermed_compactState[2];
    wire bit0AlignedSigC = intermed_compactState[1];
    wire special_signOut = intermed_compactState[0];
`ifdef HardFloat_propagateNaNPayloads
    wire [(sigWidth - 2):0] fractNaN = intermed_highAlignedSigC;
`endif
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire opSignC = signProd ^ doSubMags;
    wire [(sigWidth + 1):0] incHighAlignedSigC = intermed_highAlignedSigC + 1;
    wire [(sigSumWidth - 1):0] sigSum =
        {mulAddResult[prodWidth] ? incHighAlignedSigC
             : intermed_highAlignedSigC,
         mulAddResult[(prodWidth - 1):0],
         bit0AlignedSigC};
    wire roundingMode_min = (roundingMode == `round_min);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire CDom_sign = opSignC;
    wire signed [(expWidth + 1):0] CDom_sExp = intermed_sExp - doSubMags;
    wire [(sigWidth*2 + 1):0] CDom_absSigSum =
        doSubMags ? ~sigSum[(sigSumWidth - 1):(sigWidth + 1)]
            : {1'b0, intermed_highAlignedSigC[(sigWidth + 1):sigWidth],
                   sigSum[(sigSumWidth - 3):(sigWidth + 2)]};
    wire CDom_absSigSumExtra =
        doSubMags ? !(&sigSum[sigWidth:1]) : |sigSum[(sigWidth + 1):1];
    wire [(sigWidth + 4):0] CDom_mainSig =
        (CDom_absSigSum<<intermed_CDom_CAlignDist)>>(sigWidth - 3);
    wire [((sigWidth | 3) - 1):0] CDom_grainAlignedLowSig =
        CDom_absSigSum[(sigWidth - 1):0]<<(~sigWidth & 3);
    wire [sigWidth/4:0] CDom_reduced4LowSig;
    compressBy4#(sigWidth | 3)
        compressBy4_CDom_absSigSum(
            CDom_grainAlignedLowSig, CDom_reduced4LowSig);
    wire [(sigWidth/4 - 1):0] CDom_sigExtraMask;
    lowMaskLoHi#(clog2(sigWidth + 1) - 2, 0, sigWidth/4)
        lowMask_CDom_sigExtraMask(
            intermed_CDom_CAlignDist[(clog2(sigWidth + 1) - 1):2],
            CDom_sigExtraMask
        );
    wire CDom_reduced4SigExtra = |(CDom_reduced4LowSig & CDom_sigExtraMask);
    wire [(sigWidth + 2):0] CDom_sig =
        {CDom_mainSig>>3,
         (|CDom_mainSig[2:0]) || CDom_reduced4SigExtra || CDom_absSigSumExtra};
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire notCDom_signSigSum = sigSum[prodWidth + 3];
    wire [(prodWidth + 2):0] notCDom_absSigSum =
        notCDom_signSigSum ? ~sigSum[(prodWidth + 2):0]
            : sigSum[(prodWidth + 2):0] + doSubMags;
    wire [(prodWidth + 2)/2:0] notCDom_reduced2AbsSigSum;
    compressBy2#(prodWidth + 3)
        compressBy2_notCDom_absSigSum(
            notCDom_absSigSum, notCDom_reduced2AbsSigSum);
    wire [(clog2(prodWidth + 4) - 2):0] notCDom_normDistReduced2;
    countLeadingZeros#((prodWidth + 2)/2 + 1, clog2(prodWidth + 4) - 1)
        countLeadingZeros_notCDom(
            notCDom_reduced2AbsSigSum, notCDom_normDistReduced2);
    wire [(clog2(prodWidth + 4) - 1):0] notCDom_nearNormDist =
        notCDom_normDistReduced2<<1;
    wire signed [(expWidth + 1):0] notCDom_sExp =
        intermed_sExp - notCDom_nearNormDist;
    wire [(sigWidth + 4):0] notCDom_mainSig =
        ({1'b0, notCDom_absSigSum}<<notCDom_nearNormDist)>>(sigWidth - 1);
    wire [(((sigWidth/2 + 1) | 1) - 1):0] CDom_grainAlignedLowReduced2Sig =
        notCDom_reduced2AbsSigSum[sigWidth/2:0]<<((sigWidth/2) & 1);
    wire [(sigWidth + 2)/4:0] notCDom_reduced4AbsSigSum;
    compressBy2#((sigWidth/2 + 1) | 1)
        compressBy2_notCDom_reduced2AbsSigSum(
            CDom_grainAlignedLowReduced2Sig, notCDom_reduced4AbsSigSum);
    wire [((sigWidth + 2)/4 - 1):0] notCDom_sigExtraMask;
    lowMaskLoHi#(clog2(prodWidth + 4) - 2, 0, (sigWidth + 2)/4)
        lowMask_notCDom_sigExtraMask(
            notCDom_normDistReduced2[(clog2(prodWidth + 4) - 2):1],
            notCDom_sigExtraMask
        );
    wire notCDom_reduced4SigExtra =
        |(notCDom_reduced4AbsSigSum & notCDom_sigExtraMask);
    wire [(sigWidth + 2):0] notCDom_sig =
        {notCDom_mainSig>>3,
         (|notCDom_mainSig[2:0]) || notCDom_reduced4SigExtra};
    wire notCDom_completeCancellation =
        (notCDom_sig[(sigWidth + 2):(sigWidth + 1)] == 0);
    wire notCDom_sign =
        notCDom_completeCancellation ? roundingMode_min
            : signProd ^ notCDom_signSigSum;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    assign out_isZero =
        notNaN_addZeros || (!CIsDominant && notCDom_completeCancellation);
    assign out_sign =
           ( specialCase                 && special_signOut)
        || (!specialCase &&  CIsDominant && CDom_sign      )
        || (!specialCase && !CIsDominant && notCDom_sign   );
    assign out_sExp = CIsDominant ? CDom_sExp : notCDom_sExp;
`ifdef HardFloat_propagateNaNPayloads
    assign out_sig =
        out_isNaN ? {1'b1, fractNaN, 2'b00}
            : CIsDominant ? CDom_sig : notCDom_sig;
`else
    assign out_sig = CIsDominant ? CDom_sig : notCDom_sig;
`endif

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module
    mulAddRecFNToRaw#(
        parameter expWidth = 3,
        parameter sigWidth = 3,
        parameter imulEn = 1'b1 // set 1 to enable integer MUL.
    ) (
        input [(`floatControlWidth - 1):0] control,
        // by set op[2] to 1, we can reuse this module to execute RISC-V integer multiply instruction MUL.
        input [2:0] op,
        // Note that for both signed and unsigned multiply, the results are the same, because we truncate the sign extension when evaluating the lower part. 
        input [(expWidth + sigWidth):0] a,
        input [(expWidth + sigWidth):0] b,
        input [(expWidth + sigWidth):0] c,
        input [2:0] roundingMode,
        output invalidExc,
        output out_isNaN,
        output out_isInf,
        output out_isZero,
        output out_sign,
        output signed [(expWidth + 1):0] out_sExp,
        output [(sigWidth + 2):0] out_sig,
        // The output port of integer multiply.
        output [expWidth + sigWidth-1:0] out_imul
    );
`include "HardFloat_localFuncs.vi"

    wire [(sigWidth - 1):0] mulAddA, mulAddB;
    wire [(sigWidth*2 - 1):0] mulAddC;
    wire [5:0] intermed_compactState;
    wire signed [(expWidth + 1):0] intermed_sExp;
    wire [(clog2(sigWidth + 1) - 1):0] intermed_CDom_CAlignDist;
    wire [(sigWidth + 1):0] intermed_highAlignedSigC;
    mulAddRecFNToRaw_preMul#(expWidth, sigWidth, imulEn)
        mulAddToRaw_preMul(
            control,
            op,
            a,
            b,
            c,
            roundingMode,
            mulAddA,
            mulAddB,
            mulAddC,
            intermed_compactState,
            intermed_sExp,
            intermed_CDom_CAlignDist,
            intermed_highAlignedSigC
        );
    
    
    // MAC
    wire [sigWidth*2:0] mulAddResult = mulAddA * mulAddB + mulAddC;
    mulAddRecFNToRaw_postMul#(expWidth, sigWidth)
        mulAddToRaw_postMul(
            intermed_compactState,
            intermed_sExp,
            intermed_CDom_CAlignDist,
            intermed_highAlignedSigC,
            mulAddResult,
            roundingMode,
            invalidExc,
            out_isNaN,
            out_isInf,
            out_isZero,
            out_sign,
            out_sExp,
            out_sig
        );
    assign out_imul = mulAddResult[expWidth + sigWidth-1:0];
endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module
    mulAddRecFN#(
        parameter expWidth = 3,
        parameter sigWidth = 3,
        parameter imulEn = 1'b1
    ) (
        input [(`floatControlWidth - 1):0] control,
        input [2:0] op, 
        input [(expWidth + sigWidth):0] a,
        input [(expWidth + sigWidth):0] b,
        input [(expWidth + sigWidth):0] c,
        input [2:0] roundingMode,
        output [(expWidth + sigWidth):0] out,
        output [4:0] exceptionFlags,
        output [expWidth + sigWidth-1:0] out_imul
    );

    wire invalidExc, out_isNaN, out_isInf, out_isZero, out_sign;
    wire signed [(expWidth + 1):0] out_sExp;
    wire [(sigWidth + 2):0] out_sig;
    mulAddRecFNToRaw#(expWidth, sigWidth, imulEn)
        mulAddRecFNToRaw(
            control,
            op,
            a,
            b,
            c,
            roundingMode,
            invalidExc,
            out_isNaN,
            out_isInf,
            out_isZero,
            out_sign,
            out_sExp,
            out_sig,
            out_imul
        );
    roundRawFNToRecFN#(expWidth, sigWidth, 0)
        roundRawOut(
            control,
            invalidExc,
            1'b0,
            out_isNaN,
            out_isInf,
            out_isZero,
            out_sign,
            out_sExp,
            out_sig,
            roundingMode,
            out,
            exceptionFlags
        );
endmodule

