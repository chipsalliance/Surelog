
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
| Computes a division or square root for floating-point in recoded form.
| Multiple clock cycles are needed for each division or square-root operation,
| except possibly in special cases.
*----------------------------------------------------------------------------*/

module
    divSqrtRecFNToRaw_small#(
        parameter expWidth = 3, parameter sigWidth = 3, parameter options = 0
    ) (
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        input nReset,
        input clock,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        input [(`floatControlWidth - 1):0] control,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        output inReady,
        input inValid,
        input sqrtOp,
        input [(expWidth + sigWidth):0] a,
        input [(expWidth + sigWidth):0] b,
        input [2:0] roundingMode,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        output outValid,
        output sqrtOpOut,
        output [2:0] roundingModeOut,
        output invalidExc,
        output infiniteExc,
        output out_isNaN,
        output out_isInf,
        output out_isZero,
        output out_sign,
        output signed [(expWidth + 1):0] out_sExp,
        output [(sigWidth + 2):0] out_sig
    );
`include "HardFloat_localFuncs.vi"

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire isNaNA_S, isInfA_S, isZeroA_S, signA_S;
    wire signed [(expWidth + 1):0] sExpA_S;
    wire [sigWidth:0] sigA_S;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN_a(
            a, isNaNA_S, isInfA_S, isZeroA_S, signA_S, sExpA_S, sigA_S);
    wire isSigNaNA_S;
    isSigNaNRecFN#(expWidth, sigWidth) isSigNaN_a(a, isSigNaNA_S);
    wire isNaNB_S, isInfB_S, isZeroB_S, signB_S;
    wire signed [(expWidth + 1):0] sExpB_S;
    wire [sigWidth:0] sigB_S;
    recFNToRawFN#(expWidth, sigWidth)
        recFNToRawFN_b(
            b, isNaNB_S, isInfB_S, isZeroB_S, signB_S, sExpB_S, sigB_S);
    wire isSigNaNB_S;
    isSigNaNRecFN#(expWidth, sigWidth) isSigNaN_b(b, isSigNaNB_S);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire notSigNaNIn_invalidExc_S_div =
        (isZeroA_S && isZeroB_S) || (isInfA_S && isInfB_S);
    wire notSigNaNIn_invalidExc_S_sqrt = !isNaNA_S && !isZeroA_S && signA_S;
    wire majorExc_S =
        sqrtOp ? isSigNaNA_S || notSigNaNIn_invalidExc_S_sqrt
            : isSigNaNA_S || isSigNaNB_S || notSigNaNIn_invalidExc_S_div
                  || (!isNaNA_S && !isInfA_S && isZeroB_S);
    wire isNaN_S =
        sqrtOp ? isNaNA_S || notSigNaNIn_invalidExc_S_sqrt
            : isNaNA_S || isNaNB_S || notSigNaNIn_invalidExc_S_div;
`ifdef HardFloat_propagateNaNPayloads
    wire signNaN_S;
    wire [(sigWidth - 2):0] fractNaN_S;
    propagateFloatNaN_divSqrt#(sigWidth)
        propagateNaN(
            control,
            sqrtOp,
            isNaNA_S,
            signA_S,
            sigA_S[(sigWidth - 2):0],
            isNaNB_S,
            signB_S,
            sigB_S[(sigWidth - 2):0],
            signNaN_S,
            fractNaN_S
        );
`endif
    wire isInf_S  = sqrtOp ? isInfA_S  : isInfA_S  || isZeroB_S;
    wire isZero_S = sqrtOp ? isZeroA_S : isZeroA_S || isInfB_S;
    wire sign_S = signA_S ^ (!sqrtOp && signB_S);
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire specialCaseA_S = isNaNA_S || isInfA_S || isZeroA_S;
    wire specialCaseB_S = isNaNB_S || isInfB_S || isZeroB_S;
    wire normalCase_S_div  = !specialCaseA_S && !specialCaseB_S;
    wire normalCase_S_sqrt = !specialCaseA_S && !signA_S;
    wire normalCase_S = sqrtOp ? normalCase_S_sqrt : normalCase_S_div;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire signed [(expWidth + 2):0] sExpQuot_S_div =
        sExpA_S + {{3{sExpB_S[expWidth]}}, ~sExpB_S[(expWidth - 1):0]};
    wire signed [(expWidth + 1):0] sSatExpQuot_S_div =
        {(7<<(expWidth - 2) <= sExpQuot_S_div) ? 4'b0110
             : sExpQuot_S_div[(expWidth + 1):(expWidth - 2)],
         sExpQuot_S_div[(expWidth - 3): 0]};
    wire evenSqrt_S = sqrtOp && !sExpA_S[0];
    wire oddSqrt_S  = sqrtOp &&  sExpA_S[0];
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    reg [(clog2(sigWidth + 3) - 1):0] cycleNum;
    reg sqrtOp_Z, majorExc_Z;
    reg isNaN_Z, isInf_Z, isZero_Z, sign_Z;
    reg signed [(expWidth + 1):0] sExp_Z;
    reg [(sigWidth - 2):0] fractB_Z;
    reg [2:0] roundingMode_Z;
    /*------------------------------------------------------------------------
    | (The most-significant and least-significant bits of 'rem_Z' are needed
    | only for square roots.)
    *------------------------------------------------------------------------*/
    reg [(sigWidth + 1):0] rem_Z;
    reg notZeroRem_Z;
    reg [(sigWidth + 1):0] sigX_Z;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire idle = (cycleNum == 0);
    assign inReady = (cycleNum <= 1);
    wire entering = inReady && inValid;
    wire entering_normalCase = entering && normalCase_S;
    wire skipCycle2 = (cycleNum == 3) && sigX_Z[sigWidth + 1];
    always @(negedge nReset, posedge clock) begin
        if (!nReset) begin
            cycleNum <= 0;
        end else begin
            if (!idle || inValid) begin
                cycleNum <=
                      (entering && !normalCase_S ? 1 : 0)
                    | (entering_normalCase
                           ? (sqrtOp ? (sExpA_S[0] ? sigWidth : sigWidth + 1)
                                  : sigWidth + 2)
                           : 0)
                    | (!idle && !skipCycle2 ? cycleNum - 1 : 0)
                    | (!idle &&  skipCycle2 ? 1            : 0);
            end
        end
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    always @(posedge clock) begin
      if (!nReset) begin
            sqrtOp_Z <= 1'b0;
            majorExc_Z <= 1'b0;
            isNaN_Z <= 1'b0;
            isInf_Z <= 1'b0;
            isZero_Z <= 1'b0;
            sign_Z <= 1'b0;
            sExp_Z <= '0;
            roundingMode_Z <= '0;
            fractB_Z <= '0;
      end
      else begin
        if (entering) begin
            sqrtOp_Z   <= sqrtOp;
            majorExc_Z <= majorExc_S;
            isNaN_Z    <= isNaN_S;
            isInf_Z    <= isInf_S;
            isZero_Z   <= isZero_S;
`ifdef HardFloat_propagateNaNPayloads
            sign_Z <= isNaN_S ? signNaN_S : sign_S;
`else
            sign_Z <= sign_S;
`endif
        end
        if (entering_normalCase) begin
            sExp_Z <=
                sqrtOp ? (sExpA_S>>>1) + (1<<(expWidth - 1))
                    : sSatExpQuot_S_div;
            roundingMode_Z <= roundingMode;
        end
        if (entering_normalCase && !sqrtOp) begin
            fractB_Z <= sigB_S[(sigWidth - 2):0];
        end
      end
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    wire [1:0] decHiSigA_S = sigA_S[(sigWidth - 1):(sigWidth - 2)] - 1;
    wire [(sigWidth + 2):0] rem =
          (inReady && !oddSqrt_S ? sigA_S<<1 : 0)
        | (inReady &&  oddSqrt_S
               ? {decHiSigA_S, sigA_S[(sigWidth - 3):0], 3'b0} : 0)
        | (!inReady ? rem_Z<<1 : 0);
    wire [sigWidth:0] bitMask = ({{(sigWidth + 2){1'b0}}, 1'b1}<<cycleNum)>>2;
    wire [(sigWidth + 1):0] trialTerm =
          ( inReady && !sqrtOp    ? sigB_S<<1           : 0)
        | ( inReady && evenSqrt_S ? 1<<sigWidth         : 0)
        | ( inReady && oddSqrt_S  ? 5<<(sigWidth - 1)   : 0)
        | (!inReady && !sqrtOp_Z  ? {1'b1, fractB_Z}<<1 : 0)
        | (!inReady &&  sqrtOp_Z  ? sigX_Z<<1 | bitMask : 0);
    wire signed [(sigWidth + 3):0] trialRem = rem - trialTerm;
    wire newBit = (0 <= trialRem);
    always @(posedge clock) begin
      if (!nReset) begin
        rem_Z <='0;
        sigX_Z <='0;
        notZeroRem_Z <= 1'b0;
      end
      else begin
        if (entering_normalCase || (cycleNum > 2)) begin
            rem_Z <= newBit ? trialRem : rem;
        end
`ifdef HardFloat_propagateNaNPayloads
        if (
            (entering && isNaN_S) || entering_normalCase
                || (!inReady && newBit)
        ) begin
            notZeroRem_Z <= (trialRem != 0);
            sigX_Z <=
                  (inReady &&  isNaN_S         ? {1'b1, fractNaN_S, 2'b00} : 0)
                | (inReady && !isNaN_S && !sqrtOp ? newBit<<(sigWidth + 1) : 0)
                | (inReady && !isNaN_S &&  sqrtOp ? 1<<sigWidth            : 0)
                | (inReady && !isNaN_S && oddSqrt_S
                                                 ? newBit<<(sigWidth - 1) : 0)
                | (!inReady                      ? sigX_Z | bitMask       : 0);
        end
`else
        if (entering_normalCase || (!inReady && newBit)) begin
            notZeroRem_Z <= (trialRem != 0);
            sigX_Z <=
                  ( inReady && !sqrtOp   ? newBit<<(sigWidth + 1) : 0)
                | ( inReady &&  sqrtOp   ? 1<<sigWidth            : 0)
                | ( inReady && oddSqrt_S ? newBit<<(sigWidth - 1) : 0)
                | (!inReady              ? sigX_Z | bitMask       : 0);
        end
`endif
      end
    end
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    assign outValid = (cycleNum == 1);
    assign sqrtOpOut       = sqrtOp_Z;
    assign roundingModeOut = roundingMode_Z;
    assign invalidExc  = majorExc_Z &&  isNaN_Z;
    assign infiniteExc = majorExc_Z && !isNaN_Z;
    assign out_isNaN  = isNaN_Z;
    assign out_isInf  = isInf_Z;
    assign out_isZero = isZero_Z;
    assign out_sign   = sign_Z;
    assign out_sExp   = sExp_Z;
    assign out_sig    = {sigX_Z, notZeroRem_Z};

endmodule

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

module
    divSqrtRecFN_small#(
        parameter expWidth = 3, parameter sigWidth = 3, parameter options = 0
    ) (
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        input nReset,
        input clock,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        input [(`floatControlWidth - 1):0] control,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        output inReady,
        input inValid,
        input sqrtOp,
        input [(expWidth + sigWidth):0] a,
        input [(expWidth + sigWidth):0] b,
        input [2:0] roundingMode,
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        output outValid,
        output sqrtOpOut,
        output [(expWidth + sigWidth):0] out,
        output [4:0] exceptionFlags
    );

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    //wire sqrtOpOut;
    wire [2:0] roundingModeOut;
    wire invalidExc, infiniteExc, out_isNaN, out_isInf, out_isZero, out_sign;
    wire signed [(expWidth + 1):0] out_sExp;
    wire [(sigWidth + 2):0] out_sig;
    divSqrtRecFNToRaw_small#(expWidth, sigWidth, options)
        divSqrtRecFNToRaw(
            nReset,
            clock,
            control,
            inReady,
            inValid,
            sqrtOp,
            a,
            b,
            roundingMode,
            outValid,
            sqrtOpOut,
            roundingModeOut,
            invalidExc,
            infiniteExc,
            out_isNaN,
            out_isInf,
            out_isZero,
            out_sign,
            out_sExp,
            out_sig
        );
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    roundRawFNToRecFN#(expWidth, sigWidth, 0)
        roundRawOut(
            control,
            invalidExc,
            infiniteExc,
            out_isNaN,
            out_isInf,
            out_isZero,
            out_sign,
            out_sExp,
            out_sig,
            roundingModeOut,
            out,
            exceptionFlags
        );

endmodule

