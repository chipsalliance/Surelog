
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

module
    mulAddRecF16_add (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [16:0] a,
        input [16:0] b,
        input [2:0] roundingMode,
        output [16:0] out,
        output [4:0] exceptionFlags,
        output [15:0] out_imul
    );

    wire [16:0] recF16_1 = 'h08000;
    mulAddRecFN#(5, 11)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, recF16_1, b, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF32_add (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [32:0] a,
        input [32:0] b,
        input [2:0] roundingMode,
        output [32:0] out,
        output [4:0] exceptionFlags,
        output [31:0] out_imul
    );

    wire [32:0] recF32_1 = 33'h080000000;
    mulAddRecFN#(8, 24)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, recF32_1, b, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF64_add (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [64:0] a,
        input [64:0] b,
        input [2:0] roundingMode,
        output [64:0] out,
        output [4:0] exceptionFlags,
        output [63:0] out_imul
    );

    wire [64:0] recF64_1 = 65'h08000000000000000;
    mulAddRecFN#(11, 53)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, recF64_1, b, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF128_add (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] a,
        input [128:0] b,
        input [2:0] roundingMode,
        output [128:0] out,
        output [4:0] exceptionFlags
    );
    wire [127:0] out_imul;
    wire [128:0] recF128_1 = 129'h080000000000000000000000000000000;
    mulAddRecFN#(15, 113, 0)
        mulAddRecFN(
            control, 3'b0, a, recF128_1, b, roundingMode, out, exceptionFlags, out_imul
        );

endmodule

module
    mulAddRecF16_mul (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [16:0] a,
        input [16:0] b,
        input [2:0] roundingMode,
        output [16:0] out,
        output [4:0] exceptionFlags,
        output [15:0] out_imul
    );

    wire [16:0] zeroAddend = {a[16] ^ b[16], 16'b0};
    mulAddRecFN#(5, 11)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, b, zeroAddend, roundingMode, out, exceptionFlags, out_imul
        );

endmodule

module
    mulAddRecF32_mul (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [32:0] a,
        input [32:0] b,
        input [2:0] roundingMode,
        output [32:0] out,
        output [4:0] exceptionFlags,
        output [31:0] out_imul
    );

    wire [32:0] zeroAddend = {a[32] ^ b[32], 32'b0};
    mulAddRecFN#(8, 24)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, b, zeroAddend, roundingMode, out, exceptionFlags, out_imul
        );

endmodule

module
    mulAddRecF64_mul (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [64:0] a,
        input [64:0] b,
        input [2:0] roundingMode,
        output [64:0] out,
        output [4:0] exceptionFlags,
        output [63:0] out_imul
    );

    wire [64:0] zeroAddend = {a[64] ^ b[64], 64'b0};
    mulAddRecFN#(11, 53)
        mulAddRecFN(
            control, {int_mul, 2'b0}, a, b, zeroAddend, roundingMode, out, exceptionFlags, out_imul
        );

endmodule

module
    mulAddRecF128_mul (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] a,
        input [128:0] b,
        input [2:0] roundingMode,
        output [128:0] out,
        output [4:0] exceptionFlags
    );

    wire [128:0] zeroAddend = {a[128] ^ b[128], 128'b0};
    wire [127:0] out_imul;
    mulAddRecFN#(15, 113, 0)
        mulAddRecFN(
            control, 3'b0, a, b, zeroAddend, roundingMode, out, exceptionFlags,out_imul
        );

endmodule

module
    mulAddRecF16 (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [2:0] op,
        input [16:0] a,
        input [16:0] b,
        input [16:0] c,
        input [2:0] roundingMode,
        output [16:0] out,
        output [4:0] exceptionFlags,
        output [15:0] out_imul
    );

    mulAddRecFN#(5, 11)
        mulAddRecFN(control, op, a, b, c, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF32 (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [2:0] op,
        input [32:0] a,
        input [32:0] b,
        input [32:0] c,
        input [2:0] roundingMode,
        output [32:0] out,
        output [4:0] exceptionFlags,
        output [31:0] out_imul
    );

    mulAddRecFN#(8, 24)
        mulAddRecFN(control, op, a, b, c, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF64 (
        input [(`floatControlWidth - 1):0] control,
        input int_mul,
        input [2:0] op,
        input [64:0] a,
        input [64:0] b,
        input [64:0] c,
        input [2:0] roundingMode,
        output [64:0] out,
        output [4:0] exceptionFlags,
        output [63:0] out_imul
    );

    mulAddRecFN#(11, 53)
        mulAddRecFN(control, op, a, b, c, roundingMode, out, exceptionFlags, out_imul);

endmodule

module
    mulAddRecF128 (
        input [(`floatControlWidth - 1):0] control,
        input [2:0] op,
        input [128:0] a,
        input [128:0] b,
        input [128:0] c,
        input [2:0] roundingMode,
        output [128:0] out,
        output [4:0] exceptionFlags
    );

    wire [127:0] out_imul;

    mulAddRecFN#(15, 113)
        mulAddRecFN(control, op, a, b, c, roundingMode, out, exceptionFlags, out_imul);

endmodule

