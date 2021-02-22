
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
    recF16ToUi32 (
        input [(`floatControlWidth - 1):0] control,
        input [16:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(5, 11, 32)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF16ToUi64 (
        input [(`floatControlWidth - 1):0] control,
        input [16:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(5, 11, 64)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF16ToI32 (
        input [(`floatControlWidth - 1):0] control,
        input [16:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(5, 11, 32)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF16ToI64 (
        input [(`floatControlWidth - 1):0] control,
        input [16:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(5, 11, 64)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF32ToUi32 (
        input [(`floatControlWidth - 1):0] control,
        input [32:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(8, 24, 32)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF32ToUi64 (
        input [(`floatControlWidth - 1):0] control,
        input [32:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(8, 24, 64)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF32ToI32 (
        input [(`floatControlWidth - 1):0] control,
        input [32:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(8, 24, 32)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF32ToI64 (
        input [(`floatControlWidth - 1):0] control,
        input [32:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(8, 24, 64)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF64ToUi32 (
        input [(`floatControlWidth - 1):0] control,
        input [64:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(11, 53, 32)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF64ToUi64 (
        input [(`floatControlWidth - 1):0] control,
        input [64:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(11, 53, 64)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF64ToI32 (
        input [(`floatControlWidth - 1):0] control,
        input [64:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(11, 53, 32)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF64ToI64 (
        input [(`floatControlWidth - 1):0] control,
        input [64:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(11, 53, 64)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF128ToUi32 (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(15, 113, 32)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF128ToUi64 (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(15, 113, 64)
        recFNToIN(control, in, roundingMode, 0, out, exceptionFlags);

endmodule

module
    recF128ToI32 (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] in,
        input [2:0] roundingMode,
        output [31:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(15, 113, 32)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

module
    recF128ToI64 (
        input [(`floatControlWidth - 1):0] control,
        input [128:0] in,
        input [2:0] roundingMode,
        output [63:0] out,
        output [2:0] exceptionFlags
    );

    recFNToIN#(15, 113, 64)
        recFNToIN(control, in, roundingMode, 1, out, exceptionFlags);

endmodule

