package bsg_hardfloat_pkg;

// We use enumeration to represent the operation types accepted by fma.
// In original design, opcode determines whether to negate multiplicand or bias. 
// By setting op[0] to 1, the opC will be negated before taking part in FMA.
// By asserting op[1], the opA*opB will be negated as well.
// To support RV multiply, we introduce op[2]. When it's 1, a integer multiply opA*opB is carried regardless of op[1:0].
// For more information, please check the document.
//! WARNING: DO NOT CHANGE THE ENUMERATION VALUE! IT'S MEANINGFUL FOR AND COMPATIBLE WITH HARDFLOAT.
typedef enum bit[2:0] {
    ePM_PB = 3'b000, // Positive Multiplicand(PM), Positive Bias(PB): a*b + c
    ePM_NB = 3'b001, // Positive Multiplicand(PM), Negative Bias(NB): a*b - c
    eNM_PB = 3'b010, // Negative Multiplicand(NM), Positive Bias(PB): -(a*b) + c
    eNM_NB = 3'b011, // Negative Multiplicand(NM), Negative Bias(NB): -(a*b) - c
    eIMUL  = 3'b100  // Integer Multiply.
} fma_opcode_e;

parameter integer fp32_exp_gp = 8;   // FP32 exponent width
parameter integer fp32_sig_gp = 23;  // FP32 significand width

parameter integer fp64_exp_gp = 11;  // FP64 exponent width
parameter integer fp64_sig_gP = 52;  // FP64 significand width

endpackage
