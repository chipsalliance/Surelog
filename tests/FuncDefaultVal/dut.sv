module top();

bit[31:0] [31:0] gpr[2];

function string dasm( input tid=0);
    dasm = (opcode[1:0] == 2'b11) ? dasm32(opcode, pc, tid) : dasm16(opcode, pc, tid);
    if(regn) gpr[tid][regn] = regv;
endfunction

endmodule
