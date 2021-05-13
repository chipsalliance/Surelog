module GOOD1();
endmodule

module GOOD2();
endmodule

module dut1 ();
localparam bit          HasSndScratch  = 1'b1;
if (HasSndScratch) begin : gen_rom_snd_scratch
  GOOD1 cond_module();
end else begin : gen_rom_one_scratch
  BAD1 cond_module();
end
endmodule


module dut2 ();
localparam bit          HasSndScratch  = 1'b0;
if (HasSndScratch) begin : gen_rom_snd_scratch
  BAD2 cond_module();
end else begin : gen_rom_one_scratch
  GOOD2 cond_module();
end
endmodule
