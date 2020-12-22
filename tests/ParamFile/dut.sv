`define PARAM_FILE ""

module dut (output logic o);
   parameter SRAMInitFile = `PARAM_FILE;
   ram_1p #(
     .MemInitFile(SRAMInitFile)
   ) u_ram (
           .out(o)
   );
endmodule

module ram_1p #(
        parameter     MemInitFile = ""
) (
        output logic out
);

initial begin
  if (MemInitFile != "") begin : gen_meminit
      $display("Initializing memory %m from file '%s'.", MemInitFile);
      assign out = 1'b1;
  end

  if (MemInitFile == "") begin : gen_nomeminit
      $display("Initializing memory file is empty.");
      assign out = 1'b0;
  end
end

endmodule

