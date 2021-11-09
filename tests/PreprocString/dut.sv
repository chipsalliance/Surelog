module test();

`define message(TOTO) TATA
   
`define MAKE_MEM_PATH(filename) `"`MEM_ROOT/filename`message`"
    initial begin
    $display(`MAKE_MEM_PATH(rom.mem));
    end
endmodule
