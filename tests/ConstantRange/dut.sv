module GOOD();

endmodule


module dut #()();
parameter int NMioPads = 8;
parameter logic [NMioPads - 1:0] ConnectDioIn = 8'b11110000;
parameter logic [NMioPads - 1:0] ConnectDioOut = 8'b11110000;
   
for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_pads
     if (ConnectDioIn[k] && ConnectDioOut[k]) begin : gen_mio_inout
             GOOD good();
     end
end

if (ConnectDioIn[0]) begin
   BAD bad();
end
   
endmodule // dut

