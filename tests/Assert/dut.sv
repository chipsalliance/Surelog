module dut();


assert property ( @(posedge Clock)  strap_en_i |=> ##0 !strap_en_i [*]);


endmodule // dut
