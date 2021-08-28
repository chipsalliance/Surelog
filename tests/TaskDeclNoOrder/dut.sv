module dut #()();

task automatic set_pll_fast_run;
    static logic [5:0] band_vco1_val='h1A;
    static logic [5:0] fine_vco1_val='h04;
    static logic [5:0] band_vco2_val='h04;
    static logic [5:0] fine_vco2_val='h1C;
    logic pll_core_ready;
    input  integer pll_vco1_freq_MHz;
    input  integer pll_vco2_freq_MHz;
    input  integer vco_sel;
    output int err;
    logic [1:0] unused_1;
    integer     unused_2;
    begin
        // igen enable
        set_ibias_en(1'b1);
        #10ns;
    
    end
endtask


endmodule

