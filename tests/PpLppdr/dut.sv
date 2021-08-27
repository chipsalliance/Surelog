`define DDR_CMN_VREF_M0_CFG_ADR 32'h00000008
  `define DDR_CMN_VREF_M0_CFG_EN_FIELD 9  

`define REG_ADR(rname)      ```rname``_ADR

`define FRANGE(rname,fname) ```rname``_``fname``_FIELD

`define FWIDTH(rname,fname) ```rname``_``fname``_FIELD_WIDTH

`define CSR_WRF1(offset,rname,fname,fval) \
                                   csr_read(``offset``,`REG_ADR(``rname``), wdata); \
                                   wdata[`FRANGE(``rname``,``fname``)] = fval; \
                                   csr_write(``offset``,`REG_ADR(``rname``), wdata)


module top();

  task automatic set_refgen_en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_VREF_M0_CFG,EN,en);
    end
endtask


endmodule // top
