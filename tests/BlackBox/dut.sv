//`include "defines.svh"

//import defines::*;

module core ();

int wb_writeback_en;

endmodule


module nyuzi();

    genvar core_idx;
    generate
        for (core_idx = 0; core_idx < 1; core_idx++)
        begin : core_gen
            core  core();
        end
    endgenerate
endmodule



module top();

`define CORE0 nyuzi.core_gen[0].core

nyuzi  nyuzi();

    assign o = `CORE0.wb_writeback_en;


endmodule