



module GOOD();

endmodule // GOOD

module ScratchPad ();
parameter M_COUNT = 4;
parameter M_REGIONS = 1;
parameter ADDR_WIDTH = 32;
parameter M_ADDR_WIDTH = {M_COUNT{{M_REGIONS{32'd24}}}};
function [M_COUNT*M_REGIONS*ADDR_WIDTH-1:0] calcBaseAddrs(input [31:0] dummy);
    integer i;
    reg [ADDR_WIDTH-1:0] base;
    reg [ADDR_WIDTH-1:0] width;
    reg [ADDR_WIDTH-1:0] size;
    reg [ADDR_WIDTH-1:0] mask;
    begin
        calcBaseAddrs = {M_COUNT*M_REGIONS*ADDR_WIDTH{1'b0}};
        base = 0;
        for (i = 0; i < M_COUNT*M_REGIONS; i = i + 1) begin
            width = M_ADDR_WIDTH[i*32 +: 32];
            mask = {ADDR_WIDTH{1'b1}} >> (ADDR_WIDTH - width);
            size = mask + 1;
            if (width > 0) begin
                if ((base & mask) != 0) begin
                   base = base + size - (base & mask); // align
                end
                calcBaseAddrs[i * ADDR_WIDTH +: ADDR_WIDTH] = base;
                base = base + size; // increment
            end
        end
    end
endfunction

parameter M_BASE_ADDR_INT = calcBaseAddrs(0);

if (M_BASE_ADDR_INT == 128'b00000011000000000000000000000000000000100000000000000000000000000000000100000000000000000000000000000000000000000000000000000000) begin
  GOOD good();
end



endmodule
