module f16_prom (
    input  wire [15:0] addr,
    output wire [15:0] data_out,
    input  wire clk
);

    (* mem2reg *) reg [15:0] rom [0:15];
    reg [15:0] do;

    initial
        $readmemh("../bootrom.hex", rom);

    always @(posedge clk)
        do <= rom[addr[3:0]];

    assign data_out = do;

endmodule // f16_prom
