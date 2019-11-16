`default_nettype none

module top
        (
         inout wire [7:0] data_io,
         output reg [7:0] rdata_o,
         input wire [7:0] wdata_i,
         input wire       rxf_n_i,
         input wire       txe_n_i,
         output reg       rd_n_o,
         output reg       wr_n_o,
         output reg       siwua_n_o,
         input wire       clk_i,
         output reg       oe_n_o,
         input wire       suspend_n_i
         );

        initial begin
                rdata_o = {8{1'b0}};
                rd_n_o = 1;
                wr_n_o = 1;
                siwua_n_o = 1; /* Never flush TX data. */
        end

        assign data_io = (!txe_n_i && !wr_n_o) ? wdata_i : {8{1'bz}};

        always @(posedge clk_i, negedge suspend_n_i) begin
                if (!suspend_n_i) begin
                        wr_n_o <= 1;
                        rd_n_o <= 1;
                        oe_n_o <= 1;
                        rdata_o <= {8{1'b0}};
                end
                else begin
                        // Give TX bus precedence.
                        if (!txe_n_i) begin
                                wr_n_o <= 0;
                                rd_n_o <= 1;
                                oe_n_o <= 1;
                                rdata_o <= {8{1'b0}};
                        end
                        // oe_n_o must be driven low at least one period before we can read.
                        else if (!rxf_n_i && oe_n_o) begin
                                wr_n_o <= 1;
                                rd_n_o <= 1;
                                oe_n_o <= 0;
                                rdata_o <= {8{1'b0}};
                        end
                        else if (!rxf_n_i && !oe_n_o) begin
                                wr_n_o <= 1;
                                rd_n_o <= 0;
                                oe_n_o <= 0;
                                rdata_o <= data_io;
                        end
                        else begin
                                wr_n_o <= 1;
                                rd_n_o <= 1;
                                oe_n_o <= 1;
                                rdata_o <= {8{1'b0}};
                        end
                end // else: !if(!suspend_n_i)
        end

endmodule // usb
