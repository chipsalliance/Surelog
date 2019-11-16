module top(
    input clk,
    input rst,

    output wire  din_ready,
    input  wire din_valid,
    input  wire [2:0] din_data,
    input  wire         dout_ready,
    output wire          dout_valid,
    output wire  [2:0] dout_data

);

   wire                dout1_ready;
   wire                dout1_valid;
   wire [0:0]          dout1_data;

   wire                dout2_ready;
   wire                dout2_valid;
   wire [1:0]          dout2_data;

   wire [1:0]          din_bc_ready;
   wire [1:0]          din_bc_valid;
   wire [5:0]          din_bc_data;

   bc #(
        .SIZE(2'd2),
        .WIDTH(2'd3)
        )
   bc_din (
           .clk(clk),
           .rst(rst),

           .din_valid(din_valid),
           .din_ready(din_ready),
           .din_data(din_data),

           .dout_valid(din_bc_valid),
           .dout_ready(din_bc_ready),
           .dout_data(din_bc_data)
           );


   demux demux (
                           .clk(clk),
                           .rst(rst),

                           .din_valid(din_bc_valid[0]),
                           .din_ready(din_bc_ready[0]),
                           .din_data(din_bc_data[2:0]),

                           .dout0_valid(dout1_valid),
                           .dout0_ready(dout1_ready),
                           .dout0_data(dout1_data),

                           .dout1_valid(dout2_valid),
                           .dout1_ready(dout2_ready),
                           .dout1_data(dout2_data)
                           );

   mux mux (
            .clk(clk),
            .rst(rst),

            .ctrl_valid(din_bc_valid[1]),
            .ctrl_ready(din_bc_ready[1]),
            .ctrl_data(din_bc_data[2]),

            .din0_valid(dout1_valid),
            .din0_ready(dout1_ready),
            .din0_data(dout1_data),

            .din1_valid(dout2_valid),
            .din1_ready(dout2_ready),
            .din1_data(dout2_data),

            .dout_valid(dout_valid),
            .dout_ready(dout_ready),
            .dout_data(dout_data)
            );



endmodule
