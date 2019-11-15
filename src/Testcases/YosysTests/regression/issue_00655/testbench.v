module testbench;
    reg clk;

    initial begin
        $dumpfile("testbench.vcd");
        $dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end

    reg i = 0;
    reg out;
	wire b;

	always @(posedge clk)
	begin
		i = i + 1;
	end

	wire serial_tx;
	reg serial_rx;
	reg clk100;
	reg cpu_reset;
	wire eth_ref_clk;
	wire user_led0;
	wire user_led1;
	wire user_led2;
	wire user_led3;
	reg user_sw0;
	reg user_sw1;
	reg user_sw2;
	reg user_sw3;
	reg user_btn0;
	reg user_btn1;
	reg user_btn2;
	reg user_btn3;
	wire spiflash_1x_cs_n;
	wire spiflash_1x_mosi;
	reg spiflash_1x_miso;
	wire spiflash_1x_wp;
	wire spiflash_1x_hold;
	wire [13:0] ddram_a;
	wire [2:0] ddram_ba;
	wire ddram_ras_n;
	wire ddram_cas_n;
	wire ddram_we_n;
	wire ddram_cs_n;
	wire [1:0] ddram_dm;
	wire [15:0] ddram_dq;
	wire [1:0] ddram_dqs_p;
	wire [1:0] ddram_dqs_n;
	wire ddram_clk_p;
	wire ddram_clk_n;
	wire ddram_cke;
	wire ddram_odt;
	wire ddram_reset_n;


	top uut (
	serial_tx,
	serial_rx,
	clk,
	cpu_reset,
	eth_ref_clk,
	user_led0,
	user_led1,
	user_led2,
	user_led3,
	user_sw0,
	user_sw1,
	user_sw2,
	user_sw3,
	user_btn0,
	user_btn1,
	user_btn2,
	user_btn3,
	spiflash_1x_cs_n,
	spiflash_1x_mosi,
	spiflash_1x_miso,
	spiflash_1x_wp,
	spiflash_1x_hold,
	ddram_a,
	ddram_ba,
	ddram_ras_n,
	ddram_cas_n,
	ddram_we_n,
	ddram_cs_n,
	ddram_dm,
	ddram_dq,
	ddram_dqs_p,
	ddram_dqs_n,
	ddram_clk_p,
	ddram_clk_n,
	ddram_cke,
	ddram_odt,
	ddram_reset_n
);

endmodule
