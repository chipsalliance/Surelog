/* Machine-generated using LiteX gen */
module top(
	output reg serial_tx,
	input serial_rx,
	output MOTEA,
	output DRVSA,
	output STEP,
	output DIR,
	output WDATA,
	output WGATE,
	input TRK00,
	output user_led,
	input WPT,
	output user_led_1,
	output SIDE1,
	input INDEX,
	input RDATA,
	output reg user_led_2,
	output reg user_led_3,
	input clk50
);

wire [29:0] ibm360dd_sram_bus_adr;
wire [31:0] ibm360dd_sram_bus_dat_w;
wire [31:0] ibm360dd_sram_bus_dat_r;
wire [3:0] ibm360dd_sram_bus_sel;
wire ibm360dd_sram_bus_cyc;
wire ibm360dd_sram_bus_stb;
reg ibm360dd_sram_bus_ack = 1'd0;
wire ibm360dd_sram_bus_we;
wire [2:0] ibm360dd_sram_bus_cti;
wire [1:0] ibm360dd_sram_bus_bte;
reg ibm360dd_sram_bus_err = 1'd0;
wire [9:0] ibm360dd_sram_adr;
wire [31:0] ibm360dd_sram_dat_r;
reg [3:0] ibm360dd_sram_we = 1'd0;
wire [31:0] ibm360dd_sram_dat_w;
reg [13:0] ibm360dd_interface_adr = 1'd0;
reg ibm360dd_interface_we = 1'd0;
reg [31:0] ibm360dd_interface_dat_w = 1'd0;
wire [31:0] ibm360dd_interface_dat_r;
wire [29:0] ibm360dd_bus_wishbone_adr;
wire [31:0] ibm360dd_bus_wishbone_dat_w;
reg [31:0] ibm360dd_bus_wishbone_dat_r = 1'd0;
wire [3:0] ibm360dd_bus_wishbone_sel;
wire ibm360dd_bus_wishbone_cyc;
wire ibm360dd_bus_wishbone_stb;
reg ibm360dd_bus_wishbone_ack = 1'd0;
wire ibm360dd_bus_wishbone_we;
wire [2:0] ibm360dd_bus_wishbone_cti;
wire [1:0] ibm360dd_bus_wishbone_bte;
reg ibm360dd_bus_wishbone_err = 1'd0;
reg [1:0] ibm360dd_counter = 1'd0;
reg [31:0] ibm360dd_storage = 24'd9895604;
reg ibm360dd_sink_valid = 1'd0;
reg ibm360dd_sink_ready = 1'd0;
wire ibm360dd_sink_last;
reg [7:0] ibm360dd_sink_payload_data = 1'd0;
reg ibm360dd_uart_clk_txen = 1'd0;
reg [31:0] ibm360dd_phase_accumulator_tx = 1'd0;
reg [7:0] ibm360dd_tx_reg = 1'd0;
reg [3:0] ibm360dd_tx_bitcount = 1'd0;
reg ibm360dd_tx_busy = 1'd0;
reg ibm360dd_source_valid = 1'd0;
wire ibm360dd_source_ready;
reg [7:0] ibm360dd_source_payload_data = 1'd0;
reg ibm360dd_uart_clk_rxen = 1'd0;
reg [31:0] ibm360dd_phase_accumulator_rx = 1'd0;
wire ibm360dd_rx;
reg ibm360dd_rx_r = 1'd0;
reg [7:0] ibm360dd_rx_reg = 1'd0;
reg [3:0] ibm360dd_rx_bitcount = 1'd0;
reg ibm360dd_rx_busy = 1'd0;
wire [29:0] ibm360dd_wishbone_adr;
wire [31:0] ibm360dd_wishbone_dat_w;
wire [31:0] ibm360dd_wishbone_dat_r;
wire [3:0] ibm360dd_wishbone_sel;
reg ibm360dd_wishbone_cyc = 1'd0;
reg ibm360dd_wishbone_stb = 1'd0;
wire ibm360dd_wishbone_ack;
reg ibm360dd_wishbone_we = 1'd0;
reg [2:0] ibm360dd_wishbone_cti = 1'd0;
reg [1:0] ibm360dd_wishbone_bte = 1'd0;
wire ibm360dd_wishbone_err;
reg [2:0] ibm360dd_byte_counter = 1'd0;
reg ibm360dd_byte_counter_reset = 1'd0;
reg ibm360dd_byte_counter_ce = 1'd0;
reg [2:0] ibm360dd_word_counter = 1'd0;
reg ibm360dd_word_counter_reset = 1'd0;
reg ibm360dd_word_counter_ce = 1'd0;
reg [7:0] ibm360dd_cmd = 1'd0;
reg ibm360dd_cmd_ce = 1'd0;
reg [7:0] ibm360dd_length = 1'd0;
reg ibm360dd_length_ce = 1'd0;
reg [31:0] ibm360dd_address = 1'd0;
reg ibm360dd_address_ce = 1'd0;
reg [31:0] ibm360dd_data = 1'd0;
reg ibm360dd_rx_data_ce = 1'd0;
reg ibm360dd_tx_data_ce = 1'd0;
wire ibm360dd_reset;
wire ibm360dd_wait;
wire ibm360dd_done;
reg [22:0] ibm360dd_count = 23'd5000000;
reg ibm360dd_is_ongoing = 1'd0;
reg [8:0] io_status;// = 1'd0;
reg [8:0] io_storage_full = 9'd511;
wire [8:0] io_storage;
reg io_re = 1'd0;
reg [3:0] sigs_counter = 1'd0;
reg sigs_index_edge = 1'd0;
reg sigs_latched_index = 1'd0;
reg [18:0] sigs_dat_counter = 1'd0;
reg sigs_data_edge = 1'd0;
reg sigs_latched_data = 1'd0;
wire frontend_sink_sink_valid;
wire frontend_sink_sink_ready;
reg frontend_sink_sink_last = 1'd0;
wire [1:0] frontend_sink_sink_payload_data;
reg frontend_sink_sink_payload_hit = 1'd0;
wire frontend_source_source_valid;
wire frontend_source_source_ready;
wire frontend_source_source_last;
wire [1:0] frontend_source_source_payload_data;
wire frontend_source_source_payload_hit;
wire frontend_buffer_sink_valid;
wire frontend_buffer_sink_ready;
wire frontend_buffer_sink_last;
wire [1:0] frontend_buffer_sink_payload_data;
wire frontend_buffer_sink_payload_hit;
wire frontend_buffer_source_valid;
wire frontend_buffer_source_ready;
wire frontend_buffer_source_last;
reg [1:0] frontend_buffer_source_payload_data = 1'd0;
reg frontend_buffer_source_payload_hit = 1'd0;
wire frontend_buffer_pipe_ce;
reg frontend_buffer_valid_n = 1'd0;
reg frontend_buffer_last_n = 1'd0;
wire frontend_trigger_sink_valid;
wire frontend_trigger_sink_ready;
wire frontend_trigger_sink_last;
wire [1:0] frontend_trigger_sink_payload_data;
wire frontend_trigger_sink_payload_hit;
wire frontend_trigger_source_valid;
wire frontend_trigger_source_ready;
wire frontend_trigger_source_last;
wire [1:0] frontend_trigger_source_payload_data;
reg frontend_trigger_source_payload_hit = 1'd0;
reg [1:0] frontend_trigger_value_storage_full = 1'd0;
wire [1:0] frontend_trigger_value_storage;
reg frontend_trigger_value_re = 1'd0;
reg [1:0] frontend_trigger_mask_storage_full = 1'd0;
wire [1:0] frontend_trigger_mask_storage;
reg frontend_trigger_mask_re = 1'd0;
wire [1:0] frontend_trigger_value;
wire [1:0] frontend_trigger_mask;
wire frontend_subsampler_sink_valid;
wire frontend_subsampler_sink_ready;
wire frontend_subsampler_sink_last;
wire [1:0] frontend_subsampler_sink_payload_data;
wire frontend_subsampler_sink_payload_hit;
wire frontend_subsampler_source_valid;
wire frontend_subsampler_source_ready;
wire frontend_subsampler_source_last;
wire [1:0] frontend_subsampler_source_payload_data;
wire frontend_subsampler_source_payload_hit;
reg [15:0] frontend_subsampler_value_storage_full = 1'd0;
wire [15:0] frontend_subsampler_value_storage;
reg frontend_subsampler_value_re = 1'd0;
wire [15:0] frontend_subsampler_value;
reg [15:0] frontend_subsampler_counter = 1'd0;
wire frontend_subsampler_done;
wire frontend_strideconverter_sink_valid;
wire frontend_strideconverter_sink_ready;
wire frontend_strideconverter_sink_last;
wire [1:0] frontend_strideconverter_sink_payload_data;
wire frontend_strideconverter_sink_payload_hit;
wire frontend_strideconverter_source_valid;
wire frontend_strideconverter_source_ready;
wire frontend_strideconverter_source_last;
wire [1:0] frontend_strideconverter_source_payload_data;
wire frontend_strideconverter_source_payload_hit;
wire frontend_strideconverter_converter_sink_valid;
wire frontend_strideconverter_converter_sink_ready;
wire frontend_strideconverter_converter_sink_last;
wire [2:0] frontend_strideconverter_converter_sink_payload_data;
wire frontend_strideconverter_converter_source_valid;
wire frontend_strideconverter_converter_source_ready;
wire frontend_strideconverter_converter_source_last;
wire [2:0] frontend_strideconverter_converter_source_payload_data;
wire frontend_strideconverter_converter_source_payload_valid_token_count;
wire frontend_strideconverter_source_source_valid;
wire frontend_strideconverter_source_source_ready;
wire frontend_strideconverter_source_source_last;
wire [2:0] frontend_strideconverter_source_source_payload_data;
wire frontend_asyncfifo_sink_valid;
wire frontend_asyncfifo_sink_ready;
wire frontend_asyncfifo_sink_last;
wire [1:0] frontend_asyncfifo_sink_payload_data;
wire frontend_asyncfifo_sink_payload_hit;
wire frontend_asyncfifo_source_valid;
wire frontend_asyncfifo_source_ready;
wire frontend_asyncfifo_source_last;
wire [1:0] frontend_asyncfifo_source_payload_data;
wire frontend_asyncfifo_source_payload_hit;
wire frontend_asyncfifo_asyncfifo_we;
wire frontend_asyncfifo_asyncfifo_writable;
wire frontend_asyncfifo_asyncfifo_re;
wire frontend_asyncfifo_asyncfifo_readable;
wire [3:0] frontend_asyncfifo_asyncfifo_din;
wire [3:0] frontend_asyncfifo_asyncfifo_dout;
wire frontend_asyncfifo_graycounter0_ce;
reg [3:0] frontend_asyncfifo_graycounter0_q = 1'd0;
wire [3:0] frontend_asyncfifo_graycounter0_q_next;
reg [3:0] frontend_asyncfifo_graycounter0_q_binary = 1'd0;
reg [3:0] frontend_asyncfifo_graycounter0_q_next_binary = 1'd0;
wire frontend_asyncfifo_graycounter1_ce;
reg [3:0] frontend_asyncfifo_graycounter1_q = 1'd0;
wire [3:0] frontend_asyncfifo_graycounter1_q_next;
reg [3:0] frontend_asyncfifo_graycounter1_q_binary = 1'd0;
reg [3:0] frontend_asyncfifo_graycounter1_q_next_binary = 1'd0;
wire [3:0] frontend_asyncfifo_produce_rdomain;
wire [3:0] frontend_asyncfifo_consume_wdomain;
wire [2:0] frontend_asyncfifo_wrport_adr;
wire [3:0] frontend_asyncfifo_wrport_dat_r;
wire frontend_asyncfifo_wrport_we;
wire [3:0] frontend_asyncfifo_wrport_dat_w;
wire [2:0] frontend_asyncfifo_rdport_adr;
wire [3:0] frontend_asyncfifo_rdport_dat_r;
wire [1:0] frontend_asyncfifo_fifo_in_payload_data;
wire frontend_asyncfifo_fifo_in_payload_hit;
wire frontend_asyncfifo_fifo_in_last;
wire [1:0] frontend_asyncfifo_fifo_out_payload_data;
wire frontend_asyncfifo_fifo_out_payload_hit;
wire frontend_asyncfifo_fifo_out_last;
wire storage_sink_sink_valid;
reg storage_sink_sink_ready = 1'd0;
wire storage_sink_sink_last;
wire [1:0] storage_sink_sink_payload_data;
wire storage_sink_sink_payload_hit;
wire storage_start_re;
wire storage_start_r;
reg storage_start_w = 1'd0;
reg [14:0] storage_length_storage_full = 1'd0;
wire [14:0] storage_length_storage;
reg storage_length_re = 1'd0;
reg [14:0] storage_offset_storage_full = 1'd0;
wire [14:0] storage_offset_storage;
reg storage_offset_re = 1'd0;
reg storage_idle_status = 1'd0;
reg storage_wait_status = 1'd0;
reg storage_run_status = 1'd0;
wire storage_mem_valid_status;
wire storage_mem_ready_re;
wire storage_mem_ready_r;
reg storage_mem_ready_w = 1'd0;
wire [1:0] storage_mem_data_status;
reg storage_mem_sink_valid = 1'd0;
wire storage_mem_sink_ready;
reg storage_mem_sink_last = 1'd0;
reg [1:0] storage_mem_sink_payload_data = 1'd0;
wire storage_mem_source_valid;
reg storage_mem_source_ready = 1'd0;
wire storage_mem_source_last;
wire [1:0] storage_mem_source_payload_data;
wire storage_mem_re;
reg storage_mem_readable = 1'd0;
wire storage_mem_syncfifo_we;
wire storage_mem_syncfifo_writable;
wire storage_mem_syncfifo_re;
wire storage_mem_syncfifo_readable;
wire [2:0] storage_mem_syncfifo_din;
wire [2:0] storage_mem_syncfifo_dout;
reg [14:0] storage_mem_level0 = 1'd0;
reg storage_mem_replace = 1'd0;
reg [13:0] storage_mem_produce = 1'd0;
reg [13:0] storage_mem_consume = 1'd0;
reg [13:0] storage_mem_wrport_adr = 1'd0;
wire [2:0] storage_mem_wrport_dat_r;
wire storage_mem_wrport_we;
wire [2:0] storage_mem_wrport_dat_w;
wire storage_mem_do_read;
wire [13:0] storage_mem_rdport_adr;
wire [2:0] storage_mem_rdport_dat_r;
wire storage_mem_rdport_re;
wire [14:0] storage_mem_level1;
wire [1:0] storage_mem_fifo_in_payload_data;
wire storage_mem_fifo_in_last;
wire [1:0] storage_mem_fifo_out_payload_data;
wire storage_mem_fifo_out_last;
reg [2:0] uartwishbonebridge_state = 1'd0;
reg [2:0] uartwishbonebridge_next_state = 1'd0;
reg [1:0] litescopeanalyzer_state = 1'd0;
reg [1:0] litescopeanalyzer_next_state = 1'd0;
wire [29:0] shared_adr;
wire [31:0] shared_dat_w;
wire [31:0] shared_dat_r;
wire [3:0] shared_sel;
wire shared_cyc;
wire shared_stb;
wire shared_ack;
wire shared_we;
wire [2:0] shared_cti;
wire [1:0] shared_bte;
wire shared_err;
wire request;
wire grant;
reg [1:0] slave_sel = 1'd0;
reg [1:0] slave_sel_r = 1'd0;
wire [13:0] interface0_adr;
wire interface0_we;
wire [31:0] interface0_dat_w;
reg [31:0] interface0_dat_r = 1'd0;
wire csrbank0_frontend_trigger_value0_re;
wire [1:0] csrbank0_frontend_trigger_value0_r;
wire [1:0] csrbank0_frontend_trigger_value0_w;
wire csrbank0_frontend_trigger_mask0_re;
wire [1:0] csrbank0_frontend_trigger_mask0_r;
wire [1:0] csrbank0_frontend_trigger_mask0_w;
wire csrbank0_frontend_subsampler_value0_re;
wire [15:0] csrbank0_frontend_subsampler_value0_r;
wire [15:0] csrbank0_frontend_subsampler_value0_w;
wire csrbank0_storage_length0_re;
wire [14:0] csrbank0_storage_length0_r;
wire [14:0] csrbank0_storage_length0_w;
wire csrbank0_storage_offset0_re;
wire [14:0] csrbank0_storage_offset0_r;
wire [14:0] csrbank0_storage_offset0_w;
wire csrbank0_storage_idle_re;
wire csrbank0_storage_idle_r;
wire csrbank0_storage_idle_w;
wire csrbank0_storage_wait_re;
wire csrbank0_storage_wait_r;
wire csrbank0_storage_wait_w;
wire csrbank0_storage_run_re;
wire csrbank0_storage_run_r;
wire csrbank0_storage_run_w;
wire csrbank0_storage_mem_valid_re;
wire csrbank0_storage_mem_valid_r;
wire csrbank0_storage_mem_valid_w;
wire csrbank0_storage_mem_data_re;
wire [1:0] csrbank0_storage_mem_data_r;
wire [1:0] csrbank0_storage_mem_data_w;
wire csrbank0_sel;
wire [13:0] interface1_adr;
wire interface1_we;
wire [31:0] interface1_dat_w;
reg [31:0] interface1_dat_r = 1'd0;
wire [4:0] mmap_adr;
wire [7:0] mmap_dat_r;
wire mmap_sel;
reg mmap_sel_r = 1'd0;
wire [13:0] interface2_adr;
wire interface2_we;
wire [31:0] interface2_dat_w;
reg [31:0] interface2_dat_r = 1'd0;
wire csrbank1_input_re;
wire [8:0] csrbank1_input_r;
wire [8:0] csrbank1_input_w;
wire csrbank1_output0_re;
wire [8:0] csrbank1_output0_r;
wire [8:0] csrbank1_output0_w;
wire csrbank1_sel;
wire sys_clk;
wire sys_rst;
wire por_clk;
reg int_rst = 1'd1;
reg [29:0] array_muxed0 = 1'd0;
reg [31:0] array_muxed1 = 1'd0;
reg [3:0] array_muxed2 = 1'd0;
reg array_muxed3 = 1'd0;
reg array_muxed4 = 1'd0;
reg array_muxed5 = 1'd0;
reg [2:0] array_muxed6 = 1'd0;
reg [1:0] array_muxed7 = 1'd0;
reg xilinxmultiregvivadoimpl0_regs0 = 1'd0;
reg xilinxmultiregvivadoimpl0_regs1 = 1'd0;
reg [1:0] xilinxmultiregvivadoimpl1_regs0 = 1'd0;
reg [1:0] xilinxmultiregvivadoimpl1_regs1 = 1'd0;
reg [1:0] xilinxmultiregvivadoimpl2_regs0 = 1'd0;
reg [1:0] xilinxmultiregvivadoimpl2_regs1 = 1'd0;
reg [15:0] xilinxmultiregvivadoimpl3_regs0 = 1'd0;
reg [15:0] xilinxmultiregvivadoimpl3_regs1 = 1'd0;
reg [3:0] xilinxmultiregvivadoimpl4_regs0 = 1'd0;
reg [3:0] xilinxmultiregvivadoimpl4_regs1 = 1'd0;
reg [3:0] xilinxmultiregvivadoimpl5_regs0 = 1'd0;
reg [3:0] xilinxmultiregvivadoimpl5_regs1 = 1'd0;

// synthesis translate_off
reg dummy_s;
initial dummy_s <= 1'd0;
// synthesis translate_on
assign MOTEA = io_storage[0];
assign DRVSA = io_storage[1];
assign STEP = io_storage[2];
assign DIR = io_storage[3];
assign WDATA = io_storage[4];
assign WGATE = io_storage[5];
assign user_led = (~TRK00);
assign user_led_1 = (~WPT);
assign SIDE1 = io_storage[8];

// synthesis translate_off
reg dummy_d;
// synthesis translate_on
always @(*) begin
	io_status <= 1'd0;
	io_status[0] <= MOTEA;
	io_status[1] <= DRVSA;
	io_status[2] <= STEP;
	io_status[3] <= DIR;
	io_status[4] <= WDATA;
	io_status[5] <= WGATE;
	io_status[6] <= TRK00;
	io_status[7] <= WPT;
	io_status[8] <= SIDE1;
// synthesis translate_off
	dummy_d <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_1;
// synthesis translate_on
always @(*) begin
	ibm360dd_sram_we <= 1'd0;
	ibm360dd_sram_we[0] <= (((ibm360dd_sram_bus_cyc & ibm360dd_sram_bus_stb) & ibm360dd_sram_bus_we) & ibm360dd_sram_bus_sel[0]);
	ibm360dd_sram_we[1] <= (((ibm360dd_sram_bus_cyc & ibm360dd_sram_bus_stb) & ibm360dd_sram_bus_we) & ibm360dd_sram_bus_sel[1]);
	ibm360dd_sram_we[2] <= (((ibm360dd_sram_bus_cyc & ibm360dd_sram_bus_stb) & ibm360dd_sram_bus_we) & ibm360dd_sram_bus_sel[2]);
	ibm360dd_sram_we[3] <= (((ibm360dd_sram_bus_cyc & ibm360dd_sram_bus_stb) & ibm360dd_sram_bus_we) & ibm360dd_sram_bus_sel[3]);
// synthesis translate_off
	dummy_d_1 <= dummy_s;
// synthesis translate_on
end
assign ibm360dd_sram_adr = ibm360dd_sram_bus_adr[9:0];
assign ibm360dd_sram_bus_dat_r = ibm360dd_sram_dat_r;
assign ibm360dd_sram_dat_w = ibm360dd_sram_bus_dat_w;
assign ibm360dd_reset = ibm360dd_done;
assign ibm360dd_source_ready = 1'd1;
assign ibm360dd_wishbone_adr = (ibm360dd_address + ibm360dd_word_counter);
assign ibm360dd_wishbone_dat_w = ibm360dd_data;
assign ibm360dd_wishbone_sel = 4'd15;

// synthesis translate_off
reg dummy_d_2;
// synthesis translate_on
always @(*) begin
	ibm360dd_sink_payload_data <= 1'd0;
	case (ibm360dd_byte_counter)
		1'd0: begin
			ibm360dd_sink_payload_data <= ibm360dd_data[31:24];
		end
		1'd1: begin
			ibm360dd_sink_payload_data <= ibm360dd_data[23:16];
		end
		2'd2: begin
			ibm360dd_sink_payload_data <= ibm360dd_data[15:8];
		end
		default: begin
			ibm360dd_sink_payload_data <= ibm360dd_data[7:0];
		end
	endcase
// synthesis translate_off
	dummy_d_2 <= dummy_s;
// synthesis translate_on
end
assign ibm360dd_wait = (~ibm360dd_is_ongoing);
assign ibm360dd_sink_last = ((ibm360dd_byte_counter == 2'd3) & (ibm360dd_word_counter == (ibm360dd_length - 1'd1)));

// synthesis translate_off
reg dummy_d_3;
// synthesis translate_on
always @(*) begin
	ibm360dd_length_ce <= 1'd0;
	ibm360dd_wishbone_we <= 1'd0;
	ibm360dd_address_ce <= 1'd0;
	ibm360dd_rx_data_ce <= 1'd0;
	ibm360dd_byte_counter_reset <= 1'd0;
	ibm360dd_tx_data_ce <= 1'd0;
	ibm360dd_byte_counter_ce <= 1'd0;
	ibm360dd_word_counter_reset <= 1'd0;
	ibm360dd_is_ongoing <= 1'd0;
	ibm360dd_word_counter_ce <= 1'd0;
	uartwishbonebridge_next_state <= 1'd0;
	ibm360dd_sink_valid <= 1'd0;
	ibm360dd_wishbone_cyc <= 1'd0;
	ibm360dd_wishbone_stb <= 1'd0;
	ibm360dd_cmd_ce <= 1'd0;
	uartwishbonebridge_next_state <= uartwishbonebridge_state;
	case (uartwishbonebridge_state)
		1'd1: begin
			if (ibm360dd_source_valid) begin
				ibm360dd_length_ce <= 1'd1;
				uartwishbonebridge_next_state <= 2'd2;
			end
		end
		2'd2: begin
			if (ibm360dd_source_valid) begin
				ibm360dd_address_ce <= 1'd1;
				ibm360dd_byte_counter_ce <= 1'd1;
				if ((ibm360dd_byte_counter == 2'd3)) begin
					if ((ibm360dd_cmd == 1'd1)) begin
						uartwishbonebridge_next_state <= 2'd3;
					end else begin
						if ((ibm360dd_cmd == 2'd2)) begin
							uartwishbonebridge_next_state <= 3'd5;
						end
					end
					ibm360dd_byte_counter_reset <= 1'd1;
				end
			end
		end
		2'd3: begin
			if (ibm360dd_source_valid) begin
				ibm360dd_rx_data_ce <= 1'd1;
				ibm360dd_byte_counter_ce <= 1'd1;
				if ((ibm360dd_byte_counter == 2'd3)) begin
					uartwishbonebridge_next_state <= 3'd4;
					ibm360dd_byte_counter_reset <= 1'd1;
				end
			end
		end
		3'd4: begin
			ibm360dd_wishbone_stb <= 1'd1;
			ibm360dd_wishbone_we <= 1'd1;
			ibm360dd_wishbone_cyc <= 1'd1;
			if (ibm360dd_wishbone_ack) begin
				ibm360dd_word_counter_ce <= 1'd1;
				if ((ibm360dd_word_counter == (ibm360dd_length - 1'd1))) begin
					uartwishbonebridge_next_state <= 1'd0;
				end else begin
					uartwishbonebridge_next_state <= 2'd3;
				end
			end
		end
		3'd5: begin
			ibm360dd_wishbone_stb <= 1'd1;
			ibm360dd_wishbone_we <= 1'd0;
			ibm360dd_wishbone_cyc <= 1'd1;
			if (ibm360dd_wishbone_ack) begin
				ibm360dd_tx_data_ce <= 1'd1;
				uartwishbonebridge_next_state <= 3'd6;
			end
		end
		3'd6: begin
			ibm360dd_sink_valid <= 1'd1;
			if (ibm360dd_sink_ready) begin
				ibm360dd_byte_counter_ce <= 1'd1;
				if ((ibm360dd_byte_counter == 2'd3)) begin
					ibm360dd_word_counter_ce <= 1'd1;
					if ((ibm360dd_word_counter == (ibm360dd_length - 1'd1))) begin
						uartwishbonebridge_next_state <= 1'd0;
					end else begin
						uartwishbonebridge_next_state <= 3'd5;
						ibm360dd_byte_counter_reset <= 1'd1;
					end
				end
			end
		end
		default: begin
			if (ibm360dd_source_valid) begin
				ibm360dd_cmd_ce <= 1'd1;
				if (((ibm360dd_source_payload_data == 1'd1) | (ibm360dd_source_payload_data == 2'd2))) begin
					uartwishbonebridge_next_state <= 1'd1;
				end
				ibm360dd_byte_counter_reset <= 1'd1;
				ibm360dd_word_counter_reset <= 1'd1;
			end
			ibm360dd_is_ongoing <= 1'd1;
		end
	endcase
// synthesis translate_off
	dummy_d_3 <= dummy_s;
// synthesis translate_on
end
assign ibm360dd_done = (ibm360dd_count == 1'd0);
assign frontend_sink_sink_valid = 1'd1;
assign frontend_sink_sink_payload_data = {RDATA, INDEX};
assign storage_sink_sink_valid = frontend_source_source_valid;
assign frontend_source_source_ready = storage_sink_sink_ready;
assign storage_sink_sink_last = frontend_source_source_last;
assign storage_sink_sink_payload_data = frontend_source_source_payload_data;
assign storage_sink_sink_payload_hit = frontend_source_source_payload_hit;
assign frontend_buffer_pipe_ce = (frontend_buffer_source_ready | (~frontend_buffer_valid_n));
assign frontend_buffer_sink_ready = frontend_buffer_pipe_ce;
assign frontend_buffer_source_valid = frontend_buffer_valid_n;
assign frontend_buffer_source_last = frontend_buffer_last_n;
assign frontend_trigger_source_valid = frontend_trigger_sink_valid;
assign frontend_trigger_sink_ready = frontend_trigger_source_ready;
assign frontend_trigger_source_last = frontend_trigger_sink_last;
assign frontend_trigger_source_payload_data = frontend_trigger_sink_payload_data;

// synthesis translate_off
reg dummy_d_4;
// synthesis translate_on
always @(*) begin
	frontend_trigger_source_payload_hit <= 1'd0;
	frontend_trigger_source_payload_hit <= frontend_trigger_sink_payload_hit;
	frontend_trigger_source_payload_hit <= ((frontend_trigger_sink_payload_data & frontend_trigger_mask) == frontend_trigger_value);
// synthesis translate_off
	dummy_d_4 <= dummy_s;
// synthesis translate_on
end
assign frontend_subsampler_done = (frontend_subsampler_counter == frontend_subsampler_value);
assign frontend_subsampler_sink_ready = frontend_subsampler_source_ready;
assign frontend_subsampler_source_last = frontend_subsampler_sink_last;
assign frontend_subsampler_source_payload_data = frontend_subsampler_sink_payload_data;
assign frontend_subsampler_source_payload_hit = frontend_subsampler_sink_payload_hit;
assign frontend_subsampler_source_valid = (frontend_subsampler_sink_valid & frontend_subsampler_done);
assign frontend_strideconverter_converter_sink_valid = frontend_strideconverter_sink_valid;
assign frontend_strideconverter_converter_sink_last = frontend_strideconverter_sink_last;
assign frontend_strideconverter_sink_ready = frontend_strideconverter_converter_sink_ready;
assign frontend_strideconverter_converter_sink_payload_data = {frontend_strideconverter_sink_payload_hit, frontend_strideconverter_sink_payload_data};
assign frontend_strideconverter_source_valid = frontend_strideconverter_source_source_valid;
assign frontend_strideconverter_source_last = frontend_strideconverter_source_source_last;
assign frontend_strideconverter_source_source_ready = frontend_strideconverter_source_ready;
assign {frontend_strideconverter_source_payload_hit, frontend_strideconverter_source_payload_data} = frontend_strideconverter_source_source_payload_data;
assign frontend_strideconverter_source_source_valid = frontend_strideconverter_converter_source_valid;
assign frontend_strideconverter_converter_source_ready = frontend_strideconverter_source_source_ready;
assign frontend_strideconverter_source_source_last = frontend_strideconverter_converter_source_last;
assign frontend_strideconverter_source_source_payload_data = frontend_strideconverter_converter_source_payload_data;
assign frontend_strideconverter_converter_source_valid = frontend_strideconverter_converter_sink_valid;
assign frontend_strideconverter_converter_sink_ready = frontend_strideconverter_converter_source_ready;
assign frontend_strideconverter_converter_source_last = frontend_strideconverter_converter_sink_last;
assign frontend_strideconverter_converter_source_payload_data = frontend_strideconverter_converter_sink_payload_data;
assign frontend_strideconverter_converter_source_payload_valid_token_count = 1'd1;
assign frontend_asyncfifo_asyncfifo_din = {frontend_asyncfifo_fifo_in_last, frontend_asyncfifo_fifo_in_payload_hit, frontend_asyncfifo_fifo_in_payload_data};
assign {frontend_asyncfifo_fifo_out_last, frontend_asyncfifo_fifo_out_payload_hit, frontend_asyncfifo_fifo_out_payload_data} = frontend_asyncfifo_asyncfifo_dout;
assign frontend_asyncfifo_sink_ready = frontend_asyncfifo_asyncfifo_writable;
assign frontend_asyncfifo_asyncfifo_we = frontend_asyncfifo_sink_valid;
assign frontend_asyncfifo_fifo_in_last = frontend_asyncfifo_sink_last;
assign frontend_asyncfifo_fifo_in_payload_data = frontend_asyncfifo_sink_payload_data;
assign frontend_asyncfifo_fifo_in_payload_hit = frontend_asyncfifo_sink_payload_hit;
assign frontend_asyncfifo_source_valid = frontend_asyncfifo_asyncfifo_readable;
assign frontend_asyncfifo_source_last = frontend_asyncfifo_fifo_out_last;
assign frontend_asyncfifo_source_payload_data = frontend_asyncfifo_fifo_out_payload_data;
assign frontend_asyncfifo_source_payload_hit = frontend_asyncfifo_fifo_out_payload_hit;
assign frontend_asyncfifo_asyncfifo_re = frontend_asyncfifo_source_ready;
assign frontend_asyncfifo_graycounter0_ce = (frontend_asyncfifo_asyncfifo_writable & frontend_asyncfifo_asyncfifo_we);
assign frontend_asyncfifo_graycounter1_ce = (frontend_asyncfifo_asyncfifo_readable & frontend_asyncfifo_asyncfifo_re);
assign frontend_asyncfifo_asyncfifo_writable = (((frontend_asyncfifo_graycounter0_q[3] == frontend_asyncfifo_consume_wdomain[3]) | (frontend_asyncfifo_graycounter0_q[2] == frontend_asyncfifo_consume_wdomain[2])) | (frontend_asyncfifo_graycounter0_q[1:0] != frontend_asyncfifo_consume_wdomain[1:0]));
assign frontend_asyncfifo_asyncfifo_readable = (frontend_asyncfifo_graycounter1_q != frontend_asyncfifo_produce_rdomain);
assign frontend_asyncfifo_wrport_adr = frontend_asyncfifo_graycounter0_q_binary[2:0];
assign frontend_asyncfifo_wrport_dat_w = frontend_asyncfifo_asyncfifo_din;
assign frontend_asyncfifo_wrport_we = frontend_asyncfifo_graycounter0_ce;
assign frontend_asyncfifo_rdport_adr = frontend_asyncfifo_graycounter1_q_next_binary[2:0];
assign frontend_asyncfifo_asyncfifo_dout = frontend_asyncfifo_rdport_dat_r;

// synthesis translate_off
reg dummy_d_5;
// synthesis translate_on
always @(*) begin
	frontend_asyncfifo_graycounter0_q_next_binary <= 1'd0;
	if (frontend_asyncfifo_graycounter0_ce) begin
		frontend_asyncfifo_graycounter0_q_next_binary <= (frontend_asyncfifo_graycounter0_q_binary + 1'd1);
	end else begin
		frontend_asyncfifo_graycounter0_q_next_binary <= frontend_asyncfifo_graycounter0_q_binary;
	end
// synthesis translate_off
	dummy_d_5 <= dummy_s;
// synthesis translate_on
end
assign frontend_asyncfifo_graycounter0_q_next = (frontend_asyncfifo_graycounter0_q_next_binary ^ frontend_asyncfifo_graycounter0_q_next_binary[3:1]);

// synthesis translate_off
reg dummy_d_6;
// synthesis translate_on
always @(*) begin
	frontend_asyncfifo_graycounter1_q_next_binary <= 1'd0;
	if (frontend_asyncfifo_graycounter1_ce) begin
		frontend_asyncfifo_graycounter1_q_next_binary <= (frontend_asyncfifo_graycounter1_q_binary + 1'd1);
	end else begin
		frontend_asyncfifo_graycounter1_q_next_binary <= frontend_asyncfifo_graycounter1_q_binary;
	end
// synthesis translate_off
	dummy_d_6 <= dummy_s;
// synthesis translate_on
end
assign frontend_asyncfifo_graycounter1_q_next = (frontend_asyncfifo_graycounter1_q_next_binary ^ frontend_asyncfifo_graycounter1_q_next_binary[3:1]);
assign frontend_buffer_sink_valid = frontend_sink_sink_valid;
assign frontend_sink_sink_ready = frontend_buffer_sink_ready;
assign frontend_buffer_sink_last = frontend_sink_sink_last;
assign frontend_buffer_sink_payload_data = frontend_sink_sink_payload_data;
assign frontend_buffer_sink_payload_hit = frontend_sink_sink_payload_hit;
assign frontend_trigger_sink_valid = frontend_buffer_source_valid;
assign frontend_buffer_source_ready = frontend_trigger_sink_ready;
assign frontend_trigger_sink_last = frontend_buffer_source_last;
assign frontend_trigger_sink_payload_data = frontend_buffer_source_payload_data;
assign frontend_trigger_sink_payload_hit = frontend_buffer_source_payload_hit;
assign frontend_subsampler_sink_valid = frontend_trigger_source_valid;
assign frontend_trigger_source_ready = frontend_subsampler_sink_ready;
assign frontend_subsampler_sink_last = frontend_trigger_source_last;
assign frontend_subsampler_sink_payload_data = frontend_trigger_source_payload_data;
assign frontend_subsampler_sink_payload_hit = frontend_trigger_source_payload_hit;
assign frontend_strideconverter_sink_valid = frontend_subsampler_source_valid;
assign frontend_subsampler_source_ready = frontend_strideconverter_sink_ready;
assign frontend_strideconverter_sink_last = frontend_subsampler_source_last;
assign frontend_strideconverter_sink_payload_data = frontend_subsampler_source_payload_data;
assign frontend_strideconverter_sink_payload_hit = frontend_subsampler_source_payload_hit;
assign frontend_asyncfifo_sink_valid = frontend_strideconverter_source_valid;
assign frontend_strideconverter_source_ready = frontend_asyncfifo_sink_ready;
assign frontend_asyncfifo_sink_last = frontend_strideconverter_source_last;
assign frontend_asyncfifo_sink_payload_data = frontend_strideconverter_source_payload_data;
assign frontend_asyncfifo_sink_payload_hit = frontend_strideconverter_source_payload_hit;
assign frontend_source_source_valid = frontend_asyncfifo_source_valid;
assign frontend_asyncfifo_source_ready = frontend_source_source_ready;
assign frontend_source_source_last = frontend_asyncfifo_source_last;
assign frontend_source_source_payload_data = frontend_asyncfifo_source_payload_data;
assign frontend_source_source_payload_hit = frontend_asyncfifo_source_payload_hit;
assign storage_mem_valid_status = storage_mem_source_valid;
assign storage_mem_data_status = storage_mem_source_payload_data;
assign storage_mem_syncfifo_din = {storage_mem_fifo_in_last, storage_mem_fifo_in_payload_data};
assign {storage_mem_fifo_out_last, storage_mem_fifo_out_payload_data} = storage_mem_syncfifo_dout;
assign storage_mem_sink_ready = storage_mem_syncfifo_writable;
assign storage_mem_syncfifo_we = storage_mem_sink_valid;
assign storage_mem_fifo_in_last = storage_mem_sink_last;
assign storage_mem_fifo_in_payload_data = storage_mem_sink_payload_data;
assign storage_mem_source_valid = storage_mem_readable;
assign storage_mem_source_last = storage_mem_fifo_out_last;
assign storage_mem_source_payload_data = storage_mem_fifo_out_payload_data;
assign storage_mem_re = storage_mem_source_ready;
assign storage_mem_syncfifo_re = (storage_mem_syncfifo_readable & ((~storage_mem_readable) | storage_mem_re));
assign storage_mem_level1 = (storage_mem_level0 + storage_mem_readable);

// synthesis translate_off
reg dummy_d_7;
// synthesis translate_on
always @(*) begin
	storage_mem_wrport_adr <= 1'd0;
	if (storage_mem_replace) begin
		storage_mem_wrport_adr <= (storage_mem_produce - 1'd1);
	end else begin
		storage_mem_wrport_adr <= storage_mem_produce;
	end
// synthesis translate_off
	dummy_d_7 <= dummy_s;
// synthesis translate_on
end
assign storage_mem_wrport_dat_w = storage_mem_syncfifo_din;
assign storage_mem_wrport_we = (storage_mem_syncfifo_we & (storage_mem_syncfifo_writable | storage_mem_replace));
assign storage_mem_do_read = (storage_mem_syncfifo_readable & storage_mem_syncfifo_re);
assign storage_mem_rdport_adr = storage_mem_consume;
assign storage_mem_syncfifo_dout = storage_mem_rdport_dat_r;
assign storage_mem_rdport_re = storage_mem_do_read;
assign storage_mem_syncfifo_writable = (storage_mem_level0 != 15'd16384);
assign storage_mem_syncfifo_readable = (storage_mem_level0 != 1'd0);

// synthesis translate_off
reg dummy_d_8;
// synthesis translate_on
always @(*) begin
	storage_mem_source_ready <= 1'd0;
	storage_sink_sink_ready <= 1'd0;
	storage_idle_status <= 1'd0;
	storage_mem_sink_last <= 1'd0;
	storage_wait_status <= 1'd0;
	storage_run_status <= 1'd0;
	storage_mem_sink_valid <= 1'd0;
	litescopeanalyzer_next_state <= 1'd0;
	storage_mem_sink_payload_data <= 1'd0;
	litescopeanalyzer_next_state <= litescopeanalyzer_state;
	case (litescopeanalyzer_state)
		1'd1: begin
			storage_wait_status <= 1'd1;
			storage_mem_sink_valid <= storage_sink_sink_valid;
			storage_sink_sink_ready <= storage_mem_sink_ready;
			storage_mem_sink_last <= storage_sink_sink_last;
			storage_mem_sink_payload_data <= storage_sink_sink_payload_data;
			if ((storage_sink_sink_valid & (storage_sink_sink_payload_hit != 1'd0))) begin
				litescopeanalyzer_next_state <= 2'd2;
			end
			storage_mem_source_ready <= (storage_mem_level1 >= storage_offset_storage);
		end
		2'd2: begin
			storage_run_status <= 1'd1;
			storage_mem_sink_valid <= storage_sink_sink_valid;
			storage_sink_sink_ready <= storage_mem_sink_ready;
			storage_mem_sink_last <= storage_sink_sink_last;
			storage_mem_sink_payload_data <= storage_sink_sink_payload_data;
			if (((~storage_mem_sink_ready) | (storage_mem_level1 >= storage_length_storage))) begin
				litescopeanalyzer_next_state <= 1'd0;
				storage_mem_source_ready <= 1'd1;
			end
		end
		default: begin
			storage_idle_status <= 1'd1;
			if (storage_start_re) begin
				litescopeanalyzer_next_state <= 1'd1;
			end
			storage_sink_sink_ready <= 1'd1;
			storage_mem_source_ready <= (storage_mem_ready_re & storage_mem_ready_r);
		end
	endcase
// synthesis translate_off
	dummy_d_8 <= dummy_s;
// synthesis translate_on
end
assign shared_adr = array_muxed0;
assign shared_dat_w = array_muxed1;
assign shared_sel = array_muxed2;
assign shared_cyc = array_muxed3;
assign shared_stb = array_muxed4;
assign shared_we = array_muxed5;
assign shared_cti = array_muxed6;
assign shared_bte = array_muxed7;
assign ibm360dd_wishbone_dat_r = shared_dat_r;
assign ibm360dd_wishbone_ack = (shared_ack & (grant == 1'd0));
assign ibm360dd_wishbone_err = (shared_err & (grant == 1'd0));
assign request = {ibm360dd_wishbone_cyc};
assign grant = 1'd0;

// synthesis translate_off
reg dummy_d_9;
// synthesis translate_on
always @(*) begin
	slave_sel <= 1'd0;
	slave_sel[0] <= (shared_adr[28:26] == 1'd1);
	slave_sel[1] <= (shared_adr[28:26] == 3'd6);
// synthesis translate_off
	dummy_d_9 <= dummy_s;
// synthesis translate_on
end
assign ibm360dd_sram_bus_adr = shared_adr;
assign ibm360dd_sram_bus_dat_w = shared_dat_w;
assign ibm360dd_sram_bus_sel = shared_sel;
assign ibm360dd_sram_bus_stb = shared_stb;
assign ibm360dd_sram_bus_we = shared_we;
assign ibm360dd_sram_bus_cti = shared_cti;
assign ibm360dd_sram_bus_bte = shared_bte;
assign ibm360dd_bus_wishbone_adr = shared_adr;
assign ibm360dd_bus_wishbone_dat_w = shared_dat_w;
assign ibm360dd_bus_wishbone_sel = shared_sel;
assign ibm360dd_bus_wishbone_stb = shared_stb;
assign ibm360dd_bus_wishbone_we = shared_we;
assign ibm360dd_bus_wishbone_cti = shared_cti;
assign ibm360dd_bus_wishbone_bte = shared_bte;
assign ibm360dd_sram_bus_cyc = (shared_cyc & slave_sel[0]);
assign ibm360dd_bus_wishbone_cyc = (shared_cyc & slave_sel[1]);
assign shared_ack = (ibm360dd_sram_bus_ack | ibm360dd_bus_wishbone_ack);
assign shared_err = (ibm360dd_sram_bus_err | ibm360dd_bus_wishbone_err);
assign shared_dat_r = (({32{slave_sel_r[0]}} & ibm360dd_sram_bus_dat_r) | ({32{slave_sel_r[1]}} & ibm360dd_bus_wishbone_dat_r));
assign csrbank0_sel = (interface0_adr[13:9] == 5'd17);
assign csrbank0_frontend_trigger_value0_r = interface0_dat_w[1:0];
assign csrbank0_frontend_trigger_value0_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 1'd0));
assign csrbank0_frontend_trigger_mask0_r = interface0_dat_w[1:0];
assign csrbank0_frontend_trigger_mask0_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 1'd1));
assign csrbank0_frontend_subsampler_value0_r = interface0_dat_w[15:0];
assign csrbank0_frontend_subsampler_value0_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 2'd2));
assign storage_start_r = interface0_dat_w[0];
assign storage_start_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 2'd3));
assign csrbank0_storage_length0_r = interface0_dat_w[14:0];
assign csrbank0_storage_length0_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 3'd4));
assign csrbank0_storage_offset0_r = interface0_dat_w[14:0];
assign csrbank0_storage_offset0_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 3'd5));
assign csrbank0_storage_idle_r = interface0_dat_w[0];
assign csrbank0_storage_idle_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 3'd6));
assign csrbank0_storage_wait_r = interface0_dat_w[0];
assign csrbank0_storage_wait_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 3'd7));
assign csrbank0_storage_run_r = interface0_dat_w[0];
assign csrbank0_storage_run_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 4'd8));
assign csrbank0_storage_mem_valid_r = interface0_dat_w[0];
assign csrbank0_storage_mem_valid_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 4'd9));
assign storage_mem_ready_r = interface0_dat_w[0];
assign storage_mem_ready_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 4'd10));
assign csrbank0_storage_mem_data_r = interface0_dat_w[1:0];
assign csrbank0_storage_mem_data_re = ((csrbank0_sel & interface0_we) & (interface0_adr[3:0] == 4'd11));
assign frontend_trigger_value_storage = frontend_trigger_value_storage_full[1:0];
assign csrbank0_frontend_trigger_value0_w = frontend_trigger_value_storage_full[1:0];
assign frontend_trigger_mask_storage = frontend_trigger_mask_storage_full[1:0];
assign csrbank0_frontend_trigger_mask0_w = frontend_trigger_mask_storage_full[1:0];
assign frontend_subsampler_value_storage = frontend_subsampler_value_storage_full[15:0];
assign csrbank0_frontend_subsampler_value0_w = frontend_subsampler_value_storage_full[15:0];
assign storage_length_storage = storage_length_storage_full[14:0];
assign csrbank0_storage_length0_w = storage_length_storage_full[14:0];
assign storage_offset_storage = storage_offset_storage_full[14:0];
assign csrbank0_storage_offset0_w = storage_offset_storage_full[14:0];
assign csrbank0_storage_idle_w = storage_idle_status;
assign csrbank0_storage_wait_w = storage_wait_status;
assign csrbank0_storage_run_w = storage_run_status;
assign csrbank0_storage_mem_valid_w = storage_mem_valid_status;
assign csrbank0_storage_mem_data_w = storage_mem_data_status[1:0];
assign mmap_sel = (interface1_adr[13:9] == 2'd3);

// synthesis translate_off
reg dummy_d_10;
// synthesis translate_on
always @(*) begin
	interface1_dat_r <= 1'd0;
	if (mmap_sel_r) begin
		interface1_dat_r <= mmap_dat_r;
	end
// synthesis translate_off
	dummy_d_10 <= dummy_s;
// synthesis translate_on
end
assign mmap_adr = interface1_adr[4:0];
assign csrbank1_sel = (interface2_adr[13:9] == 5'd16);
assign csrbank1_input_r = interface2_dat_w[8:0];
assign csrbank1_input_re = ((csrbank1_sel & interface2_we) & (interface2_adr[0] == 1'd0));
assign csrbank1_output0_r = interface2_dat_w[8:0];
assign csrbank1_output0_re = ((csrbank1_sel & interface2_we) & (interface2_adr[0] == 1'd1));
assign csrbank1_input_w = io_status[8:0];
assign io_storage = io_storage_full[8:0];
assign csrbank1_output0_w = io_storage_full[8:0];
assign interface0_adr = ibm360dd_interface_adr;
assign interface2_adr = ibm360dd_interface_adr;
assign interface1_adr = ibm360dd_interface_adr;
assign interface0_we = ibm360dd_interface_we;
assign interface2_we = ibm360dd_interface_we;
assign interface1_we = ibm360dd_interface_we;
assign interface0_dat_w = ibm360dd_interface_dat_w;
assign interface2_dat_w = ibm360dd_interface_dat_w;
assign interface1_dat_w = ibm360dd_interface_dat_w;
assign ibm360dd_interface_dat_r = ((interface0_dat_r | interface2_dat_r) | interface1_dat_r);
assign sys_clk = clk50;
assign por_clk = clk50;
assign sys_rst = int_rst;

// synthesis translate_off
reg dummy_d_11;
// synthesis translate_on
always @(*) begin
	array_muxed0 <= 1'd0;
	case (grant)
		default: begin
			array_muxed0 <= ibm360dd_wishbone_adr;
		end
	endcase
// synthesis translate_off
	dummy_d_11 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_12;
// synthesis translate_on
always @(*) begin
	array_muxed1 <= 1'd0;
	case (grant)
		default: begin
			array_muxed1 <= ibm360dd_wishbone_dat_w;
		end
	endcase
// synthesis translate_off
	dummy_d_12 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_13;
// synthesis translate_on
always @(*) begin
	array_muxed2 <= 1'd0;
	case (grant)
		default: begin
			array_muxed2 <= ibm360dd_wishbone_sel;
		end
	endcase
// synthesis translate_off
	dummy_d_13 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_14;
// synthesis translate_on
always @(*) begin
	array_muxed3 <= 1'd0;
	case (grant)
		default: begin
			array_muxed3 <= ibm360dd_wishbone_cyc;
		end
	endcase
// synthesis translate_off
	dummy_d_14 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_15;
// synthesis translate_on
always @(*) begin
	array_muxed4 <= 1'd0;
	case (grant)
		default: begin
			array_muxed4 <= ibm360dd_wishbone_stb;
		end
	endcase
// synthesis translate_off
	dummy_d_15 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_16;
// synthesis translate_on
always @(*) begin
	array_muxed5 <= 1'd0;
	case (grant)
		default: begin
			array_muxed5 <= ibm360dd_wishbone_we;
		end
	endcase
// synthesis translate_off
	dummy_d_16 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_17;
// synthesis translate_on
always @(*) begin
	array_muxed6 <= 1'd0;
	case (grant)
		default: begin
			array_muxed6 <= ibm360dd_wishbone_cti;
		end
	endcase
// synthesis translate_off
	dummy_d_17 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_18;
// synthesis translate_on
always @(*) begin
	array_muxed7 <= 1'd0;
	case (grant)
		default: begin
			array_muxed7 <= ibm360dd_wishbone_bte;
		end
	endcase
// synthesis translate_off
	dummy_d_18 <= dummy_s;
// synthesis translate_on
end
assign ibm360dd_rx = xilinxmultiregvivadoimpl0_regs1;
assign frontend_trigger_value = xilinxmultiregvivadoimpl1_regs1;
assign frontend_trigger_mask = xilinxmultiregvivadoimpl2_regs1;
assign frontend_subsampler_value = xilinxmultiregvivadoimpl3_regs1;
assign frontend_asyncfifo_produce_rdomain = xilinxmultiregvivadoimpl4_regs1;
assign frontend_asyncfifo_consume_wdomain = xilinxmultiregvivadoimpl5_regs1;

always @(posedge por_clk) begin
	int_rst <= 1'd0;
end

always @(posedge sys_clk) begin
	if (sys_rst) begin
		ibm360dd_sram_bus_ack <= 1'd0;
		ibm360dd_interface_adr <= 1'd0;
		ibm360dd_interface_we <= 1'd0;
		ibm360dd_interface_dat_w <= 1'd0;
		ibm360dd_bus_wishbone_dat_r <= 1'd0;
		ibm360dd_bus_wishbone_ack <= 1'd0;
		ibm360dd_counter <= 1'd0;
		serial_tx <= 1'd1;
		ibm360dd_sink_ready <= 1'd0;
		ibm360dd_uart_clk_txen <= 1'd0;
		ibm360dd_phase_accumulator_tx <= 1'd0;
		ibm360dd_tx_reg <= 1'd0;
		ibm360dd_tx_bitcount <= 1'd0;
		ibm360dd_tx_busy <= 1'd0;
		ibm360dd_source_valid <= 1'd0;
		ibm360dd_source_payload_data <= 1'd0;
		ibm360dd_uart_clk_rxen <= 1'd0;
		ibm360dd_phase_accumulator_rx <= 1'd0;
		ibm360dd_rx_r <= 1'd0;
		ibm360dd_rx_reg <= 1'd0;
		ibm360dd_rx_bitcount <= 1'd0;
		ibm360dd_rx_busy <= 1'd0;
		ibm360dd_byte_counter <= 1'd0;
		ibm360dd_word_counter <= 1'd0;
		ibm360dd_cmd <= 1'd0;
		ibm360dd_length <= 1'd0;
		ibm360dd_address <= 1'd0;
		ibm360dd_data <= 1'd0;
		ibm360dd_count <= 23'd5000000;
		io_storage_full <= 9'd511;
		io_re <= 1'd0;
		user_led_2 <= 1'd0;
		sigs_counter <= 1'd0;
		sigs_index_edge <= 1'd0;
		sigs_latched_index <= 1'd0;
		sigs_dat_counter <= 1'd0;
		user_led_3 <= 1'd0;
		sigs_data_edge <= 1'd0;
		sigs_latched_data <= 1'd0;
		frontend_buffer_source_payload_data <= 1'd0;
		frontend_buffer_source_payload_hit <= 1'd0;
		frontend_buffer_valid_n <= 1'd0;
		frontend_buffer_last_n <= 1'd0;
		frontend_trigger_value_storage_full <= 1'd0;
		frontend_trigger_value_re <= 1'd0;
		frontend_trigger_mask_storage_full <= 1'd0;
		frontend_trigger_mask_re <= 1'd0;
		frontend_subsampler_value_storage_full <= 1'd0;
		frontend_subsampler_value_re <= 1'd0;
		frontend_subsampler_counter <= 1'd0;
		frontend_asyncfifo_graycounter0_q <= 1'd0;
		frontend_asyncfifo_graycounter0_q_binary <= 1'd0;
		frontend_asyncfifo_graycounter1_q <= 1'd0;
		frontend_asyncfifo_graycounter1_q_binary <= 1'd0;
		storage_length_storage_full <= 1'd0;
		storage_length_re <= 1'd0;
		storage_offset_storage_full <= 1'd0;
		storage_offset_re <= 1'd0;
		storage_mem_readable <= 1'd0;
		storage_mem_level0 <= 1'd0;
		storage_mem_produce <= 1'd0;
		storage_mem_consume <= 1'd0;
		uartwishbonebridge_state <= 1'd0;
		litescopeanalyzer_state <= 1'd0;
		slave_sel_r <= 1'd0;
		interface0_dat_r <= 1'd0;
		mmap_sel_r <= 1'd0;
		interface2_dat_r <= 1'd0;
	end else begin
		sigs_latched_index <= INDEX;
		sigs_index_edge <= (sigs_latched_index & (~INDEX));
		if (sigs_index_edge) begin
			sigs_index_edge <= 1'd0;
			sigs_counter <= (sigs_counter + 1'd1);
		end
		if ((sigs_counter >= 3'd5)) begin
			sigs_counter <= 1'd0;
			user_led_2 <= (~user_led_2);
		end
		sigs_latched_data <= RDATA;
		sigs_data_edge <= (sigs_latched_data ^ RDATA);
		if (sigs_data_edge) begin
			sigs_data_edge <= 1'd0;
			sigs_dat_counter <= (sigs_dat_counter + 1'd1);
		end
		if ((sigs_dat_counter >= 19'd500000)) begin
			sigs_dat_counter <= 1'd0;
			user_led_3 <= (~user_led_3);
		end
		ibm360dd_sram_bus_ack <= 1'd0;
		if (((ibm360dd_sram_bus_cyc & ibm360dd_sram_bus_stb) & (~ibm360dd_sram_bus_ack))) begin
			ibm360dd_sram_bus_ack <= 1'd1;
		end
		ibm360dd_interface_we <= 1'd0;
		ibm360dd_interface_dat_w <= ibm360dd_bus_wishbone_dat_w;
		ibm360dd_interface_adr <= ibm360dd_bus_wishbone_adr;
		ibm360dd_bus_wishbone_dat_r <= ibm360dd_interface_dat_r;
		if ((ibm360dd_counter == 1'd1)) begin
			ibm360dd_interface_we <= ibm360dd_bus_wishbone_we;
		end
		if ((ibm360dd_counter == 2'd2)) begin
			ibm360dd_bus_wishbone_ack <= 1'd1;
		end
		if ((ibm360dd_counter == 2'd3)) begin
			ibm360dd_bus_wishbone_ack <= 1'd0;
		end
		if ((ibm360dd_counter != 1'd0)) begin
			ibm360dd_counter <= (ibm360dd_counter + 1'd1);
		end else begin
			if ((ibm360dd_bus_wishbone_cyc & ibm360dd_bus_wishbone_stb)) begin
				ibm360dd_counter <= 1'd1;
			end
		end
		if (ibm360dd_byte_counter_reset) begin
			ibm360dd_byte_counter <= 1'd0;
		end else begin
			if (ibm360dd_byte_counter_ce) begin
				ibm360dd_byte_counter <= (ibm360dd_byte_counter + 1'd1);
			end
		end
		if (ibm360dd_word_counter_reset) begin
			ibm360dd_word_counter <= 1'd0;
		end else begin
			if (ibm360dd_word_counter_ce) begin
				ibm360dd_word_counter <= (ibm360dd_word_counter + 1'd1);
			end
		end
		if (ibm360dd_cmd_ce) begin
			ibm360dd_cmd <= ibm360dd_source_payload_data;
		end
		if (ibm360dd_length_ce) begin
			ibm360dd_length <= ibm360dd_source_payload_data;
		end
		if (ibm360dd_address_ce) begin
			ibm360dd_address <= {ibm360dd_address[23:0], ibm360dd_source_payload_data};
		end
		if (ibm360dd_rx_data_ce) begin
			ibm360dd_data <= {ibm360dd_data[23:0], ibm360dd_source_payload_data};
		end else begin
			if (ibm360dd_tx_data_ce) begin
				ibm360dd_data <= ibm360dd_wishbone_dat_r;
			end
		end
		ibm360dd_sink_ready <= 1'd0;
		if (((ibm360dd_sink_valid & (~ibm360dd_tx_busy)) & (~ibm360dd_sink_ready))) begin
			ibm360dd_tx_reg <= ibm360dd_sink_payload_data;
			ibm360dd_tx_bitcount <= 1'd0;
			ibm360dd_tx_busy <= 1'd1;
			serial_tx <= 1'd0;
		end else begin
			if ((ibm360dd_uart_clk_txen & ibm360dd_tx_busy)) begin
				ibm360dd_tx_bitcount <= (ibm360dd_tx_bitcount + 1'd1);
				if ((ibm360dd_tx_bitcount == 4'd8)) begin
					serial_tx <= 1'd1;
				end else begin
					if ((ibm360dd_tx_bitcount == 4'd9)) begin
						serial_tx <= 1'd1;
						ibm360dd_tx_busy <= 1'd0;
						ibm360dd_sink_ready <= 1'd1;
					end else begin
						serial_tx <= ibm360dd_tx_reg[0];
						ibm360dd_tx_reg <= {1'd0, ibm360dd_tx_reg[7:1]};
					end
				end
			end
		end
		if (ibm360dd_tx_busy) begin
			{ibm360dd_uart_clk_txen, ibm360dd_phase_accumulator_tx} <= (ibm360dd_phase_accumulator_tx + ibm360dd_storage);
		end else begin
			{ibm360dd_uart_clk_txen, ibm360dd_phase_accumulator_tx} <= 1'd0;
		end
		ibm360dd_source_valid <= 1'd0;
		ibm360dd_rx_r <= ibm360dd_rx;
		if ((~ibm360dd_rx_busy)) begin
			if (((~ibm360dd_rx) & ibm360dd_rx_r)) begin
				ibm360dd_rx_busy <= 1'd1;
				ibm360dd_rx_bitcount <= 1'd0;
			end
		end else begin
			if (ibm360dd_uart_clk_rxen) begin
				ibm360dd_rx_bitcount <= (ibm360dd_rx_bitcount + 1'd1);
				if ((ibm360dd_rx_bitcount == 1'd0)) begin
					if (ibm360dd_rx) begin
						ibm360dd_rx_busy <= 1'd0;
					end
				end else begin
					if ((ibm360dd_rx_bitcount == 4'd9)) begin
						ibm360dd_rx_busy <= 1'd0;
						if (ibm360dd_rx) begin
							ibm360dd_source_payload_data <= ibm360dd_rx_reg;
							ibm360dd_source_valid <= 1'd1;
						end
					end else begin
						ibm360dd_rx_reg <= {ibm360dd_rx, ibm360dd_rx_reg[7:1]};
					end
				end
			end
		end
		if (ibm360dd_rx_busy) begin
			{ibm360dd_uart_clk_rxen, ibm360dd_phase_accumulator_rx} <= (ibm360dd_phase_accumulator_rx + ibm360dd_storage);
		end else begin
			{ibm360dd_uart_clk_rxen, ibm360dd_phase_accumulator_rx} <= 32'd2147483648;
		end
		if (ibm360dd_reset) begin
			uartwishbonebridge_state <= 1'd0;
		end else begin
			uartwishbonebridge_state <= uartwishbonebridge_next_state;
		end
		if (ibm360dd_wait) begin
			if ((~ibm360dd_done)) begin
				ibm360dd_count <= (ibm360dd_count - 1'd1);
			end
		end else begin
			ibm360dd_count <= 23'd5000000;
		end
		if (frontend_buffer_pipe_ce) begin
			frontend_buffer_valid_n <= frontend_buffer_sink_valid;
		end
		if (frontend_buffer_pipe_ce) begin
			frontend_buffer_last_n <= (frontend_buffer_sink_valid & frontend_buffer_sink_last);
		end
		if (frontend_buffer_pipe_ce) begin
			frontend_buffer_source_payload_data <= frontend_buffer_sink_payload_data;
			frontend_buffer_source_payload_hit <= frontend_buffer_sink_payload_hit;
		end
		if (frontend_subsampler_source_ready) begin
			if (frontend_subsampler_done) begin
				frontend_subsampler_counter <= 1'd0;
			end else begin
				if (frontend_subsampler_sink_valid) begin
					frontend_subsampler_counter <= (frontend_subsampler_counter + 1'd1);
				end
			end
		end
		frontend_asyncfifo_graycounter0_q_binary <= frontend_asyncfifo_graycounter0_q_next_binary;
		frontend_asyncfifo_graycounter0_q <= frontend_asyncfifo_graycounter0_q_next;
		frontend_asyncfifo_graycounter1_q_binary <= frontend_asyncfifo_graycounter1_q_next_binary;
		frontend_asyncfifo_graycounter1_q <= frontend_asyncfifo_graycounter1_q_next;
		if (storage_mem_syncfifo_re) begin
			storage_mem_readable <= 1'd1;
		end else begin
			if (storage_mem_re) begin
				storage_mem_readable <= 1'd0;
			end
		end
		if (((storage_mem_syncfifo_we & storage_mem_syncfifo_writable) & (~storage_mem_replace))) begin
			storage_mem_produce <= (storage_mem_produce + 1'd1);
		end
		if (storage_mem_do_read) begin
			storage_mem_consume <= (storage_mem_consume + 1'd1);
		end
		if (((storage_mem_syncfifo_we & storage_mem_syncfifo_writable) & (~storage_mem_replace))) begin
			if ((~storage_mem_do_read)) begin
				storage_mem_level0 <= (storage_mem_level0 + 1'd1);
			end
		end else begin
			if (storage_mem_do_read) begin
				storage_mem_level0 <= (storage_mem_level0 - 1'd1);
			end
		end
		litescopeanalyzer_state <= litescopeanalyzer_next_state;
		slave_sel_r <= slave_sel;
		interface0_dat_r <= 1'd0;
		if (csrbank0_sel) begin
			case (interface0_adr[3:0])
				1'd0: begin
					interface0_dat_r <= csrbank0_frontend_trigger_value0_w;
				end
				1'd1: begin
					interface0_dat_r <= csrbank0_frontend_trigger_mask0_w;
				end
				2'd2: begin
					interface0_dat_r <= csrbank0_frontend_subsampler_value0_w;
				end
				2'd3: begin
					interface0_dat_r <= storage_start_w;
				end
				3'd4: begin
					interface0_dat_r <= csrbank0_storage_length0_w;
				end
				3'd5: begin
					interface0_dat_r <= csrbank0_storage_offset0_w;
				end
				3'd6: begin
					interface0_dat_r <= csrbank0_storage_idle_w;
				end
				3'd7: begin
					interface0_dat_r <= csrbank0_storage_wait_w;
				end
				4'd8: begin
					interface0_dat_r <= csrbank0_storage_run_w;
				end
				4'd9: begin
					interface0_dat_r <= csrbank0_storage_mem_valid_w;
				end
				4'd10: begin
					interface0_dat_r <= storage_mem_ready_w;
				end
				4'd11: begin
					interface0_dat_r <= csrbank0_storage_mem_data_w;
				end
			endcase
		end
		if (csrbank0_frontend_trigger_value0_re) begin
			frontend_trigger_value_storage_full[1:0] <= csrbank0_frontend_trigger_value0_r;
		end
		frontend_trigger_value_re <= csrbank0_frontend_trigger_value0_re;
		if (csrbank0_frontend_trigger_mask0_re) begin
			frontend_trigger_mask_storage_full[1:0] <= csrbank0_frontend_trigger_mask0_r;
		end
		frontend_trigger_mask_re <= csrbank0_frontend_trigger_mask0_re;
		if (csrbank0_frontend_subsampler_value0_re) begin
			frontend_subsampler_value_storage_full[15:0] <= csrbank0_frontend_subsampler_value0_r;
		end
		frontend_subsampler_value_re <= csrbank0_frontend_subsampler_value0_re;
		if (csrbank0_storage_length0_re) begin
			storage_length_storage_full[14:0] <= csrbank0_storage_length0_r;
		end
		storage_length_re <= csrbank0_storage_length0_re;
		if (csrbank0_storage_offset0_re) begin
			storage_offset_storage_full[14:0] <= csrbank0_storage_offset0_r;
		end
		storage_offset_re <= csrbank0_storage_offset0_re;
		mmap_sel_r <= mmap_sel;
		interface2_dat_r <= 1'd0;
		if (csrbank1_sel) begin
			case (interface2_adr[0])
				1'd0: begin
					interface2_dat_r <= csrbank1_input_w;
				end
				1'd1: begin
					interface2_dat_r <= csrbank1_output0_w;
				end
			endcase
		end
		if (csrbank1_output0_re) begin
			io_storage_full[8:0] <= csrbank1_output0_r;
		end
		io_re <= csrbank1_output0_re;
	end
	xilinxmultiregvivadoimpl0_regs0 <= serial_rx;
	xilinxmultiregvivadoimpl0_regs1 <= xilinxmultiregvivadoimpl0_regs0;
	xilinxmultiregvivadoimpl1_regs0 <= frontend_trigger_value_storage;
	xilinxmultiregvivadoimpl1_regs1 <= xilinxmultiregvivadoimpl1_regs0;
	xilinxmultiregvivadoimpl2_regs0 <= frontend_trigger_mask_storage;
	xilinxmultiregvivadoimpl2_regs1 <= xilinxmultiregvivadoimpl2_regs0;
	xilinxmultiregvivadoimpl3_regs0 <= frontend_subsampler_value_storage;
	xilinxmultiregvivadoimpl3_regs1 <= xilinxmultiregvivadoimpl3_regs0;
	xilinxmultiregvivadoimpl4_regs0 <= frontend_asyncfifo_graycounter0_q;
	xilinxmultiregvivadoimpl4_regs1 <= xilinxmultiregvivadoimpl4_regs0;
	xilinxmultiregvivadoimpl5_regs0 <= frontend_asyncfifo_graycounter1_q;
	xilinxmultiregvivadoimpl5_regs1 <= xilinxmultiregvivadoimpl5_regs0;
end

reg [31:0] mem[0:1023];
reg [9:0] memadr;
always @(posedge sys_clk) begin
	if (ibm360dd_sram_we[0])
		mem[ibm360dd_sram_adr][7:0] <= ibm360dd_sram_dat_w[7:0];
	if (ibm360dd_sram_we[1])
		mem[ibm360dd_sram_adr][15:8] <= ibm360dd_sram_dat_w[15:8];
	if (ibm360dd_sram_we[2])
		mem[ibm360dd_sram_adr][23:16] <= ibm360dd_sram_dat_w[23:16];
	if (ibm360dd_sram_we[3])
		mem[ibm360dd_sram_adr][31:24] <= ibm360dd_sram_dat_w[31:24];
	memadr <= ibm360dd_sram_adr;
end

assign ibm360dd_sram_dat_r = mem[memadr];

reg [7:0] mem_1[0:16];
reg [7:0] memdat;
always @(posedge sys_clk) begin
	memdat <= mem_1[mmap_adr];
end

assign mmap_dat_r = memdat;

initial begin
	//$readmemh("mem_1.init", mem_1);
end

reg [3:0] storage[0:7];
reg [2:0] memadr_1;
reg [3:0] memdat_1;
always @(posedge sys_clk) begin
	if (frontend_asyncfifo_wrport_we)
		storage[frontend_asyncfifo_wrport_adr] <= frontend_asyncfifo_wrport_dat_w;
	memadr_1 <= frontend_asyncfifo_wrport_adr;
end

always @(posedge sys_clk) begin
	memdat_1 <= storage[frontend_asyncfifo_rdport_adr];
end

assign frontend_asyncfifo_wrport_dat_r = storage[memadr_1];
assign frontend_asyncfifo_rdport_dat_r = memdat_1;

reg [2:0] storage_1[0:16383];
reg [13:0] memadr_2;
reg [2:0] memdat_2;
always @(posedge sys_clk) begin
	if (storage_mem_wrport_we)
		storage_1[storage_mem_wrport_adr] <= storage_mem_wrport_dat_w;
	memadr_2 <= storage_mem_wrport_adr;
end

always @(posedge sys_clk) begin
	if (storage_mem_rdport_re)
		memdat_2 <= storage_1[storage_mem_rdport_adr];
end

assign storage_mem_wrport_dat_r = storage_1[memadr_2];
assign storage_mem_rdport_dat_r = memdat_2;

endmodule
