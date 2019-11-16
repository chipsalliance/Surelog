/* Machine-generated using Migen */
module top(
	inout clk_if,
	inout i2c_scl,
	inout i2c_sda,
	output fx2_sloe,
	output fx2_slrd,
	output fx2_slwr,
	output fx2_pktend,
	output [1:0] fx2_fifoadr,
	input [3:0] fx2_flag,
	inout [7:0] fx2_fd,
	inout [7:0] io,
	inout [7:0] io_1
);

wire por_clk;
wire sys_clk;
wire sys_rst;
wire clk_buf;
reg [10:0] reset_delay = 11'd2047;
wire tstriple0_o0;
wire tstriple0_oe0;
wire tstriple0_i0;
wire tstriple1_o0;
wire tstriple1_oe0;
wire tstriple1_i0;
wire [6:0] i2c_slave_address;
reg i2c_slave_start;
wire i2c_slave_stop;
wire i2c_slave_write;
reg [7:0] i2c_slave_data_i = 8'd0;
reg i2c_slave_ack_o;
wire i2c_slave_read;
wire [7:0] i2c_slave_data_o;
wire i2c_slave_scl_i;
reg i2c_slave_scl_o = 1'd1;
wire i2c_slave_sda_i;
reg i2c_slave_sda_o = 1'd1;
wire i2c_slave_bus_sample;
wire i2c_slave_bus_setup;
wire i2c_slave_bus_start;
wire i2c_slave_bus_stop;
reg i2c_slave_scl_r = 1'd1;
reg i2c_slave_sda_r = 1'd1;
reg [2:0] i2c_slave_bitno = 3'd0;
reg [7:0] i2c_slave_shreg_i = 8'd0;
reg [7:0] i2c_slave_shreg_o = 8'd0;
reg i2c_slave_signal_is_el0 = 1'd1;
wire i2c_slave_fsm_is_el0;
reg i2c_slave_signal_is_el1 = 1'd0;
wire i2c_slave_fsm_is_el1;
wire i2c_slave_fsm_is_el2;
reg [7:0] registers_address = 8'd0;
reg dummyfifo0_we;
reg dummyfifo0_writable = 1'd0;
reg [7:0] dummyfifo0_din;
reg dummyfifo1_we;
reg dummyfifo1_writable = 1'd0;
reg [7:0] dummyfifo1_din;
reg dummyfifo2_re;
reg dummyfifo2_readable = 1'd0;
reg [7:0] dummyfifo2_dout = 8'd0;
reg dummyfifo3_re;
reg dummyfifo3_readable = 1'd0;
reg [7:0] dummyfifo3_dout = 8'd0;
wire tstriple0_o1;
wire tstriple0_oe1;
wire tstriple0_i1;
wire tstriple1_o1;
wire tstriple1_oe1;
wire tstriple1_i1;
wire tstriple2_o0;
wire tstriple2_oe0;
wire tstriple2_i0;
wire tstriple3_o0;
wire tstriple3_oe0;
wire tstriple3_i0;
wire tstriple4_o0;
wire tstriple4_oe0;
wire tstriple4_i0;
wire tstriple5_o0;
wire tstriple5_oe0;
wire tstriple5_i0;
wire tstriple6_o0;
wire tstriple6_oe0;
wire tstriple6_i0;
wire tstriple7_o0;
wire tstriple7_oe0;
wire tstriple7_i0;
wire tstriple0_o2;
wire tstriple0_oe2;
wire tstriple0_i2;
wire tstriple1_o2;
wire tstriple1_oe2;
wire tstriple1_i2;
wire tstriple2_o1;
wire tstriple2_oe1;
wire tstriple2_i1;
wire tstriple3_o1;
wire tstriple3_oe1;
wire tstriple3_i1;
wire tstriple4_o1;
wire tstriple4_oe1;
wire tstriple4_i1;
wire tstriple5_o1;
wire tstriple5_oe1;
wire tstriple5_i1;
wire tstriple6_o1;
wire tstriple6_oe1;
wire tstriple6_i1;
wire tstriple7_o1;
wire tstriple7_oe1;
wire tstriple7_i1;
reg [7:0] reg0 = 8'd0;
reg [7:0] reg1 = 8'd0;
wire [7:0] reg2;
reg ro_reg_dummy0 = 1'd0;
reg [7:0] reg3 = 8'd0;
reg [7:0] reg4 = 8'd0;
wire [7:0] reg5;
reg ro_reg_dummy1 = 1'd0;
reg [2:0] i2cslave_state = 3'd0;
reg [2:0] i2cslave_next_state;
reg [2:0] i2c_slave_bitno_i2cslave_next_value;
reg i2c_slave_bitno_i2cslave_next_value_ce;
reg [7:0] i2c_slave_shreg_i_i2cslave_t_next_value;
reg i2c_slave_shreg_i_i2cslave_t_next_value_ce;
reg i2c_slave_sda_o_i2cslave_f_next_value0;
reg i2c_slave_sda_o_i2cslave_f_next_value_ce0;
reg [7:0] i2c_slave_shreg_o_i2cslave_f_next_value1;
reg i2c_slave_shreg_o_i2cslave_f_next_value_ce1;
reg [7:0] i2c_slave_data_i_i2cslave_f_next_value2;
reg i2c_slave_data_i_i2cslave_f_next_value_ce2;
reg latch_addr = 1'd0;
reg [1:0] fx2arbiter_addr = 2'd0;
wire [7:0] fx2arbiter_o;
reg fx2arbiter_oe = 1'd0;
wire [7:0] fx2arbiter_i;
reg fx2arbiter_sloe = 1'd0;
reg fx2arbiter_slrd;
reg fx2arbiter_slwr;
reg fx2arbiter_pend;
wire [3:0] fx2arbiter_rdy;
reg [1:0] fx2arbiter_naddr;
reg [2:0] fx2arbiter_state = 3'd0;
reg [2:0] fx2arbiter_next_state;
reg [1:0] fx2arbiter_addr_fx2arbiter_next_value;
reg fx2arbiter_addr_fx2arbiter_next_value_ce;
reg fx2arbiter_sloe_fx2arbiter_t_next_value;
reg fx2arbiter_sloe_fx2arbiter_t_next_value_ce;
reg fx2arbiter_oe_fx2arbiter_f_next_value;
reg fx2arbiter_oe_fx2arbiter_f_next_value_ce;
reg [7:0] rhs_array_muxed0;
wire [7:0] lhs_array_muxed;
reg [7:0] rhs_array_muxed1;
reg basiclowerer_array_muxed0;
reg t_array_muxed0;
reg rhs_array_muxed2;
reg basiclowerer_array_muxed1;
reg t_array_muxed1;
reg basiclowerer_array_muxed2;
reg t_array_muxed2;
reg [7:0] array_muxed = 8'd0;
reg multiregimpl0_regs0 = 1'd1;
reg multiregimpl0_regs1 = 1'd1;
reg multiregimpl1_regs0 = 1'd1;
reg multiregimpl1_regs1 = 1'd1;


// Adding a dummy event (using a dummy signal 'dummy_s') to get the simulator
// to run the combinatorial process once at the beginning.
// synthesis translate_off
reg dummy_s;
initial dummy_s <= 1'd0;
// synthesis translate_on

assign i2c_slave_address = 4'd8;
assign sys_clk = por_clk;
assign sys_rst = (reset_delay != 1'd0);
assign i2c_slave_stop = i2c_slave_signal_is_el0;
assign i2c_slave_write = i2c_slave_signal_is_el1;
assign i2c_slave_read = i2c_slave_fsm_is_el2;
assign tstriple0_o0 = 1'd0;
assign tstriple0_oe0 = (~i2c_slave_scl_o);
assign tstriple1_o0 = 1'd0;
assign tstriple1_oe0 = (~i2c_slave_sda_o);
assign i2c_slave_bus_sample = ((~i2c_slave_scl_r) & i2c_slave_scl_i);
assign i2c_slave_bus_setup = (i2c_slave_scl_r & (~i2c_slave_scl_i));
assign i2c_slave_bus_start = ((i2c_slave_scl_i & i2c_slave_sda_r) & (~i2c_slave_sda_i));
assign i2c_slave_bus_stop = ((i2c_slave_scl_i & (~i2c_slave_sda_r)) & i2c_slave_sda_i);

// synthesis translate_off
reg dummy_d;
// synthesis translate_on
always @(*) begin
	i2c_slave_start <= 1'd0;
	i2cslave_next_state <= 3'd0;
	i2c_slave_bitno_i2cslave_next_value <= 3'd0;
	i2c_slave_bitno_i2cslave_next_value_ce <= 1'd0;
	i2c_slave_shreg_i_i2cslave_t_next_value <= 8'd0;
	i2c_slave_shreg_i_i2cslave_t_next_value_ce <= 1'd0;
	i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd0;
	i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd0;
	i2c_slave_shreg_o_i2cslave_f_next_value1 <= 8'd0;
	i2c_slave_shreg_o_i2cslave_f_next_value_ce1 <= 1'd0;
	i2c_slave_data_i_i2cslave_f_next_value2 <= 8'd0;
	i2c_slave_data_i_i2cslave_f_next_value_ce2 <= 1'd0;
	i2cslave_next_state <= i2cslave_state;
	case (i2cslave_state)
		1'd1: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_setup) begin
					i2c_slave_bitno_i2cslave_next_value <= 1'd0;
					i2c_slave_bitno_i2cslave_next_value_ce <= 1'd1;
					i2cslave_next_state <= 2'd2;
				end
			end
		end
		2'd2: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (i2c_slave_bus_sample) begin
						i2c_slave_shreg_i_i2cslave_t_next_value <= ((i2c_slave_shreg_i <<< 1'd1) | i2c_slave_sda_i);
						i2c_slave_shreg_i_i2cslave_t_next_value_ce <= 1'd1;
					end else begin
						if (i2c_slave_bus_setup) begin
							i2c_slave_bitno_i2cslave_next_value <= (i2c_slave_bitno + 1'd1);
							i2c_slave_bitno_i2cslave_next_value_ce <= 1'd1;
							if ((i2c_slave_bitno == 3'd7)) begin
								if ((i2c_slave_shreg_i[7:1] == i2c_slave_address)) begin
									i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd0;
									i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
									i2cslave_next_state <= 2'd3;
								end else begin
									i2cslave_next_state <= 1'd0;
								end
							end
						end
					end
				end
			end
		end
		2'd3: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (i2c_slave_bus_setup) begin
						if ((~i2c_slave_shreg_i[0])) begin
							i2c_slave_start <= 1'd1;
							i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd1;
							i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
							i2cslave_next_state <= 3'd4;
						end
					end else begin
						if (i2c_slave_bus_sample) begin
							if (i2c_slave_shreg_i[0]) begin
								i2c_slave_start <= 1'd1;
								i2cslave_next_state <= 3'd6;
								i2c_slave_shreg_o_i2cslave_f_next_value1 <= i2c_slave_data_o;
								i2c_slave_shreg_o_i2cslave_f_next_value_ce1 <= 1'd1;
							end
						end
					end
				end
			end
		end
		3'd4: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (i2c_slave_bus_sample) begin
						i2c_slave_shreg_i_i2cslave_t_next_value <= ((i2c_slave_shreg_i <<< 1'd1) | i2c_slave_sda_i);
						i2c_slave_shreg_i_i2cslave_t_next_value_ce <= 1'd1;
					end else begin
						if (i2c_slave_bus_setup) begin
							i2c_slave_bitno_i2cslave_next_value <= (i2c_slave_bitno + 1'd1);
							i2c_slave_bitno_i2cslave_next_value_ce <= 1'd1;
							if ((i2c_slave_bitno == 3'd7)) begin
								i2c_slave_data_i_i2cslave_f_next_value2 <= i2c_slave_shreg_i;
								i2c_slave_data_i_i2cslave_f_next_value_ce2 <= 1'd1;
								i2cslave_next_state <= 3'd5;
							end
						end
					end
				end
			end
		end
		3'd5: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (((~i2c_slave_scl_i) & i2c_slave_ack_o)) begin
						i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd0;
						i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
					end else begin
						if (i2c_slave_bus_setup) begin
							i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd1;
							i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
							i2cslave_next_state <= 3'd4;
						end
					end
				end
			end
		end
		3'd6: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (i2c_slave_bus_setup) begin
						i2c_slave_bitno_i2cslave_next_value <= (i2c_slave_bitno + 1'd1);
						i2c_slave_bitno_i2cslave_next_value_ce <= 1'd1;
						i2c_slave_sda_o_i2cslave_f_next_value0 <= i2c_slave_shreg_o[7];
						i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
						i2c_slave_shreg_o_i2cslave_f_next_value1 <= (i2c_slave_shreg_o <<< 1'd1);
						i2c_slave_shreg_o_i2cslave_f_next_value_ce1 <= 1'd1;
					end else begin
						if (i2c_slave_bus_sample) begin
							if ((i2c_slave_bitno == 1'd0)) begin
								i2c_slave_sda_o_i2cslave_f_next_value0 <= 1'd1;
								i2c_slave_sda_o_i2cslave_f_next_value_ce0 <= 1'd1;
								i2cslave_next_state <= 3'd7;
							end
						end
					end
				end
			end
		end
		3'd7: begin
			if (i2c_slave_bus_stop) begin
				i2cslave_next_state <= 1'd0;
			end else begin
				if (i2c_slave_bus_start) begin
					i2cslave_next_state <= 1'd1;
				end else begin
					if (i2c_slave_bus_sample) begin
						if ((~i2c_slave_sda_i)) begin
							i2cslave_next_state <= 3'd6;
						end else begin
							i2cslave_next_state <= 1'd0;
						end
					end
				end
			end
		end
		default: begin
			if (i2c_slave_bus_start) begin
				i2cslave_next_state <= 1'd1;
			end
		end
	endcase
// synthesis translate_off
	dummy_d <= dummy_s;
// synthesis translate_on
end
assign i2c_slave_fsm_is_el0 = ((~(i2cslave_state == 1'd0)) & (i2cslave_next_state == 1'd0));
assign i2c_slave_fsm_is_el1 = ((~(i2cslave_state == 3'd5)) & (i2cslave_next_state == 3'd5));
assign i2c_slave_fsm_is_el2 = ((~(i2cslave_state == 3'd6)) & (i2cslave_next_state == 3'd6));
assign i2c_slave_data_o = rhs_array_muxed0;

// synthesis translate_off
reg dummy_d_1;
// synthesis translate_on
always @(*) begin
	i2c_slave_ack_o <= 1'd0;
	if (i2c_slave_write) begin
		if ((latch_addr & (i2c_slave_data_i < 3'd6))) begin
			i2c_slave_ack_o <= 1'd1;
		end else begin
			if ((~latch_addr)) begin
				i2c_slave_ack_o <= 1'd1;
			end
		end
	end
// synthesis translate_off
	dummy_d_1 <= dummy_s;
// synthesis translate_on
end
assign fx2_fifoadr = fx2arbiter_addr;
assign fx2arbiter_rdy = (fx2_flag & {dummyfifo3_readable, dummyfifo2_readable, dummyfifo1_writable, dummyfifo0_writable});
assign lhs_array_muxed = fx2arbiter_i;

// synthesis translate_off
reg dummy_d_2;
// synthesis translate_on
always @(*) begin
	dummyfifo0_din <= 8'd0;
	dummyfifo1_din <= 8'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			dummyfifo0_din <= lhs_array_muxed;
		end
		default: begin
			dummyfifo1_din <= lhs_array_muxed;
		end
	endcase
// synthesis translate_off
	dummy_d_2 <= dummy_s;
// synthesis translate_on
end
assign fx2arbiter_o = rhs_array_muxed1;
assign fx2_sloe = (~fx2arbiter_sloe);
assign fx2_slrd = (~fx2arbiter_slrd);
assign fx2_slwr = (~fx2arbiter_slwr);
assign fx2_pktend = (~fx2arbiter_pend);

// synthesis translate_off
reg dummy_d_3;
// synthesis translate_on
always @(*) begin
	fx2arbiter_naddr <= 2'd0;
	case ({fx2arbiter_addr, fx2arbiter_rdy})
		1'd0: begin
			fx2arbiter_naddr <= 1'd1;
		end
		1'd1: begin
			fx2arbiter_naddr <= 1'd0;
		end
		2'd2: begin
			fx2arbiter_naddr <= 1'd1;
		end
		2'd3: begin
			fx2arbiter_naddr <= 1'd0;
		end
		3'd4: begin
			fx2arbiter_naddr <= 2'd2;
		end
		3'd5: begin
			fx2arbiter_naddr <= 1'd0;
		end
		3'd6: begin
			fx2arbiter_naddr <= 1'd1;
		end
		3'd7: begin
			fx2arbiter_naddr <= 1'd0;
		end
		4'd8: begin
			fx2arbiter_naddr <= 2'd3;
		end
		4'd9: begin
			fx2arbiter_naddr <= 1'd0;
		end
		4'd10: begin
			fx2arbiter_naddr <= 1'd1;
		end
		4'd11: begin
			fx2arbiter_naddr <= 1'd0;
		end
		4'd12: begin
			fx2arbiter_naddr <= 2'd2;
		end
		4'd13: begin
			fx2arbiter_naddr <= 1'd0;
		end
		4'd14: begin
			fx2arbiter_naddr <= 1'd1;
		end
		4'd15: begin
			fx2arbiter_naddr <= 1'd0;
		end
		5'd16: begin
			fx2arbiter_naddr <= 2'd2;
		end
		5'd17: begin
			fx2arbiter_naddr <= 1'd0;
		end
		5'd18: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd19: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd20: begin
			fx2arbiter_naddr <= 2'd2;
		end
		5'd21: begin
			fx2arbiter_naddr <= 2'd2;
		end
		5'd22: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd23: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd24: begin
			fx2arbiter_naddr <= 2'd3;
		end
		5'd25: begin
			fx2arbiter_naddr <= 2'd3;
		end
		5'd26: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd27: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd28: begin
			fx2arbiter_naddr <= 2'd2;
		end
		5'd29: begin
			fx2arbiter_naddr <= 2'd2;
		end
		5'd30: begin
			fx2arbiter_naddr <= 1'd1;
		end
		5'd31: begin
			fx2arbiter_naddr <= 1'd1;
		end
		6'd32: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd33: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd34: begin
			fx2arbiter_naddr <= 1'd1;
		end
		6'd35: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd36: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd37: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd38: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd39: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd40: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd41: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd42: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd43: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd44: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd45: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd46: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd47: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd48: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd49: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd50: begin
			fx2arbiter_naddr <= 1'd1;
		end
		6'd51: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd52: begin
			fx2arbiter_naddr <= 2'd2;
		end
		6'd53: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd54: begin
			fx2arbiter_naddr <= 1'd1;
		end
		6'd55: begin
			fx2arbiter_naddr <= 1'd0;
		end
		6'd56: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd57: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd58: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd59: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd60: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd61: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd62: begin
			fx2arbiter_naddr <= 2'd3;
		end
		6'd63: begin
			fx2arbiter_naddr <= 2'd3;
		end
	endcase
// synthesis translate_off
	dummy_d_3 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_4;
// synthesis translate_on
always @(*) begin
	dummyfifo0_we <= 1'd0;
	dummyfifo1_we <= 1'd0;
	dummyfifo2_re <= 1'd0;
	dummyfifo3_re <= 1'd0;
	fx2arbiter_slrd <= 1'd0;
	fx2arbiter_slwr <= 1'd0;
	fx2arbiter_pend <= 1'd0;
	fx2arbiter_next_state <= 3'd0;
	fx2arbiter_addr_fx2arbiter_next_value <= 2'd0;
	fx2arbiter_addr_fx2arbiter_next_value_ce <= 1'd0;
	fx2arbiter_sloe_fx2arbiter_t_next_value <= 1'd0;
	fx2arbiter_sloe_fx2arbiter_t_next_value_ce <= 1'd0;
	fx2arbiter_oe_fx2arbiter_f_next_value <= 1'd0;
	fx2arbiter_oe_fx2arbiter_f_next_value_ce <= 1'd0;
	t_array_muxed0 <= 1'd0;
	t_array_muxed1 <= 1'd0;
	t_array_muxed2 <= 1'd0;
	fx2arbiter_next_state <= fx2arbiter_state;
	case (fx2arbiter_state)
		1'd1: begin
			if (fx2arbiter_addr[1]) begin
				fx2arbiter_sloe_fx2arbiter_t_next_value <= 1'd0;
				fx2arbiter_sloe_fx2arbiter_t_next_value_ce <= 1'd1;
				fx2arbiter_next_state <= 2'd2;
			end else begin
				fx2arbiter_oe_fx2arbiter_f_next_value <= 1'd0;
				fx2arbiter_oe_fx2arbiter_f_next_value_ce <= 1'd1;
				fx2arbiter_next_state <= 3'd5;
			end
		end
		2'd2: begin
			fx2arbiter_oe_fx2arbiter_f_next_value <= 1'd1;
			fx2arbiter_oe_fx2arbiter_f_next_value_ce <= 1'd1;
			fx2arbiter_next_state <= 2'd3;
		end
		2'd3: begin
			if (basiclowerer_array_muxed0) begin
				fx2arbiter_slwr <= 1'd1;
				t_array_muxed0 <= 1'd1;
				case (fx2arbiter_addr[0])
					1'd0: begin
						dummyfifo2_re <= t_array_muxed0;
					end
					default: begin
						dummyfifo3_re <= t_array_muxed0;
					end
				endcase
				if ((~(fx2_flag & (1'd1 <<< fx2arbiter_addr)))) begin
					fx2arbiter_next_state <= 3'd4;
				end
			end else begin
				fx2arbiter_pend <= (~rhs_array_muxed2);
				fx2arbiter_next_state <= 1'd0;
			end
		end
		3'd4: begin
			if (basiclowerer_array_muxed1) begin
				fx2arbiter_slwr <= 1'd1;
				t_array_muxed1 <= 1'd1;
				case (fx2arbiter_addr[0])
					1'd0: begin
						dummyfifo2_re <= t_array_muxed1;
					end
					default: begin
						dummyfifo3_re <= t_array_muxed1;
					end
				endcase
				fx2arbiter_next_state <= 1'd0;
			end else begin
				if ((~basiclowerer_array_muxed2)) begin
					fx2arbiter_pend <= 1'd1;
					fx2arbiter_next_state <= 1'd0;
				end
			end
		end
		3'd5: begin
			fx2arbiter_sloe_fx2arbiter_t_next_value <= 1'd1;
			fx2arbiter_sloe_fx2arbiter_t_next_value_ce <= 1'd1;
			fx2arbiter_next_state <= 3'd6;
		end
		3'd6: begin
			if ((fx2arbiter_rdy & (1'd1 <<< fx2arbiter_addr))) begin
				fx2arbiter_slrd <= 1'd1;
				t_array_muxed2 <= 1'd1;
				case (fx2arbiter_addr[0])
					1'd0: begin
						dummyfifo0_we <= t_array_muxed2;
					end
					default: begin
						dummyfifo1_we <= t_array_muxed2;
					end
				endcase
			end else begin
				fx2arbiter_next_state <= 1'd0;
			end
		end
		default: begin
			fx2arbiter_addr_fx2arbiter_next_value <= fx2arbiter_naddr;
			fx2arbiter_addr_fx2arbiter_next_value_ce <= 1'd1;
			if (fx2arbiter_rdy) begin
				fx2arbiter_next_state <= 1'd1;
			end
		end
	endcase
// synthesis translate_off
	dummy_d_4 <= dummy_s;
// synthesis translate_on
end
assign {tstriple7_oe0, tstriple6_oe0, tstriple5_oe0, tstriple4_oe0, tstriple3_oe0, tstriple2_oe0, tstriple1_oe1, tstriple0_oe1} = reg0;
assign {tstriple7_o0, tstriple6_o0, tstriple5_o0, tstriple4_o0, tstriple3_o0, tstriple2_o0, tstriple1_o1, tstriple0_o1} = reg1;
assign reg2 = {tstriple7_i0, tstriple6_i0, tstriple5_i0, tstriple4_i0, tstriple3_i0, tstriple2_i0, tstriple1_i1, tstriple0_i1};
assign {tstriple7_oe1, tstriple6_oe1, tstriple5_oe1, tstriple4_oe1, tstriple3_oe1, tstriple2_oe1, tstriple1_oe2, tstriple0_oe2} = reg3;
assign {tstriple7_o1, tstriple6_o1, tstriple5_o1, tstriple4_o1, tstriple3_o1, tstriple2_o1, tstriple1_o2, tstriple0_o2} = reg4;
assign reg5 = {tstriple7_i1, tstriple6_i1, tstriple5_i1, tstriple4_i1, tstriple3_i1, tstriple2_i1, tstriple1_i2, tstriple0_i2};

// synthesis translate_off
reg dummy_d_5;
// synthesis translate_on
always @(*) begin
	rhs_array_muxed0 <= 8'd0;
	case (registers_address)
		1'd0: begin
			rhs_array_muxed0 <= reg0;
		end
		1'd1: begin
			rhs_array_muxed0 <= reg1;
		end
		2'd2: begin
			rhs_array_muxed0 <= reg2;
		end
		2'd3: begin
			rhs_array_muxed0 <= reg3;
		end
		3'd4: begin
			rhs_array_muxed0 <= reg4;
		end
		default: begin
			rhs_array_muxed0 <= reg5;
		end
	endcase
// synthesis translate_off
	dummy_d_5 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_6;
// synthesis translate_on
always @(*) begin
	rhs_array_muxed1 <= 8'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			rhs_array_muxed1 <= dummyfifo2_dout;
		end
		default: begin
			rhs_array_muxed1 <= dummyfifo3_dout;
		end
	endcase
// synthesis translate_off
	dummy_d_6 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_7;
// synthesis translate_on
always @(*) begin
	basiclowerer_array_muxed0 <= 1'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			basiclowerer_array_muxed0 <= dummyfifo2_readable;
		end
		default: begin
			basiclowerer_array_muxed0 <= dummyfifo3_readable;
		end
	endcase
// synthesis translate_off
	dummy_d_7 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_8;
// synthesis translate_on
always @(*) begin
	rhs_array_muxed2 <= 1'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			rhs_array_muxed2 <= 1'd0;
		end
		default: begin
			rhs_array_muxed2 <= 1'd0;
		end
	endcase
// synthesis translate_off
	dummy_d_8 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_9;
// synthesis translate_on
always @(*) begin
	basiclowerer_array_muxed1 <= 1'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			basiclowerer_array_muxed1 <= dummyfifo2_readable;
		end
		default: begin
			basiclowerer_array_muxed1 <= dummyfifo3_readable;
		end
	endcase
// synthesis translate_off
	dummy_d_9 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_10;
// synthesis translate_on
always @(*) begin
	basiclowerer_array_muxed2 <= 1'd0;
	case (fx2arbiter_addr[0])
		1'd0: begin
			basiclowerer_array_muxed2 <= 1'd0;
		end
		default: begin
			basiclowerer_array_muxed2 <= 1'd0;
		end
	endcase
// synthesis translate_off
	dummy_d_10 <= dummy_s;
// synthesis translate_on
end
assign i2c_slave_scl_i = multiregimpl0_regs1;
assign i2c_slave_sda_i = multiregimpl1_regs1;

always @(posedge por_clk) begin
	if ((reset_delay != 1'd0)) begin
		reset_delay <= (reset_delay - 1'd1);
	end
end

always @(posedge sys_clk) begin
	i2c_slave_scl_r <= i2c_slave_scl_i;
	i2c_slave_sda_r <= i2c_slave_sda_i;
	i2c_slave_signal_is_el0 <= i2c_slave_fsm_is_el0;
	i2c_slave_signal_is_el1 <= i2c_slave_fsm_is_el1;
	i2cslave_state <= i2cslave_next_state;
	if (i2c_slave_bitno_i2cslave_next_value_ce) begin
		i2c_slave_bitno <= i2c_slave_bitno_i2cslave_next_value;
	end
	if (i2c_slave_shreg_i_i2cslave_t_next_value_ce) begin
		i2c_slave_shreg_i <= i2c_slave_shreg_i_i2cslave_t_next_value;
	end
	if (i2c_slave_sda_o_i2cslave_f_next_value_ce0) begin
		i2c_slave_sda_o <= i2c_slave_sda_o_i2cslave_f_next_value0;
	end
	if (i2c_slave_shreg_o_i2cslave_f_next_value_ce1) begin
		i2c_slave_shreg_o <= i2c_slave_shreg_o_i2cslave_f_next_value1;
	end
	if (i2c_slave_data_i_i2cslave_f_next_value_ce2) begin
		i2c_slave_data_i <= i2c_slave_data_i_i2cslave_f_next_value2;
	end
	if (i2c_slave_start) begin
		latch_addr <= 1'd1;
	end
	if (i2c_slave_write) begin
		if (latch_addr) begin
			if ((i2c_slave_data_i < 3'd6)) begin
				latch_addr <= 1'd0;
				registers_address <= i2c_slave_data_i;
			end
		end else begin
			array_muxed = i2c_slave_data_i;
			case (registers_address)
				1'd0: begin
					reg0 <= array_muxed;
				end
				1'd1: begin
					reg1 <= array_muxed;
				end
				2'd2: begin
					ro_reg_dummy0 <= array_muxed;
				end
				2'd3: begin
					reg3 <= array_muxed;
				end
				3'd4: begin
					reg4 <= array_muxed;
				end
				default: begin
					ro_reg_dummy1 <= array_muxed;
				end
			endcase
		end
	end
	fx2arbiter_state <= fx2arbiter_next_state;
	if (fx2arbiter_addr_fx2arbiter_next_value_ce) begin
		fx2arbiter_addr <= fx2arbiter_addr_fx2arbiter_next_value;
	end
	if (fx2arbiter_sloe_fx2arbiter_t_next_value_ce) begin
		fx2arbiter_sloe <= fx2arbiter_sloe_fx2arbiter_t_next_value;
	end
	if (fx2arbiter_oe_fx2arbiter_f_next_value_ce) begin
		fx2arbiter_oe <= fx2arbiter_oe_fx2arbiter_f_next_value;
	end
	if (sys_rst) begin
		i2c_slave_data_i <= 8'd0;
		i2c_slave_sda_o <= 1'd1;
		i2c_slave_scl_r <= 1'd1;
		i2c_slave_sda_r <= 1'd1;
		i2c_slave_bitno <= 3'd0;
		i2c_slave_shreg_i <= 8'd0;
		i2c_slave_shreg_o <= 8'd0;
		i2c_slave_signal_is_el0 <= 1'd1;
		i2c_slave_signal_is_el1 <= 1'd0;
		registers_address <= 8'd0;
		reg0 <= 8'd0;
		reg1 <= 8'd0;
		ro_reg_dummy0 <= 1'd0;
		reg3 <= 8'd0;
		reg4 <= 8'd0;
		ro_reg_dummy1 <= 1'd0;
		i2cslave_state <= 3'd0;
		latch_addr <= 1'd0;
		fx2arbiter_addr <= 2'd0;
		fx2arbiter_oe <= 1'd0;
		fx2arbiter_sloe <= 1'd0;
		fx2arbiter_state <= 3'd0;
	end
	multiregimpl0_regs0 <= tstriple0_i0;
	multiregimpl0_regs1 <= multiregimpl0_regs0;
	multiregimpl1_regs0 <= tstriple1_i0;
	multiregimpl1_regs1 <= multiregimpl1_regs0;
end

SB_IO #(
	.PIN_TYPE(6'd1)
) SB_IO (
	.PACKAGE_PIN(clk_if),
	.D_IN_0(clk_buf)
);

SB_GB SB_GB(
	.USER_SIGNAL_TO_GLOBAL_BUFFER(clk_buf),
	.GLOBAL_BUFFER_OUTPUT(por_clk)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_1 (
	.D_OUT_0(tstriple0_o0),
	.OUTPUT_ENABLE(tstriple0_oe0),
	.PACKAGE_PIN(i2c_scl),
	.D_IN_0(tstriple0_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_2 (
	.D_OUT_0(tstriple1_o0),
	.OUTPUT_ENABLE(tstriple1_oe0),
	.PACKAGE_PIN(i2c_sda),
	.D_IN_0(tstriple1_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_3 (
	.D_OUT_0(tstriple0_o1),
	.OUTPUT_ENABLE(tstriple0_oe1),
	.PACKAGE_PIN(io[0][0]),
	.D_IN_0(tstriple0_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_4 (
	.D_OUT_0(tstriple1_o1),
	.OUTPUT_ENABLE(tstriple1_oe1),
	.PACKAGE_PIN(io[1][0]),
	.D_IN_0(tstriple1_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_5 (
	.D_OUT_0(tstriple2_o0),
	.OUTPUT_ENABLE(tstriple2_oe0),
	.PACKAGE_PIN(io[2][0]),
	.D_IN_0(tstriple2_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_6 (
	.D_OUT_0(tstriple3_o0),
	.OUTPUT_ENABLE(tstriple3_oe0),
	.PACKAGE_PIN(io[3][0]),
	.D_IN_0(tstriple3_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_7 (
	.D_OUT_0(tstriple4_o0),
	.OUTPUT_ENABLE(tstriple4_oe0),
	.PACKAGE_PIN(io[4][0]),
	.D_IN_0(tstriple4_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_8 (
	.D_OUT_0(tstriple5_o0),
	.OUTPUT_ENABLE(tstriple5_oe0),
	.PACKAGE_PIN(io[5][0]),
	.D_IN_0(tstriple5_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_9 (
	.D_OUT_0(tstriple6_o0),
	.OUTPUT_ENABLE(tstriple6_oe0),
	.PACKAGE_PIN(io[6][0]),
	.D_IN_0(tstriple6_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_10 (
	.D_OUT_0(tstriple7_o0),
	.OUTPUT_ENABLE(tstriple7_oe0),
	.PACKAGE_PIN(io[7][0]),
	.D_IN_0(tstriple7_i0)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_11 (
	.D_OUT_0(tstriple0_o2),
	.OUTPUT_ENABLE(tstriple0_oe2),
	.PACKAGE_PIN(io_1[0][0]),
	.D_IN_0(tstriple0_i2)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_12 (
	.D_OUT_0(tstriple1_o2),
	.OUTPUT_ENABLE(tstriple1_oe2),
	.PACKAGE_PIN(io_1[1][0]),
	.D_IN_0(tstriple1_i2)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_13 (
	.D_OUT_0(tstriple2_o1),
	.OUTPUT_ENABLE(tstriple2_oe1),
	.PACKAGE_PIN(io_1[2][0]),
	.D_IN_0(tstriple2_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_14 (
	.D_OUT_0(tstriple3_o1),
	.OUTPUT_ENABLE(tstriple3_oe1),
	.PACKAGE_PIN(io_1[3][0]),
	.D_IN_0(tstriple3_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_15 (
	.D_OUT_0(tstriple4_o1),
	.OUTPUT_ENABLE(tstriple4_oe1),
	.PACKAGE_PIN(io_1[4][0]),
	.D_IN_0(tstriple4_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_16 (
	.D_OUT_0(tstriple5_o1),
	.OUTPUT_ENABLE(tstriple5_oe1),
	.PACKAGE_PIN(io_1[5][0]),
	.D_IN_0(tstriple5_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_17 (
	.D_OUT_0(tstriple6_o1),
	.OUTPUT_ENABLE(tstriple6_oe1),
	.PACKAGE_PIN(io_1[6][0]),
	.D_IN_0(tstriple6_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_18 (
	.D_OUT_0(tstriple7_o1),
	.OUTPUT_ENABLE(tstriple7_oe1),
	.PACKAGE_PIN(io_1[7][0]),
	.D_IN_0(tstriple7_i1)
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_19 (
	.D_OUT_0(fx2arbiter_o[0]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[0]),
	.D_IN_0(fx2arbiter_i[0])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_20 (
	.D_OUT_0(fx2arbiter_o[1]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[1]),
	.D_IN_0(fx2arbiter_i[1])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_21 (
	.D_OUT_0(fx2arbiter_o[2]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[2]),
	.D_IN_0(fx2arbiter_i[2])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_22 (
	.D_OUT_0(fx2arbiter_o[3]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[3]),
	.D_IN_0(fx2arbiter_i[3])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_23 (
	.D_OUT_0(fx2arbiter_o[4]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[4]),
	.D_IN_0(fx2arbiter_i[4])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_24 (
	.D_OUT_0(fx2arbiter_o[5]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[5]),
	.D_IN_0(fx2arbiter_i[5])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_25 (
	.D_OUT_0(fx2arbiter_o[6]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[6]),
	.D_IN_0(fx2arbiter_i[6])
);

SB_IO #(
	.PIN_TYPE(6'd41)
) SB_IO_26 (
	.D_OUT_0(fx2arbiter_o[7]),
	.OUTPUT_ENABLE(fx2arbiter_oe),
	.PACKAGE_PIN(fx2_fd[7]),
	.D_IN_0(fx2arbiter_i[7])
);

endmodule
