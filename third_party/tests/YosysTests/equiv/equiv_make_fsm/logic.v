module \$fsm (CLK, ARST, CTRL_IN, CTRL_OUT);

parameter NAME = "";

parameter CLK_POLARITY = 1'b1;
parameter ARST_POLARITY = 1'b1;

parameter CTRL_IN_WIDTH = 1;
parameter CTRL_OUT_WIDTH = 1;

parameter STATE_BITS = 1;
parameter STATE_NUM = 1;
parameter STATE_NUM_LOG2 = 1;
parameter STATE_RST = 0;
parameter STATE_TABLE = 1'b0;

parameter TRANS_NUM = 1;
parameter TRANS_TABLE = 4'b0x0x;

input CLK, ARST;
input [CTRL_IN_WIDTH-1:0] CTRL_IN;
output reg [CTRL_OUT_WIDTH-1:0] CTRL_OUT;

wire pos_clk = CLK == CLK_POLARITY;
wire pos_arst = ARST == ARST_POLARITY;

reg [STATE_BITS-1:0] state;
reg [STATE_BITS-1:0] state_tmp;
reg [STATE_BITS-1:0] next_state;

reg [STATE_BITS-1:0] tr_state_in;
reg [STATE_BITS-1:0] tr_state_out;
reg [CTRL_IN_WIDTH-1:0] tr_ctrl_in;
reg [CTRL_OUT_WIDTH-1:0] tr_ctrl_out;

integer i;

task tr_fetch;
	input [31:0] tr_num;
	reg [31:0] tr_pos;
	reg [STATE_NUM_LOG2-1:0] state_num;
	begin
		tr_pos = (2*STATE_NUM_LOG2+CTRL_IN_WIDTH+CTRL_OUT_WIDTH)*tr_num;
		tr_ctrl_out = TRANS_TABLE >> tr_pos;
		tr_pos = tr_pos + CTRL_OUT_WIDTH;
		state_num = TRANS_TABLE >> tr_pos;
		tr_state_out = STATE_TABLE >> (STATE_BITS*state_num);
		tr_pos = tr_pos + STATE_NUM_LOG2;
		tr_ctrl_in = TRANS_TABLE >> tr_pos;
		tr_pos = tr_pos + CTRL_IN_WIDTH;
		state_num = TRANS_TABLE >> tr_pos;
		tr_state_in = STATE_TABLE >> (STATE_BITS*state_num);
		tr_pos = tr_pos + STATE_NUM_LOG2;
	end
endtask
/*

always @(posedge pos_clk, posedge pos_arst) begin
	if (pos_arst) begin
		state_tmp = STATE_TABLE[STATE_BITS*(STATE_RST+1)-1:STATE_BITS*STATE_RST];
		for (i = 0; i < STATE_BITS; i = i+1)
			if (state_tmp[i] === 1'bz)
				state_tmp[i] = 0;
		state <= state_tmp;
	end else begin
		state_tmp = next_state;
		for (i = 0; i < STATE_BITS; i = i+1)
			if (state_tmp[i] === 1'bz)
				state_tmp[i] = 0;
		state <= state_tmp;
	end
end

always @(state, CTRL_IN) begin
	next_state <= STATE_TABLE[STATE_BITS*(STATE_RST+1)-1:STATE_BITS*STATE_RST];
	CTRL_OUT <= 'bx;
	// $display("---");
	// $display("Q: %b %b", state, CTRL_IN);
	for (i = 0; i < TRANS_NUM; i = i+1) begin
		tr_fetch(i);
		// $display("T: %b %b -> %b %b [%d]", tr_state_in, tr_ctrl_in, tr_state_out, tr_ctrl_out, i);
		casez ({state, CTRL_IN})
			{tr_state_in, tr_ctrl_in}: begin
				// $display("-> %b %b <-   MATCH", state, CTRL_IN);
				{next_state, CTRL_OUT} <= {tr_state_out, tr_ctrl_out};
			end
		endcase
	end
end
*/
endmodule
