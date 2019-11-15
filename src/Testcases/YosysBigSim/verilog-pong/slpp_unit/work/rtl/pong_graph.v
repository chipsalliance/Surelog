`timescale 1ns / 1ps
module pong_graph(
		input wire clk, reset,
		input wire [1:0] btn1,
		input wire [1:0] btn2,
		input wire [9:0] pix_x, pix_y,
		input wire graph_still,
		output reg miss, hit_left, hit_right,
		output wire graph_on,
		output reg [2:0] graph_rgb,
		output reg [7:0] left_score, right_score
	);

	// define constant value here
	localparam MAX_X = 640;
	localparam MAX_Y = 480;
	localparam BALL_SIZE = 8;
	localparam BAR_SIZE = 108;
	localparam BAR_V = 4;
	localparam BAR_LEFT_X = 40;
	localparam BAR_RIGHT_X = 600;
	localparam BAR_WIDTH = 6;
	localparam V_X = 3;
	localparam V_X_N = -3;
	localparam V_Y = 3;
	localparam V_Y_N = -3;

	// all about ball
	reg [9:0] ball_x, ball_y;
	wire [9:0] ball_x_next, ball_y_next;
	wire [9:0] ball_right, ball_left, ball_top, ball_bottom;
	reg [9:0] x_delta, x_delta_next;
	reg [9:0] y_delta, y_delta_next;
	
	wire [2:0] ball_row, ball_col;
	reg [7:0] ball_data;
	
	// all about the output rgb
	wire bar_on, ball_on;
	wire [2:0] bar_rgb, ball_rgb;
	
	// colors
	assign bar_rgb = 3'b101;	// purple
	assign ball_rgb = 3'b100;	// red
	
	// bar right & left
	reg [9:0] bar_right, bar_right_next;
	reg [9:0] bar_left, bar_left_next;
	wire [9:0] bar_right_top, bar_right_bottom;
	wire [9:0] bar_left_top, bar_left_bottom;
	
	// to judge wether added
	reg added;

	// refr_tick: 1-clock tick asserted at start of v-sync
	//	   i.e., when the screen is refreshed (60 Hz)
	assign refr_tick = (pix_y == 481) && (pix_x == 0);
	
	// keep refreshing all the assistant values
	assign ball_right = ball_x + 4;
	assign ball_left = ball_x - 3;
	assign ball_top = ball_y - 3;
	assign ball_bottom = ball_y + 4;
	assign ball_x_next = (graph_still) ? MAX_X / 2 :
						 (refr_tick) ? ball_x + x_delta : ball_x;
	assign ball_y_next = (graph_still) ? MAX_Y / 2 :
						 (refr_tick) ? ball_y + y_delta : ball_y;

	assign ball_row = pix_y[2:0] - ball_top[2:0];
	assign ball_col = pix_x[2:0] - ball_left[2:0];
	assign ball_bit = ball_data[ball_col];

	assign ball_on = (ball_left <= pix_x) && (pix_x <= ball_right)
					 && (ball_top <= pix_y) && (pix_y <= ball_bottom)
					 && ball_bit;

	assign bar_right_top = bar_right - BAR_SIZE / 2;
	assign bar_right_bottom = bar_right + BAR_SIZE / 2;
	assign bar_left_top = bar_left - BAR_SIZE / 2;
	assign bar_left_bottom = bar_left + BAR_SIZE / 2;
	
	assign bar_on = ((BAR_LEFT_X <= pix_x) && (pix_x <= BAR_LEFT_X + BAR_WIDTH)
					 && (bar_right_top <= pix_y) && (pix_y <= bar_right_bottom))
					 || ((BAR_RIGHT_X >= pix_x) && (pix_x >= BAR_RIGHT_X - BAR_WIDTH)
					 && (bar_left_top <= pix_y) && (pix_y <= bar_left_bottom));

	// provide the ball's data
	always @*
		case (ball_row)
			3'h0: ball_data = 8'b00111100;	 //   ****
			3'h1: ball_data = 8'b01111110;	 //  ******
			3'h2: ball_data = 8'b11111111;	 // ********
			3'h3: ball_data = 8'b11111111;	 // ********
			3'h4: ball_data = 8'b11111111;	 // ********
			3'h5: ball_data = 8'b11111111;	 // ********
			3'h6: ball_data = 8'b01111110;	 //  ******
			3'h7: ball_data = 8'b00111100;	 //   ****
		endcase
	
	// move ball and deal reset
	always @(posedge clk, posedge reset)
	begin
		if (reset)
			begin
				bar_right <= 0;
				bar_left <= 0;
				ball_x <= 0;
				ball_y <= 0;
				x_delta <= V_X;
				y_delta <= V_Y;
			end
		else
			begin
				bar_right <= bar_right_next;
				bar_left <= bar_left_next;
				ball_x <= ball_x_next;
				ball_y <= ball_y_next;
				x_delta <= x_delta_next;
				y_delta <= y_delta_next;
			end
	end

	// calc the position of bar
	always @*
	begin
		bar_right_next = bar_right;
		if (graph_still)
			bar_right_next = MAX_Y / 2;
		else if (refr_tick)
			if (btn1[1] & (bar_right_bottom < (MAX_Y - 1 - BAR_V)))
				bar_right_next = bar_right + BAR_V;
			else if (btn1[0] & (bar_right_top > BAR_V)) 
				bar_right_next = bar_right - BAR_V;

		bar_left_next = bar_left;
		if (graph_still)
			bar_left_next = MAX_Y / 2;
		else if (refr_tick)
			if (btn2[1] & (bar_left_bottom < (MAX_Y - 1 - BAR_V)))
				bar_left_next = bar_left + BAR_V;
			else if (btn2[0] & (bar_left_top > BAR_V)) 
				bar_left_next = bar_left - BAR_V;
	end

	// deal with the ball's movement
	always @(posedge refr_tick, posedge reset)
	  if (reset) begin
		hit_left = 1'b0;
		hit_right = 1'b0;
		miss = 1'b0;
		x_delta_next = V_X;
		y_delta_next = V_Y;
		right_score = 8'b0;
		left_score = 8'b0;
		added = 0;
	  end else begin
		hit_left = 1'b0;
		hit_right = 1'b0;
		miss = 1'b0;
		x_delta_next = x_delta;
		y_delta_next = y_delta;
		if (graph_still)
			begin
				x_delta_next = V_X;
				y_delta_next = V_Y;
				hit_right = 1'b0;
				hit_left = 1'b0;
				miss = 1'b0;
				right_score = 8'b0;
				left_score = 8'b0;
				added = 0;
			end
		else if (ball_top <= 5)
			begin
				y_delta_next = V_Y;
				hit_right = 1'b0;
				hit_left = 1'b0;
				added = 0;
			end
		else if (ball_bottom >= MAX_Y - 5)
			begin
				y_delta_next = V_Y_N;
				hit_right = 1'b0;
				hit_left = 1'b0;
				added = 0;
			end
		else if (BAR_LEFT_X <= ball_left && BAR_LEFT_X + BAR_WIDTH >= ball_left - 1
				&& ball_top - bar_right + BAR_SIZE / 2 > 0 && bar_right - ball_top + BAR_SIZE / 2 > 0)
			begin
				hit_left = 1'b1;
				hit_right = 1'b0;
				x_delta_next = V_X;
				if(added == 0)
				begin
					if(left_score[3:0] == 4'b1001)
					begin
						left_score[3:0] = 4'b0000;
						left_score[7:4] = left_score[7:4] + 1;
					end
					else
						left_score[3:0] = left_score[3:0] + 1;
				end
				added = 1;
			end
		else if (BAR_RIGHT_X >= ball_right && BAR_RIGHT_X - BAR_WIDTH <= ball_right + 1
				&& ball_top - bar_left + BAR_SIZE / 2 > 0 && bar_left - ball_top + BAR_SIZE / 2 > 0)
			begin
				hit_right = 1'b1;
				hit_left = 1'b0;
				x_delta_next = V_X_N;
				if(added == 0)
				begin
					if(right_score[3:0] == 4'h9)
					begin
						right_score[3:0] = 4'h0;
						right_score[7:4] = right_score[7:4] + 1;
					end
					else
						right_score[3:0] = right_score[3:0] + 1;
				end
				added = 1;
			end
		else if (ball_right >= MAX_X - 10 || ball_right <= 10)
			begin
				added = 0;
				miss = 1'b1;
				hit_right = 1'b0;
				hit_left = 1'b0;
				right_score = 8'b0;
				left_score = 8'b0;
			end
	  end

	// assign rgb to the correct color
	always @* 
	begin
		if (bar_on)
			graph_rgb = bar_rgb;
		else if (ball_on)
			graph_rgb = ball_rgb;
		else
			graph_rgb = 3'b000;
	end

	// decide wether need to display
	assign graph_on =  bar_on | ball_on;

endmodule
