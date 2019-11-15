module text_graph(
		input wire clk,
		input wire [3:0] left_high, left_low,
		input wire [3:0] right_high, right_low,
		input wire [9:0] pix_x, pix_y,
		output wire text_on,
		output reg [2:0] text_rgb
    );
	wire [10:0] rom_add;
	wire [3:0] row_add;
	wire [2:0] bit_add;
	wire [7:0] temp_data;
	reg [7:0] char_add;
	wire bit_color;
	
	font_rom rom(.clk(clk),.addr(rom_add),.data(temp_data));
	
	assign text_on = (pix_y[9:5]==0) && (pix_x[9:4] >= 9 ) && (pix_x[9:4] < 24);
	assign row_add = pix_y[4:1];
	assign bit_add = pix_x[3:1];
	always @*
		case(pix_x[9:4])
			6'b001001: char_add = 7'h53;
			6'b001010: char_add = 7'h63;
			6'b001011: char_add = 7'h6f;
			6'b001100: char_add = 7'h72;
			6'b001101: char_add = 7'h65;
			6'b001110: char_add = 7'h3a;
			6'b001111: char_add = 7'h00;
			6'b010000: char_add = {3'b011,left_high};
			6'b010001: char_add = {3'b011,left_low};
			6'b010010: char_add = 7'h00;
			6'b010011: char_add = 7'h2d;
			6'b010100: char_add = 7'h2d;
			6'b010101: char_add = 7'h00;
			6'b010110: char_add = {3'b011,right_high};
			6'b010111: char_add = {3'b011,right_low};
			6'b011000: char_add = 7'h00;
		endcase

	always @*
	begin
		text_rgb = 3'b110;
		if(text_on && bit_color)
			text_rgb = 3'b000;
	end
	
	assign rom_add = {char_add, row_add};
	assign bit_color = temp_data[~bit_add];
	
endmodule
