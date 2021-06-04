/*
control register [7:0]ctrl:
bit 0:	When set, external clock is chosen for PWM/timer. When cleared, wb clock is used for PWM/timer.
bit 1:	When set,  PWM is enabled. When cleared,  timer is enabled.
bit 2:	When set,  PWM/timer starts. When cleared, PWM/timer stops.
bit 3:	When set, timer runs continuously. When cleared, timer runs one time.
bit 4:	When set, o_pwm enabled.
bit 5:	timer interrupt bit	When it is written with 0, interrupt request is cleared. 
bit 6:	When set, a 16-bit external signal i_DC is used as duty cycle. When cleared, register DC is used.
bit 7:	When set, counter reset for PWM/timer, it's output and bit 5 will also be cleared. When changing from PWM mode to timer mode reset is needed before timer starts.
*/
module	pwm(
//tlul interface
	input 			clk_i,												
	input 			rst_ni,												

	input 			re_i,											
	input 			we_i,											
	input  [7:0]    addr_i,											
	input  [31:0]   wdata_i,											
	input  [3:0]	be_i,										
	output [31:0]   rdata_o,																								
    output          o_pwm,
	output          o_pwm_2,
	output  reg     oe_pwm1,
	output  reg     oe_pwm2

);

////////////////////control logic////////////////////////////
parameter  adr_ctrl_1	=	0,
		   adr_divisor_1=	4,
		   adr_period_1	=	8,
		   adr_DC_1		=	12;

parameter  adr_ctrl_2	=	16,
		   adr_divisor_2=	20,
		   adr_period_2	=	24,
		   adr_DC_2		=	28;



					 
reg	[7:0]  ctrl;
reg	[15:0] period;		
reg	[15:0] DC_1;		
reg	[15:0] divisor;	

reg	[7:0]  ctrl_2;
reg	[15:0] period_2;		
reg	[15:0] DC_2;		
reg	[15:0] divisor_2;	

wire	   write;

assign	   write = we_i & ~re_i;

always@(posedge clk_i)
	if(~rst_ni)begin
		ctrl[4:2]	<=	0;
		ctrl[0]  	<=	0;
		ctrl[1] <= 1'b0;
		ctrl[7:6]	<=	0;
		DC_1			<=	0;
		period		<=	0;
		divisor		<=	0;

		
		ctrl_2[4:2]	 <=	0;
		ctrl_2[0]  	 <=	1'b0;
		ctrl_2[7:6]	 <=	0;
		ctrl_2[1]   <=  1'b0;
		DC_2		<=	0;
		period_2	<=	0;
		divisor_2	<=	0;
	end
	else if(write)begin
		case(addr_i)
			adr_ctrl_1:begin
				ctrl[0]	<=	wdata_i[0];
				ctrl[1] <= 1'b1;
				ctrl[4:2]	<=	wdata_i[4:2];
				ctrl[7:6]	<=	wdata_i[7:6];
			end

			adr_ctrl_2:begin
				ctrl_2[0]	<=	wdata_i[0];
				ctrl_2[1]   <= 1'b1;
				ctrl_2[4:2]	<=	wdata_i[4:2];
				ctrl_2[7:6]	<=	wdata_i[7:6];
			end

			adr_divisor_1	:  divisor	<=	wdata_i[15:0];
			adr_period_1	:  period   <=	wdata_i[15:0];
			adr_DC_1		:  DC_1		<=	wdata_i[15:0];

			adr_divisor_2	:  divisor_2	<=	wdata_i[15:0];
			adr_period_2	:  period_2		<=	wdata_i[15:0];
			adr_DC_2		:  DC_2			<=	wdata_i[15:0];
		endcase
	end

wire	pwm_1;
assign	pwm_1 = ctrl[1];

wire    pwm_2;
assign		pwm_2 = ctrl_2[1];

// clock division 
reg  clock_p1;
reg  clock_p2;

reg  [15:0] counter_p1;
reg  [15:0] counter_p2;
reg  [15:0] period_counter1;
reg  [15:0] period_counter2;

reg         pts;
reg         pts_2;

always @(posedge clk_i or negedge rst_ni) begin
  if(~rst_ni) begin
    clock_p1   <= 1'b0;
    clock_p2   <= 1'b0;
    counter_p1 <= 0;
    counter_p2 <= 0;
  end else begin
    if(pwm_1) begin
      counter_p1 <= counter_p1 + 1;
      if(counter_p1 == divisor-1) begin
        counter_p1 <= 0;
        clock_p1   <= ~clock_p1;
      end
    end

    
    if(pwm_2) begin
      counter_p2 <= counter_p2 + 1;
      if(counter_p2 == divisor_2-1) begin
        counter_p2 <= 0;
        clock_p2    <= ~clock_p2;
      end
    end

  end
end





always@(posedge clock_p1 )
	if(~rst_ni)begin
		pts   <= 0;
		period_counter1    <= 0;
	end
	else begin
	if(ctrl[2])begin
		if(pwm_1) begin
		    oe_pwm1 <= 1'b1;
			if(period_counter1	>=	period) period_counter1 <=	0;
			else period_counter1	<=	period_counter1+1;

			if(period_counter1	<	DC_1)	pts	<=	1'b1;
			else pts	<=	1'b0;
		end
	end
	else begin
			pts	    <= 1'b0;
			period_counter1	    <= 0;
			oe_pwm1 <= 0;
	end
end



always@(posedge clock_p2 )
	if(~rst_ni)begin
		pts_2	<=	0;
		period_counter2	<=	0;
	end
	else begin
	if(ctrl_2[2])begin
		if(pwm_2) begin
		     oe_pwm2 <= 1'b1;
			if(period_counter2	>=	period_2) period_counter2	<=	0;
			else period_counter2	<=	period_counter2+1;

			if(period_counter2	<	DC_2)	pts_2	<=	1'b1;
			else pts_2	<=	1'b0;
		end
	end
	else begin
			pts_2	<=	1'b0;
			period_counter2	<=	0;
			oe_pwm2 <=  1'b0;
	end
end
//////////////////////////////////////////////////////////

assign	o_pwm   = ctrl[4]? pts: 0;
assign	o_pwm_2 = ctrl_2[4]? pts_2: 0;
assign	rdata_o = (addr_i == adr_ctrl_1)   ? {8'h0,ctrl}  :
			  	(addr_i == adr_divisor_1)? divisor	  :
			  	(addr_i == adr_period_1) ? period		  :
			  	(addr_i == adr_DC_1)	   ? DC_1			  : 
				  (addr_i == adr_DC_2)	   ? DC_2		  :
				  (addr_i == adr_period_2) ? period_2	  :
				  (addr_i == adr_divisor_2)? divisor_2    :
				  (addr_i == adr_ctrl_2)   ? {8'h0,ctrl_2}:0;


endmodule
