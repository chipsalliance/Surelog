/* verilator lint_off DECLFILENAME */
module dut (fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam, fsm2rst,  ctrl, keys, brake, accelerate, rd, wr, Fsm2Out, speed);
   
input fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam;

input  fsm2rst, ctrl;
input  keys, brake, accelerate;
output [3:0] speed;   
output [2:0] Fsm2Out;
output rd, wr;  
      
wire fsm1clk, fsm3clk, fsm1rst, SlowRam, fsm2rst;
wire ctrl;
wire keys, brake, accelerate;

wire rd, wr;
wire [2:0] Fsm2Out;
wire [3:0] speed;


FSM1 F1(.Clk(fsm1clk),
        .Reset(fsm1rst),
        .SlowRam(SlowRam),
        .Read(rd),
        .Write(wr));
        
FSM2 F2(.clock(fsm2clk),
        .reset(fsm2rst),
        .control(ctrl),
        .y(Fsm2Out));
        
FSM3 F3(.clock(fsm3clk),
        .keys(keys),
        .brake(brake), 
        .accelerate(accelerate),
        .Speed(speed));

endmodule   


module FSM1 (Clk, Reset, SlowRam, Read, Write);
input Clk, Reset, SlowRam;
output Read, Write;

reg Read, Write, Wait, Delay;

parameter [3:0] ST_Read = 0, ST_Write = 1, ST_Delay = 2,
                ST_Trx = 3, ST_Hold = 4, ST_Block = 5,
                ST_Wait = 6, ST_Turn = 7, ST_Quit = 8,
                ST_Exit = 9, ST_Done = 10;
reg       [3:0] CurState, NextState;


always @(posedge Clk) begin:SEQ
  if (Reset)
    CurState <= ST_Read;
  else
    CurState <= NextState;
end

always @(CurState) begin:COMB
  case (CurState)

    ST_Trx: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 1) NextState = ST_Hold;
      else if (Write == 1) NextState = ST_Block;
      else if (SlowRam == 1) NextState = ST_Wait;
      else if (Wait == 0) NextState = ST_Turn;
      else if (Delay == 1) NextState = ST_Quit;
      else NextState = ST_Block;
    end

    ST_Hold: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 0) NextState = ST_Hold;
      else if (Write == 0) NextState = ST_Block;
      else if (SlowRam == 0) NextState = ST_Wait;
      else if (Wait == 1) NextState = ST_Turn;
      else if (Delay == 0) NextState = ST_Quit;
      else NextState = ST_Block;
    end

    ST_Block: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 1) NextState = ST_Wait;
      else if (Write == 1) NextState = ST_Turn;
      else if (SlowRam == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Done;
      else if (Delay == 1) NextState = ST_Exit;
      else NextState = ST_Block;
    end

    ST_Wait: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Turn: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 0) NextState = ST_Write;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Exit;
    end

    ST_Quit: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Wait == 1) NextState = ST_Wait;
      else if (Write == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Exit: begin
      Wait = ~Wait;
     Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Done;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Write;
    end

    ST_Done: begin
     Wait = ~Wait;
     Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Read: begin
      Read = 1;
      Write = 0;
      Wait = ~Wait;
      Delay = ~Delay;
      NextState = ST_Write;
    end
    
    ST_Write: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 1;
      if (SlowRam)
        NextState = ST_Delay;
      else
        NextState = ST_Read;
    end
    
    ST_Delay: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 0;
      NextState = ST_Read;
    end
    
    default: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 0;
      NextState = ST_Read;
    end
    
  endcase
end

endmodule


module FSM2(clock, reset, control, y);
input clock, reset, control;
output [2:0] y;
reg [2:0] y;

parameter [3:0] ST0 =0, ST1=1, ST2=2, ST3=3, ST4=4, ST5=5, ST6=6,ST7=7,
                ST8=8, ST9=9, ST10=10;
reg [3:0] CurrentState, NextState;

reg Ctrl1,Ctrl2,Ctrl3,Ctrl4,Ctrl5,Ctrl6,Ctrl7;

   
task SwitchCtrl;
begin
  Ctrl1 = ~Ctrl1;
  Ctrl2 = ~Ctrl2;
  Ctrl3 = ~Ctrl3;
  Ctrl4 = ~Ctrl4;
  Ctrl5 = ~Ctrl5;
  Ctrl6 = ~Ctrl6;
  Ctrl7 = ~Ctrl7;
end
endtask


always @(control or CurrentState) begin:COMB
  NextState = ST0;
  case (CurrentState)
    ST0:begin
      NextState = ST1;
      SwitchCtrl;
    end
    
    ST1:begin
      if (control)
        NextState = ST2;
      else
        NextState = ST3;
      SwitchCtrl;
    end
    
    ST2:begin
      NextState = ST3;
      SwitchCtrl;
    end
    
    ST3:begin
      NextState = ST0;
    end

   ST4:begin
      SwitchCtrl;
      NextState = ST5;
   end

   ST5:begin
      NextState = ST10;
      SwitchCtrl;
   end

   ST6:begin
      SwitchCtrl;
      NextState = ST3;
   end

   ST7:begin
      SwitchCtrl;
      if (Ctrl1) NextState = ST8;
      else if (Ctrl2) NextState = ST4;
      else if (Ctrl3) NextState = ST3;
      else if (Ctrl4) NextState = ST1;
      else if (Ctrl5) NextState = ST0;
      else if (Ctrl6) NextState = ST2;
      else if (Ctrl7) NextState = ST5;
      else NextState = ST1;
   end

   ST8:begin
      SwitchCtrl;
      if (Ctrl1) NextState = ST8;
      else if (!Ctrl2) NextState = ST4;
      else if (Ctrl3) NextState = ST3;
      else if (!Ctrl4) NextState = ST1;
      else if (Ctrl5) NextState = ST0;
      else if (!Ctrl6) NextState = ST2;
      else if (Ctrl7) NextState = ST5;
      else NextState = ST1;
   end

   ST9:begin
      SwitchCtrl;
      if (Ctrl3) NextState = ST7;
      else NextState = ST1;
   end

   ST10:begin
      SwitchCtrl;
      if (Ctrl4) NextState = ST6;
      else NextState = ST1;
   end
   default:begin
   end  
  endcase
end


always @(posedge clock or posedge reset) begin:SEQ
  if (reset)
    CurrentState <= ST0;
  else
    CurrentState <= NextState;
end
    

always @(CurrentState) begin:OUT_LOGIC
  case (CurrentState)
    ST0: y=1;
    ST1: y=2;
    ST2: y=3;
    ST3: y=4;
    default: y=1;
  endcase
end


endmodule


module FSM3(clock, keys, brake, accelerate, Speed);
input clock, keys, brake, accelerate;
output [3:0] Speed;
reg [3:0] Speed;

reg Ctrl1, Ctrl2, Ctrl3;

parameter Stop   =  4'b0000,
          Move   =  4'b0001,
          Turn   =  4'b0010,
          Slow   =  4'b0011,
          Medium =  4'b0100,
          Fast   =  4'b0101,
          Faster =  4'b0110;        


 always @(posedge clock or negedge keys) begin:FSM3
   
 if (keys) begin
   Ctrl1 <= 0;
   Ctrl2 <= 0;
   Ctrl3 <= 0;

   if (accelerate)
     case (Speed)
      Stop:   Speed <= Slow;
      Move:   Speed <= Faster;
      Turn:   Speed <= Move;
      Slow:   Speed <= Medium;
      Medium: Speed <= Fast;
      Fast:   Speed <= Fast;
      Faster: Speed <= Stop;
      default:begin
      end   
     endcase
   else if (brake)
    case (Speed)
      Stop:   Speed <= Faster;
      Move:   Speed <= Faster;
      Turn:   Speed <= Move;
      Slow:   Speed <= Stop;
      Medium: Speed <= Slow;
      Fast:   Speed <= Medium;
      Faster: Speed <= Slow;
      default:begin
      end  
    endcase
   else begin
    Speed <= Speed;
   end 
    
  end   
  else begin
   Speed <= Stop;  
   Ctrl1 <= ~Ctrl1;
   Ctrl2 <= ~Ctrl2;
   Ctrl3 <= ~Ctrl3; 
  end

 end

endmodule

