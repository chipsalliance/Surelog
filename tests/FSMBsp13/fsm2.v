module FSM2(clock, reset, control, y);
input clock, reset, control;
output [2:0] y;
reg [2:0] y;

parameter [3:0] ST0 =0, ST1=1, ST2=2, ST3=3, ST4=4, ST5=5, ST6=6,ST7=7,
                ST8=8, ST9=9, ST10=10;
reg [3:0] CurrentState, NextState;

reg Ctrl1,Ctrl2,Ctrl3,Ctrl4,Ctrl5,Ctrl6,Ctrl7;

initial begin
  Ctrl1 = 1;
  Ctrl2 = 0;
  Ctrl3 = 1;
  Ctrl4 = 0;
  Ctrl5 = 1;
  Ctrl6 = 0;
  Ctrl7 = 1;
end

   
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

  endcase
end


always @(posedge clock or posedge reset) begin:SEQ
  if (reset)
    CurrentState = ST0;
  else
    CurrentState = NextState;
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


