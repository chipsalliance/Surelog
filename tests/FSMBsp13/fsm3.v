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

initial begin
  Ctrl1 = 0;
  Ctrl2 = 1;
  Ctrl3 = 0;
end
   
always @(posedge clock or negedge keys) begin:FSM3
  if (!keys)
   Speed = Stop;
  else if (accelerate)
    case (Speed)
      Stop:   Speed = Slow;
      Move:   Speed = Faster;
      Turn:   Speed = Move;
      Slow:   Speed = Medium;
      Medium: Speed = Fast;
      Fast:   Speed = Fast;
      Faster: Speed = Stop;
    endcase
  else if (brake)
    case (Speed)
      Stop:   Speed = Faster;
      Move:   Speed = Faster;
      Turn:   Speed = Move;
      Slow:   Speed = Stop;
      Medium: Speed = Slow;
      Fast:   Speed = Medium;
      Faster: Speed = Slow;
    endcase
  else
    Speed = Speed;

 if (!keys)
   Ctrl1 = 0;
 else
   Ctrl1 = ~Ctrl1;

 if (!keys)
   Ctrl2 = 0;
 else
   Ctrl2 = ~Ctrl2;

 if (!keys)
   Ctrl3 = 0;
 else
   Ctrl3 = ~Ctrl3;
 end

endmodule
