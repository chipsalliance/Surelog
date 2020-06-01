module FSM(clock, keys, brake, accelerate, Speed);
  input clock, keys, brake, accelerate;
  wire clock, keys, brake, accelerate;
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
 
    if (accelerate)
      case (Speed)
      Stop:   Speed <= Slow;
      Move:   Speed <= Faster;
      default:begin
      end   
      endcase
    end
  else if (brake)
    case (Speed)
      Stop:   Speed <= Faster;
      Move:   Speed <= Faster;
      default:begin
      end  
    endcase
  else begin
    Speed <= Speed;
  end 
  
  end
  
  endmodule
  
