module top (in_a, out_vt);

input [1:0] in_a;
output out_vt;
reg   [2:0] result;
assign out_vt = result;

always @(*)
  begin
     result    = 3'b000;
     case (in_a)
       2'b00 : begin
          result = 3'b101;
       end

       2'b01: begin
          result    = 3'b001;
       end

       default;

     endcase
  end
endmodule
