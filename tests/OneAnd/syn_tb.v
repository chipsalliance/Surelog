module syn_tb(input logic clk, output logic o); 
  logic a, b;

  integer state = 0;
  always @ (posedge clk) begin
    if (state==0) begin       
        a <= 0;
        b <= 0;
        state++; 
    end
    else if (state==1) begin
        a <= 1;
        b <= 1;
        state++;  
        $display("%0d & %0d = %0d", a, b, o);
     end
    else if (state==2) begin
        a <= 1;
        b <= 0;
        state++;
        $display("%0d & %0d = %0d", a, b, o);
    end
    else if (state==3) begin
        a <= 0;
        b <= 1;
        state++;
        $display("%0d & %0d = %0d", a, b, o);
     end 
    else if (state==4) begin
        $display("%0d & %0d = %0d", a, b, o);
        state++; 
        $finish; 
    end 
  end

   
  dut dut1(a,b,o);
    
endmodule
