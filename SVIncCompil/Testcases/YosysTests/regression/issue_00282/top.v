module top(input clk,input[3:0] in, output [7:0] out);
        reg[2:0] state;
        always @(posedge clk) begin
                out<=0;
                case (state)
                        0: begin
                                if(in == 0) begin
                                        state<=1;
                                        out<=0;
                                end
                                if(in == 1) begin
                                        state<=2;
                                        out<=1;
                                end
                                if(in == 2) begin
                                        state<=5;
                                        out<=2;
                                end
                        end
                        1: begin
                                if(in == 0) begin
                                        state<=1;
                                        out<=3;
                                end
                                if(in == 1) begin
                                        state<=3;
                                        out<=4;
                                end
                                if(in == 2) begin
                                        state<=1;
                                        out<=5;
                                end
                                if(in == 3) begin
                                        state<=3;
                                        out<=6;
                                end
                                if(in == 4) begin
                                        state<=2;
                                        out<=7;
                                end
                                if(in == 5) begin
                                        state<=5;
                                        out<=8;
                                end
                                if(in == 6) begin
                                        state<=3;
                                        out<=9;
                                end
                                if(in == 7) begin
                                        state<=5;
                                        out<=10;
                                end
                                if(in == 8) begin
                                        state<=3;
                                        out<=11;
                                end
                                if(in == 9) begin
                                        state<=2;
                                        out<=12;
                                end
                        end
                        2: begin
  if(in == 0) begin
                                        state<=2;
                                        out<=13;
                                end
                                if(in == 1) begin
                                        state<=2;
                                        out<=14;
                                end
                                if(in == 2) begin
                                        state<=1;
                                        out<=15;
                                end
                                if(in == 3) begin
                                        state<=1;
                                        out<=16;
                                end
                                if(in == 4) begin
                                        state<=2;
                                        out<=17;
                                end
                                if(in == 5) begin
                                        state<=2;
                                        out<=18;
                                end
                                if(in == 6) begin
                                        state<=2;
                                        out<=19;
                                end
                                if(in == 7) begin
                                        state<=5;
                                        out<=20;
                                end
                                if(in == 8) begin
                                        state<=5;
                                        out<=21;
                                end
                                if(in == 9) begin
                                        state<=2;
                                        out<=22;
                                end
                        end
 3: begin
                                if(in == 0) begin
                                        state<=3;
                                        out<=23;
                                end
                                if(in == 1) begin
                                        state<=3;
                                        out<=24;
                                end
                                if(in == 2) begin
                                        state<=3;
                                        out<=25;
                                end
                                if(in == 3) begin
                                        state<=3;
                                        out<=26;
                                end
                                if(in == 4) begin
                                        state<=4;
                                        out<=27;
                                end
                                if(in == 5) begin
                                        state<=5;
                                        out<=28;
                                end
                                if(in == 6) begin
                                        state<=3;
                                        out<=29;
                                end
                                if(in == 7) begin
                                        state<=5;
                                        out<=30;
                                end
                                if(in == 8) begin
                                        state<=3;
                                        out<=31;
                                end
                                if(in == 9) begin
                                        state<=2;
                                        out<=32;
                                end
                        end
4: begin
                                if(in == 0) begin
                                        state<=4;
                                        out<=33;
                                end
                                if(in == 1) begin
                                        state<=4;
                                        out<=34;
                                end
                                if(in == 2) begin
                                        state<=3;
                                        out<=35;
                                end
                                if(in == 3) begin
                                        state<=3;
                                        out<=36;
                                end
                                if(in == 4) begin
                                        state<=4;
                                        out<=37;
                                end
                                if(in == 5) begin
                                        state<=2;
                                        out<=38;
                                end
                                if(in == 6) begin
                                        state<=2;
                                        out<=39;
                                end
                                if(in == 7) begin
                                        state<=5;
                                        out<=40;
                                end
                                if(in == 8) begin
                                        state<=5;
                                        out<=41;
                                end
                                if(in == 9) begin
                                        state<=2;
                                        out<=42;
                                end
                        end
   5: begin
                                if(in == 0) begin
                                        state<=1;
                                        out<=43;
                                end
                                if(in == 1) begin
                                        state<=1;
                                        out<=44;
                                end
                                if(in == 2) begin
                                        state<=1;
                                        out<=45;
                                end
                                if(in == 3) begin
                                        state<=1;
                                        out<=46;
                                end
                                if(in == 4) begin
                                        state<=2;
                                        out<=47;
                                end
                                if(in == 5) begin
                                        state<=5;
                                        out<=48;
                                end
                                if(in == 6) begin
                                        state<=5;
                                        out<=49;
                                end
                                if(in == 7) begin
                                        state<=5;
                                        out<=50;
                                end
                                if(in == 8) begin
                                        state<=5;
                                        out<=51;
                                end
                                if(in == 9) begin
                                        state<=2;
                                        out<=52;
                                end
                        end
                endcase
        end
endmodule
