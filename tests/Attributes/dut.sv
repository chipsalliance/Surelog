module bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  bar bar_instance ( (* clock_connected  = 1'b1 *) clk, rst, (* this_is_the_input  = "foo" *) inp, out);


  assign blah  = pieces0  & (* src = "attacks-qbb.py:34" *) b ;

  assign \$37  = empty2 <<< (* src = "attacks-qbb.py:38" *) 4'h9;

  initial begin;
    (* full_case = 1 *)
    (* parallel_case = 1 *)
    case (a)
      2'b00 :
        b = 0;
      2'b01, 2'b10 :
        b = 1;
      default :
        b = 0;
    endcase
  end


   
endmodule

