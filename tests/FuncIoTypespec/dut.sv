module shift(a,s,z);
  parameter    width_a = 4;
  parameter    signd_a = 1;
  parameter    width_s = 2;
  parameter    width_z = 8;

  input [width_a-1:0] a;
  input [width_s-1:0] s;
  output [width_z -1:0] z;

  generate if ( signd_a )
  begin: SGNED
    assign z = fshl_s(a,s,a[width_a-1]);
  end
  else
  begin: UNSGNED
    assign z = fshl_s(a,s,1'b0);
  end
  endgenerate

  function [width_z-1:0] fshl_u_1;
     input [width_a  :0] arg1;
     input [width_s-1:0] arg2;
     input sbit;
     parameter olen = width_z;
     parameter ilen = width_a+1;
     parameter len = (ilen >= olen) ? ilen : olen;
     reg [len-1:0] result;
     reg [len-1:0] result_t;
     begin
       result_t = {(len){sbit}};
       result_t[ilen-1:0] = arg1;
       result = result_t <<< arg2;
       fshl_u_1 =  result[olen-1:0];
     end
  endfunction // fshl_u

  function [width_z-1:0] fshl_u;
     input [width_a-1:0] arg1;
     input [width_s-1:0] arg2;
     input sbit;
     fshl_u = fshl_u_1({sbit,arg1} ,arg2, sbit);
  endfunction // fshl_u

  function [width_z-1:0] fshr_u;
     input [width_a-1:0] arg1;
     input [width_s-1:0] arg2;
     input sbit;
     parameter olen = width_z;
     parameter ilen = signd_a ? width_a : width_a+1;
     parameter len = (ilen >= olen) ? ilen : olen;
     reg signed [len-1:0] result;
     reg signed [len-1:0] result_t;
     begin
       result_t = $signed( {(len){sbit}} );
       result_t[width_a-1:0] = arg1; // Line 64
       result = result_t >>> arg2;
       fshr_u =  result[olen-1:0]; // Line 66
     end
  endfunction

  function [width_z-1:0] fshl_s;
     input [width_a-1:0] arg1;
     input [width_s-1:0] arg2;
     input sbit;
     reg [width_a:0] sbit_arg1;
     begin
       if ( arg2[width_s-1] == 1'b0 )
       begin
         sbit_arg1[width_a:0] = {(width_a+1){1'b0}};
         fshl_s = fshl_u(arg1, arg2, sbit);
       end
       else
       begin
         sbit_arg1[width_a] = sbit;
         sbit_arg1[width_a-1:0] = arg1;
         fshl_s = fshr_u(sbit_arg1[width_a:1], ~arg2, sbit);
       end
     end
  endfunction
endmodule

module top (a,s,z);
  // Different size parameters than are the default of the shift module.
  parameter width_a = 240;
  parameter width_s = 9;
  parameter width_z = 240;

  input [width_a-1:0] a;
  input [width_s-1:0] s;
  output [width_z-1:0] z;

  shift #(
      .width_a(width_a),
      .width_s(width_s),
      .width_z(width_z)
  ) inst (
      .a(a),
      .s(s),
      .z(z)
  );
endmodule
