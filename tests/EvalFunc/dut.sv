package prim_util_pkg;
  
  function automatic integer _clog2(integer value);
    integer result;
    value = value - 1;
    for (result = 0; value > 0; result = result + 1) begin
      value = value >> 1;
    end
    return result;
  endfunction

  function automatic integer vbits(integer value);

    return (value == 1) ? 1 : prim_util_pkg::_clog2(value);

  endfunction

endpackage



module top ();

function automatic integer vbits(integer value);
  return (value == 1) ? 1 : $clog2(value);
endfunction

function integer foo;
input integer value;
return value;
endfunction

function integer log2;
input integer value;
reg [31:0] shifted;
integer res;
begin
 if (value < 2)
  log2 = value;
 else
 begin
  shifted = value-1;
  for (res=0; shifted>0; res=res+1)
   shifted = shifted>>1;
  log2 = res;
 end
end
endfunction


function integer log2_2;
input integer value;
begin 
log2_2 = 0; 
if (value) begin
    value = foo(value) - 1;
    for (; value > 0; log2_2 = log2_2 + 1) 
     value = value >> 1;
end 
end
endfunction

localparam RATIO = 30;
localparam log2RATIO1 = log2(RATIO);
localparam log2RATIO2 = vbits(RATIO);
localparam log2RATIO3 = log2_2(RATIO);
localparam log2RATIO4 = prim_util_pkg::vbits(RATIO);
endmodule
