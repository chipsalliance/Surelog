/*
:name: class_member_test_31
:description: Test
:tags: 8.3
*/
class myclass;
function void shifter;
  for (int shft_idx=0, bit c=1'b1; shft_idx < n_bits;
       shft_idx++) begin
    dout = {dout} << 1;
  end
endfunction
endclass