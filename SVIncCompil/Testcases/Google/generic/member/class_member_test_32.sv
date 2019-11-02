/*
:name: class_member_test_32
:description: Test
:should_fail: 0
:tags: 8.3
*/
class myclass;
function void shifter;
  for (var int shft_idx=1, bit c=1'b0; shft_idx < n_bits;
       shft_idx++) begin
    dout = {dout} << 1;
  end
endfunction
endclass