/*
:name: class_member_test_52
:description: Test
:tags: 8.3
*/
class myclass;
function apkg::num_t apply_all();
  foreach (this.foo[i]) begin
    y = {y, this.foo[i]};
    z = {z, super.bar[i]};
  end
endfunction
endclass