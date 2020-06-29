/*
:name: class_member_test_55
:description: Test
:tags: 8.3
*/
class myclass extends uvm_object;
static constraint size_c {
  soft A inside {[1:10]};
  A + B <= C;
}
endclass