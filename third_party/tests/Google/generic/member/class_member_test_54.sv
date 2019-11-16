/*
:name: class_member_test_54
:description: Test
:should_fail: 0
:tags: 8.3
*/
class myclass extends uvm_object;
constraint size_c {
  A + B <= C;
};
endclass