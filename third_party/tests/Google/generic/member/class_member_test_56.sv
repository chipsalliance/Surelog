/*
:name: class_member_test_56
:description: Test
:tags: 8.3
*/
class myclass extends uvm_object;
constraint size_c {
  soft A inside {[1:10]};
  A dist { 1 := 10, [2:9] :/ 80, 10 := 10 };
  A + B <= C;
}
endclass