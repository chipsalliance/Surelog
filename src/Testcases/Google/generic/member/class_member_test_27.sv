/*
:name: class_member_test_27
:description: Test
:should_fail: 0
:tags: 8.3
*/
class myclass;
virtual function void starter(uvm_phase phase);
  report_server new_server = new;
endfunction : starter
endclass