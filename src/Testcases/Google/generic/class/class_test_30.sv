/*
:name: class_test_30
:description: Test
:should_fail: 0
:tags: 6.15 8.3
*/
class Foo;
integer size;
function new (integer size);
  begin
    this.size = size;
  end
endfunction
task print();
  begin
    $write("Hello, world!");
  end
endtask
endclass