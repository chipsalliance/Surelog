/*
:name: class_test_43
:description: Test
:tags: 6.15 8.3
*/
class macros_as_class_item;
 `uvm_object_utils_begin(foobar)
 `uvm_field_int(node, UVM_DEFAULT);
 `uvm_field_int(foo::bar_t, UVM_DEFAULT);
 `uvm_field_enum(offset, UVM_DEFAULT)
 `uvm_object_utils_end
endclass