/*
:name: class_test_45
:description: Test
:tags: 6.15 8.3
*/
class macros_as_class_item;
 `uvm_object_param_utils_begin(my_class)
   `uvm_field_int(blah1, F1)
   `uvm_field_real(blah2, F2)
   `uvm_field_enum(blah3, F3)
 `uvm_object_utils_end
endclass