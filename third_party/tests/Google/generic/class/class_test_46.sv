/*
:name: class_test_46
:description: Test
:tags: 6.15 8.3
*/
class macros_as_class_item;
 `uvm_component_utils(my_type)
 `uvm_component_utils_begin(my_type)
   `uvm_field_object(blah1, F1)
   `uvm_field_event(blah2, F2)
   `uvm_field_string(blah3, F3)
 `uvm_component_utils_end
endclass