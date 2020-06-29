/*
:name: class_test_44
:description: Test
:tags: 6.15 8.3
*/
class macros_as_class_item;
 `uvm_field_utils_begin(my_class)
   `uvm_field_int(blah1, flag1)
   `uvm_field_real(blah2, flag2)
   `uvm_field_enum(blah3, flag3)
   `uvm_field_object(blah4, flag4)
   `uvm_field_event(blah5, flag5)
   `uvm_field_string(blah6, flag6)
   `uvm_field_array_int(blah7, flag7)
   `uvm_field_sarray_int(blah8, flag8)
   `uvm_field_aa_int_string(blah9, flag9)
 `uvm_field_utils_end
endclass