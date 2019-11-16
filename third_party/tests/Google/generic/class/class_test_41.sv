/*
:name: class_test_41
:description: Test
:should_fail: 0
:tags: 6.15 8.3
*/
class macros_as_class_item;
 `uvm_object_utils(stress_seq)
 `uvm_object_registry(myclass, "class_name")
 `uvm_sweets(dessert)
 `non_uvm_macro(apple, `banana, "cherry")
endclass