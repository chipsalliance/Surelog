/*
:name: iface_class_test_11
:description: Test
:tags: 8.3 8.26
*/
interface class base_ic;
parameter N = 2;
typedef some_class#(N) car_type;
pure virtual task pure_task1;
pure virtual function void pure_task1;
endclass