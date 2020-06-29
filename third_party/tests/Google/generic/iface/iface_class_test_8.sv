/*
:name: iface_class_test_8
:description: Test
:tags: 8.3 8.26
*/
interface class base_ic;
parameter N = 2;
parameter type T = bit;
localparam M = f(bhg::arr[N]) -1;
endclass