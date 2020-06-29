/*
:name: typedef_test_13
:description: Test
:tags: 6.18
*/
typedef bit data_t;
parameter k = 6;
parameter j = 5;
parameter l = 2;

typedef data_t my_ar_t [bit[31:0][k:0]][bit[j:0][l:0]];
