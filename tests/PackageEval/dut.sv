package test_pkg;

 parameter int NStraps  = 2;
 parameter int MioStrapPos [0:NStraps-1] = '{1, 0};


typedef struct packed {
    logic valid;
    logic [63:0] data;
} t_test;
parameter TEST_SIZE = $bits(t_test);


endpackage


