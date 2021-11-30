virtual class C#(parameter type T = logic, parameter SIZE = 1);
    typedef logic [SIZE-1:0] t_vector;
    typedef T t_array [SIZE-1:0];
    typedef struct {
        t_vector m0 [2*SIZE-1:0];
        t_array m1;
    } t_struct;
endclass


module top ();
    typedef logic [7:0] t_t0;
    C#(t_t0,3)::t_vector v0; C#(t_t0,3)::t_array a0;
    C#(bit,4)::t_struct s0;
endmodule

