

function automatic bit my_function();
endfunction

nettype bit net_bit with my_function;


nettype real my_real;

module dut ();

    my_real my_real_net;

endmodule


typedef some_other_type myalias;



typedef struct {
  real field1;
  bit field2;
} T;


function automatic T Tsum (input T driver[]);
  Tsum.field1 = 0.0;
  foreach (driver[i])
    Tsum.field1 += driver[i].field1;
endfunction

nettype T wT;

nettype T wTsum with Tsum;
