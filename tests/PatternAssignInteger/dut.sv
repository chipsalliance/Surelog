module top(output logic[7:0] o);
   assign o = '{0:1, 3:1, 7:1, default:0};
endmodule