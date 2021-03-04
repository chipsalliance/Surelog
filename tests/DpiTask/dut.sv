module top ();

  export "DPI-C" task task_1;
  task task_1(output int ret);
    ret = 2;
  endtask

endmodule
