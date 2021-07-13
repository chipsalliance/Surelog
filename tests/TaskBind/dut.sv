module tb;
 initial display();
 // Note that the task is now automatic
 task automatic display();
 integer i = 0;
 i = i + 1;
 $display("i=%0d", i);
 endtask
endmodule // tb

