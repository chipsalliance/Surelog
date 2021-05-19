module tb;

 initial display();
 
 task display();
 integer i = 0;
 i = i + 1;
 $display("i=%0d", i);
 endtask
endmodule
