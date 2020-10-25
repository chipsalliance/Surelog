
package pack;

virtual class door;

    int state;
    int timer;
    logic open,lock,clock;
    parameter OPENED    = 2'b00,
	      CLOSED    = 2'b01,
	      LOCKED    = 2'b10;
  pure virtual task door_fsm();

  function f1();
    f2();
  endfunction

endclass


class doorOpen extends door;

    extern function new (int a);
   
    function f2();
      f1();
    endfunction

    function new (int b);
    f1();
    f2();
    endfunction

    virtual task door_fsm();
        if (open)  state = OPENED;
    endtask

endclass

endpackage


module door_mod;

    pack::doorOpen open;
    initial begin
        open = new();       
        open.door_fsm();  
        open.f1();   
    end
endmodule

