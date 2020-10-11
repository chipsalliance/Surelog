package pack;

virtual class door;
    int state;
    int timer;
    logic open,lock,clock;
    parameter OPENED    = 2'b00,
	      CLOSED    = 2'b01,
	      LOCKED    = 2'b10;
    pure virtual task door_fsm();
endclass

class doorOpen extends door;
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
    end
endmodule

class toto;
endclass

