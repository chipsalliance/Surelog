
typedef enum {UNICAST=11,MULTICAST,BROADCAST} pkt_type;

program constaint_mode_ex;
  class frame_t; 
    rand pkt_type ptype;
    rand integer len;
    rand bit  [7:0] payload [];
    constraint common {
      payload.size() == len;
    }
    // Constraint the members
    constraint unicast {
      len <= 2;
      ptype == UNICAST;
    }
    // Constraint the members
    constraint multicast {
      len >= 3;
      len <= 4;
      ptype == MULTICAST;
    }
    function string getType(pkt_type ltype);
      begin
        case(ltype)
         UNICAST   : getType = "UNICAST";
         MULTICAST : getType = "MULTICAST";
         BROADCAST : getType = "BROADCAST";
         default   : getType = "UNKNOWN";
        endcase
      end
    endfunction
    // Print the members of the class
    task print() ;
      begin
        integer i =0;
        $write("Packet type %s\n",getType(ptype));
        $write("Size of frame is %0d\n",len);
        if (payload.size() > 0) begin
          $write("Payload is ");
          for (i=0; i < len; i++) begin
            $write(" %2x",payload[i]);
          end
          $write("\n");
        end
      end  
    endtask
  endclass
 
  initial begin 
     frame_t frame = new();
     integer j = 0;
     $write("-------------------------------\n");
     // Do contraint for Unicast frame
     frame.multicast.constraint_mode(0);
     if (frame.multicast.constraint_mode() == 0) begin
       if (frame.randomize() == 1) begin
         frame.print(); 
       end else begin
         $write("Failed to randomize frame\n");
       end
     end else begin
        $write("Failed to disable constraint multicast\n");
     end
     $write("-------------------------------\n");
     // Check the status of constraint multicast
     $write ("Constraint state of multicast is %0d\n",
         frame.multicast.constraint_mode());
     $write("-------------------------------\n");
     // Now disable the unitcast and enable multicast
     frame.unicast.constraint_mode(0);
     frame.multicast.constraint_mode(1);
     if (frame.randomize() == 1) begin
       frame.print(); 
     end else begin
       $write("Failed to randomize frame\n");
     end
     $write("-------------------------------\n");
  end
endprogram
