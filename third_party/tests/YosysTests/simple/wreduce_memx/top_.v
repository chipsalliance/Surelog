module top ( in_data, do );

   input [15:0] in_data;
   output [15:0]  do;
   reg [15:0] out_data;

   assign do = out_data;

   always @ (*)
     begin

    Test_task(in_data, out_data);
         // out_data = in_data; // This works but above task doesn't

     end

   task Test_task;
      input [15:0]  in_d;
      output [15:0] out_data;

      begin
        out_data = in_d;
      end
   endtask

endmodule
