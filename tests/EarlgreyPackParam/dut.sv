
package alert_handler_reg_pkg;
  parameter int NAlerts = 35;
  parameter logic [NAlerts-1:0] AsyncOn = 35'b11111111111111111100000000000000000;
endpackage

module test ();

 parameter Toto = alert_handler_reg_pkg::AsyncOn[22:21];
endmodule


module prim_alert_sender
#(
  parameter bit AsyncOn = 1'b1,
  parameter bit IsFatal = 1'b0
) ();

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) dec_ack ();

    if (AsyncOn) begin : gen_async_assert                                                          
    end

 endmodule

module GOOD();
endmodule

module prim_diff_decode #(
  parameter bit AsyncOn = 1'b0
) ();

  if (AsyncOn) begin : gen_async
     GOOD good();
  end

endmodule

module top ();

  aes #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[22:21])
	) u_aes ();
  
endmodule

module aes  
#( parameter logic [4-1:0] AlertAsyncOn = {4{1'b1}})();

   for (genvar i = 0; i < 4; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) alert_sender (
    );
  end

endmodule

