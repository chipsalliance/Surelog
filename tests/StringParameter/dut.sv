module top();
        parameter_module #(
                .FIRSTPARAMETER("TOPFIRSTVALUE"),
                .SECONDPARAMETER("TOPSECONDVALUE")
        ) test_module ();
endmodule

module parameter_module ();
parameter FIRSTPARAMETER = "FIRSTVALUE";
parameter SECONDPARAMETER = "SECONDVALUE";
endmodule

