module dut();


    aw_select: assume property( @(posedge clk_i) (slv_req_i.aw_valid |->
                                                 (slv_aw_select_i < NoMstPorts))) else
      $fatal(1, "slv_aw_select_i is %d: AW has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_aw_select_i, NoMstPorts);


endmodule

