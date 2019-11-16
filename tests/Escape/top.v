
module top () ;
timeunit 100ps;
timeprecision 1ps;
endmodule


class env extends uvm_env;

  
  function void connect_phase(uvm_phase phase);
 
    assert(uvm_resource_db#(virtual add_sub_if)::read_by_name( get_full_name(), "add_sub_if", m_if));
  endfunction
 endclass

module bottom1 (input a, input b) ;
 timeunit 10ps;
 timeprecision 1ps;
 bottom2 u1 (a[0], b);
 bottom3 u2 (a[0], b);

 my_interface my_interface(.*);

endmodule

module bottom2 (input a, input b) ;
not (b, a);
endmodule


`ifndef FAIL_IF_STR_EQUAL
`define FAIL_IF_STR_EQUAL(a,b) \
  begin \
    string stra; \
    string strb; \
    stra = a; \
    strb = b; \
    if (svunit_pkg::current_tc.fail(`"fail_if_str_equal`", stra.compare(strb)==0, $sformatf(`"\"%s\" == \"%s\"`",stra,strb), `__FILE__, `__LINE__)) begin \
      if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
    end \
  end
`endif

`ifndef FAIL_UNLESS_STR_EQUAL
`define FAIL_UNLESS_STR_EQUAL(a,b) \
  begin \
    string stra; \
    string strb; \
    stra = a; \
    strb = b; \
    if (svunit_pkg::current_tc.fail(`"fail_unless_str_equal`", stra.compare(strb)!=0, $sformatf(`"\"%s\" != \"%s\"`",stra,strb), `__FILE__, `__LINE__)) begin \
      if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
    end \
  end
`endif

`timescale 100ps/10ps

module bottom3 () ;

 ddr \g_datapath:0:g_io 
    (
      .capture (capture),
      .clk (clk)
    );



endmodule

