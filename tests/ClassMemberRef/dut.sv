package pkg;

class m_uvm_printer_knobs;

  bit identifier = 1;

endclass

class uvm_printer;

  extern virtual function void set_name_enabled (bit enabled);
  m_uvm_printer_knobs knobs ;

endclass

function void uvm_printer::set_name_enabled (bit enabled);
knobs.identifier = enabled ;
endfunction

endpackage

module top();

pkg::uvm_printer printer;
initial begin
    printer = new;
printer.set_name_enabled (en);
end
endmodule // top
