package pack;
 
class ovm_printer;
endclass

class ovm_options_container;
ovm_printer     printer;
endclass


ovm_options_container ovm_auto_options_object = ovm_options_container::init();

class ovm_object;

extern function void print(ovm_printer printer=null);

//ovm_auto_options_object.printer = printer;

//endfunction

endclass

function void ovm_object::print(ovm_printer printer=null);

  if(printer==null)
    printer = ovm_default_printer;

  if(printer.istop()) begin
    printer.print_object(get_name(), this);
  end
  else begin
    //do m_field_automation here so user doesn't need to call anything to get
    //automation.
    ovm_auto_options_object.printer = printer;
    m_field_automation(null, OVM_PRINT, "");
    //call user override
    do_print(printer);
  end
endfunction


endpackage

