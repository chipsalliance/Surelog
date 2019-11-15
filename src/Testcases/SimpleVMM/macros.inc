`define INFO(msg) \
  $display("INFO:  [%0t][%0s]: %s", $time, name, msg)

`define SVTEST_END \
    if (svunit_ut.get_error_count() == local_error_count) \
      `INFO($sformatf(`"%s::PASSED`", _testName)); \
   else \
      `INFO($sformatf(`"%s::FAILED`", _testName)); \
    svunit_ut.update_exit_status(); \
  end

`define uvm_file `__FILE__
`define uvm_line `__LINE__

 
`define BOTTOM `TOP 
`define TOP `BOTTOM1
`define BOTTOM1 `BOTTOM

`define uvm_fatal(ID, MSG) \
   begin \
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,ID)) \
       uvm_report_fatal (ID, MSG, UVM_NONE, `uvm_file, `uvm_line, "", 1); \
   end

`define uvm_declare_p_sequencer(SEQUENCER) \
  SEQUENCER p_sequencer;\
  virtual function void m_set_p_sequencer();\
    super.m_set_p_sequencer(); \
    if( !$cast(p_sequencer, m_sequencer)) \
        `uvm_fatal("DCLPSQ", \
        $sformatf("%m %s Error casting p_sequencer, please verify that this sequence/sequence item is intended to execute on this type of sequencer", get_full_name())) \
  endfunction  


