package uart_csr_ral_pkg;
  import uvm_pkg::*;
  import rggen_ral_pkg::*;
  `include "uvm_macros.svh"
  `include "rggen_ral_macros.svh"
  class rbr_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field rbr;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(rbr, 0, 8, "RO", 1, 8'h00, 0, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("lcr.dlab", 1'h0);
    endfunction
  endclass
  class thr_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field thr;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(thr, 0, 8, "WO", 0, 8'hff, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("lcr.dlab", 1'h0);
    endfunction
  endclass
  class ier_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field erbfi;
    rand rggen_ral_field etbei;
    rand rggen_ral_field elsi;
    rand rggen_ral_field edssi;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(erbfi, 0, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(etbei, 1, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(elsi, 2, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(edssi, 3, 1, "RW", 0, 1'h0, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("lcr.dlab", 1'h0);
    endfunction
  endclass
  class iir_reg_model extends rggen_ral_reg;
    rand rggen_ral_field intpend;
    rand rggen_ral_field intid2;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(intpend, 0, 1, "RO", 1, 1'h1, 1, -1, "")
      `rggen_ral_create_field(intid2, 1, 3, "RO", 1, 3'h0, 1, -1, "")
    endfunction
  endclass
  class fcr_reg_model extends rggen_ral_reg;
    rand rggen_ral_field fifoen;
    rand rggen_ral_w1trg_field rcvr_fifo_reset;
    rand rggen_ral_w1trg_field xmit_fifo_reset;
    rand rggen_ral_field dma_mode_select;
    rand rggen_ral_field rcvr_fifo_trigger_level;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(fifoen, 0, 1, "WO", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(rcvr_fifo_reset, 1, 1, "W1TRG", 0, 1'h0, 0, -1, "")
      `rggen_ral_create_field(xmit_fifo_reset, 2, 1, "W1TRG", 0, 1'h0, 0, -1, "")
      `rggen_ral_create_field(dma_mode_select, 3, 1, "WO", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(rcvr_fifo_trigger_level, 6, 2, "WO", 0, 2'h0, 1, -1, "")
    endfunction
  endclass
  class lcr_reg_model extends rggen_ral_reg;
    rand rggen_ral_field wls;
    rand rggen_ral_field stb;
    rand rggen_ral_field pen;
    rand rggen_ral_field eps;
    rand rggen_ral_field stick_parity;
    rand rggen_ral_field set_break;
    rand rggen_ral_field dlab;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(wls, 0, 2, "RW", 0, 2'h3, 1, -1, "")
      `rggen_ral_create_field(stb, 2, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(pen, 3, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(eps, 4, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(stick_parity, 5, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(set_break, 6, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(dlab, 7, 1, "RW", 0, 1'h0, 1, -1, "")
    endfunction
  endclass
  class mrc_reg_model extends rggen_ral_reg;
    rand rggen_ral_field dtr;
    rand rggen_ral_field rts;
    rand rggen_ral_field out1;
    rand rggen_ral_field out2;
    rand rggen_ral_field loop;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(dtr, 0, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(rts, 1, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(out1, 2, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(out2, 3, 1, "RW", 0, 1'h0, 1, -1, "")
      `rggen_ral_create_field(loop, 4, 1, "RW", 0, 1'h0, 1, -1, "")
    endfunction
  endclass
  class lsr_reg_model extends rggen_ral_reg;
    rand rggen_ral_field dr;
    rand rggen_ral_field oe;
    rand rggen_ral_field pe;
    rand rggen_ral_field fe;
    rand rggen_ral_field bi;
    rand rggen_ral_field thre;
    rand rggen_ral_field temt;
    rand rggen_ral_field error_in_rcvr_fifo;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(dr, 0, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(oe, 1, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(pe, 2, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(fe, 3, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(bi, 4, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(thre, 5, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(temt, 6, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(error_in_rcvr_fifo, 7, 1, "RO", 1, 1'h0, 1, -1, "")
    endfunction
  endclass
  class msr_reg_model extends rggen_ral_reg;
    rand rggen_ral_field dcts;
    rand rggen_ral_field ddsr;
    rand rggen_ral_field teri;
    rand rggen_ral_field ddcd;
    rand rggen_ral_field cts;
    rand rggen_ral_field dsr;
    rand rggen_ral_field ri;
    rand rggen_ral_field dcd;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(dcts, 0, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(ddsr, 1, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(teri, 2, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(ddcd, 3, 1, "RO", 1, 1'h0, 1, -1, "")
      `rggen_ral_create_field(cts, 4, 1, "RO", 1, 1'h0, 0, -1, "")
      `rggen_ral_create_field(dsr, 5, 1, "RO", 1, 1'h0, 0, -1, "")
      `rggen_ral_create_field(ri, 6, 1, "RO", 1, 1'h0, 0, -1, "")
      `rggen_ral_create_field(dcd, 7, 1, "RO", 1, 1'h0, 0, -1, "")
    endfunction
  endclass
  class scratch_reg_model extends rggen_ral_reg;
    rand rggen_ral_field scratch;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(scratch, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
  endclass
  class dll_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field dll;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(dll, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("lcr.dlab", 1'h1);
    endfunction
  endclass
  class dlm_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field dlm;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(dlm, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("lcr.dlab", 1'h1);
    endfunction
  endclass
  class uart_csr_block_model extends rggen_ral_block;
    rand rbr_reg_model rbr;
    rand thr_reg_model thr;
    rand ier_reg_model ier;
    rand iir_reg_model iir;
    rand fcr_reg_model fcr;
    rand lcr_reg_model lcr;
    rand mrc_reg_model mrc;
    rand lsr_reg_model lsr;
    rand msr_reg_model msr;
    rand scratch_reg_model scratch;
    rand dll_reg_model dll;
    rand dlm_reg_model dlm;
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg(rbr, '{}, 5'h00, "RO", "g_rbr.u_register")
      `rggen_ral_create_reg(thr, '{}, 5'h00, "WO", "g_thr.u_register")
      `rggen_ral_create_reg(ier, '{}, 5'h04, "RW", "g_ier.u_register")
      `rggen_ral_create_reg(iir, '{}, 5'h08, "RO", "g_iir.u_register")
      `rggen_ral_create_reg(fcr, '{}, 5'h08, "WO", "g_fcr.u_register")
      `rggen_ral_create_reg(lcr, '{}, 5'h0c, "RW", "g_lcr.u_register")
      `rggen_ral_create_reg(mrc, '{}, 5'h10, "RW", "g_mrc.u_register")
      `rggen_ral_create_reg(lsr, '{}, 5'h14, "RO", "g_lsr.u_register")
      `rggen_ral_create_reg(msr, '{}, 5'h18, "RO", "g_msr.u_register")
      `rggen_ral_create_reg(scratch, '{}, 5'h1c, "RW", "g_scratch.u_register")
      `rggen_ral_create_reg(dll, '{}, 5'h00, "RW", "g_dll.u_register")
      `rggen_ral_create_reg(dlm, '{}, 5'h04, "RW", "g_dlm.u_register")
    endfunction
  endclass
endpackage
