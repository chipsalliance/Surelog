package block_1_ral_pkg;
  import uvm_pkg::*;
  import rggen_ral_pkg::*;
  `include "uvm_macros.svh"
  `include "rggen_ral_macros.svh"
  class register_file_0_register_0_reg_model extends rggen_ral_reg;
    rand rggen_ral_field bit_field_0;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
  endclass
  class register_file_0_register_1_reg_model extends rggen_ral_reg;
    rand rggen_ral_field bit_field_0;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
  endclass
  class register_file_0_reg_file_model extends rggen_ral_reg_file;
    rand register_file_0_register_0_reg_model register_0;
    rand register_file_0_register_1_reg_model register_1;
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg(register_0, '{}, 7'h00, "RW", "g_register_0.u_register")
      `rggen_ral_create_reg(register_1, '{}, 7'h04, "RW", "g_register_1.u_register")
    endfunction
  endclass
  class register_file_1_register_0_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field bit_field_0;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("register_file_0.register_0.bit_field_0", array_index[0]);
      setup_index_field("register_file_0.register_1.bit_field_0", 8'h00);
    endfunction
  endclass
  class register_file_1_register_1_reg_model extends rggen_ral_indirect_reg;
    rand rggen_ral_field bit_field_0;
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0, 0, 8, "RW", 0, 8'h00, 1, -1, "")
    endfunction
    function void setup_index_fields();
      setup_index_field("register_file_0.register_0.bit_field_0", array_index[0]);
      setup_index_field("register_file_0.register_1.bit_field_0", 8'h01);
    endfunction
  endclass
  class register_file_1_reg_file_model extends rggen_ral_reg_file;
    rand register_file_1_register_0_reg_model register_0[2];
    rand register_file_1_register_1_reg_model register_1[2];
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg(register_0[0], '{0}, 7'h00, "RW", "g_register_0.g[0].u_register")
      `rggen_ral_create_reg(register_0[1], '{1}, 7'h00, "RW", "g_register_0.g[1].u_register")
      `rggen_ral_create_reg(register_1[0], '{0}, 7'h00, "RW", "g_register_1.g[0].u_register")
      `rggen_ral_create_reg(register_1[1], '{1}, 7'h00, "RW", "g_register_1.g[1].u_register")
    endfunction
  endclass
  class register_file_2_register_file_0_register_0_reg_model extends rggen_ral_reg;
    rand rggen_ral_field bit_field_0[2];
    rand rggen_ral_rwe_field bit_field_1[2];
    rand rggen_ral_rwl_field bit_field_2[2];
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0[0], 0, 4, "RW", 0, 4'h0, 1, 0, "")
      `rggen_ral_create_field(bit_field_0[1], 4, 4, "RW", 0, 4'h0, 1, 1, "")
      `rggen_ral_create_field(bit_field_1[0], 8, 4, "RWE", 0, 4'h0, 1, 0, "register_file_0.register_0.bit_field_0")
      `rggen_ral_create_field(bit_field_1[1], 12, 4, "RWE", 0, 4'h0, 1, 1, "register_file_0.register_0.bit_field_0")
      `rggen_ral_create_field(bit_field_2[0], 16, 4, "RWL", 0, 4'h0, 1, 0, "register_file_2.register_file_0.register_1.bit_field_0")
      `rggen_ral_create_field(bit_field_2[1], 20, 4, "RWL", 0, 4'h0, 1, 1, "register_file_2.register_file_0.register_1.bit_field_0")
    endfunction
  endclass
  class register_file_2_register_file_0_register_1_reg_model extends rggen_ral_reg;
    rand rggen_ral_field bit_field_0[2];
    function new(string name);
      super.new(name, 32, 0);
    endfunction
    function void build();
      `rggen_ral_create_field(bit_field_0[0], 0, 1, "RW", 0, 1'h0, 1, 0, "")
      `rggen_ral_create_field(bit_field_0[1], 1, 1, "RW", 0, 1'h0, 1, 1, "")
    endfunction
  endclass
  class register_file_2_register_file_0_reg_file_model extends rggen_ral_reg_file;
    rand register_file_2_register_file_0_register_0_reg_model register_0[2][3];
    rand register_file_2_register_file_0_register_1_reg_model register_1;
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg(register_0[0][0], '{0, 0}, 7'h00, "RW", "g_register_0.g[0].g[0].u_register")
      `rggen_ral_create_reg(register_0[0][1], '{0, 1}, 7'h04, "RW", "g_register_0.g[0].g[1].u_register")
      `rggen_ral_create_reg(register_0[0][2], '{0, 2}, 7'h08, "RW", "g_register_0.g[0].g[2].u_register")
      `rggen_ral_create_reg(register_0[1][0], '{1, 0}, 7'h0c, "RW", "g_register_0.g[1].g[0].u_register")
      `rggen_ral_create_reg(register_0[1][1], '{1, 1}, 7'h10, "RW", "g_register_0.g[1].g[1].u_register")
      `rggen_ral_create_reg(register_0[1][2], '{1, 2}, 7'h14, "RW", "g_register_0.g[1].g[2].u_register")
      `rggen_ral_create_reg(register_1, '{}, 7'h18, "RW", "g_register_1.u_register")
    endfunction
  endclass
  class register_file_2_reg_file_model extends rggen_ral_reg_file;
    rand register_file_2_register_file_0_reg_file_model register_file_0;
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg_file(register_file_0, '{}, 7'h00, "g_register_file_0")
    endfunction
  endclass
  class block_1_block_model extends rggen_ral_block;
    rand register_file_0_reg_file_model register_file_0;
    rand register_file_1_reg_file_model register_file_1;
    rand register_file_2_reg_file_model register_file_2[2];
    function new(string name);
      super.new(name, 4, 0);
    endfunction
    function void build();
      `rggen_ral_create_reg_file(register_file_0, '{}, 7'h00, "g_register_file_0")
      `rggen_ral_create_reg_file(register_file_1, '{}, 7'h10, "g_register_file_1")
      `rggen_ral_create_reg_file(register_file_2[0], '{0}, 7'h20, "g_register_file_2.g[0]")
      `rggen_ral_create_reg_file(register_file_2[1], '{1}, 7'h40, "g_register_file_2.g[1]")
    endfunction
  endclass
endpackage
