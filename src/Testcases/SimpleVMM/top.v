`include "vmm.sv"

/*
`define vmm_data_new(_class) \
 \
   `define vmm_data_new_used 1 \
 \
   static VMM_LOG log = new(`"_class`", `"class`"); \


`define vmm_data_member_end(_class) \
   endfunction \
 \
   `ifndef vmm_data_new_used \
      static VMM_LOG log = new(`"_class`", `"class`"); \
 \
      function new(vmm_log log = null); \
         super.new((log == null) ? this.log : log); \
      endfunction \
   `endif \
   `undef vmm_data_new_used \
   vmm_data_methods(_class)


`vmm_data_new(toto)
`vmm_data_member_end(toto)
`vmm_data_member_end(toto)
*/
