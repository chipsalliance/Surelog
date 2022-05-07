package pack;

class uvm_mem_region;

   /*local*/ bit [63:0] Xstart_offsetX;  // Can't be local since function
   /*local*/ bit [63:0] Xend_offsetX;    // calls not supported in constraints


   // Function -- NODOCS -- get_start_offset
   //
   // Get the start offset of the region
   //
   // Return the address offset, within the memory,
   // where this memory region starts.
   //
   extern function bit [63:0] get_start_offset();


   // Function -- NODOCS -- get_end_offset
   //
   // Get the end offset of the region
   //
   // Return the address offset, within the memory,
   // where this memory region ends.
   //
   extern function bit [63:0] get_end_offset();


endclass




class uvm_mem_mam;

uvm_mem_region in_use[$];
extern function uvm_mem_mam_cfg reconfigure(uvm_mem_mam_cfg cfg = null);

endclass

function uvm_mem_mam_cfg uvm_mem_mam::reconfigure(uvm_mem_mam_cfg cfg = null);
  
   top = this.in_use[i].get_start_offset();

endfunction: reconfigure

endpackage
