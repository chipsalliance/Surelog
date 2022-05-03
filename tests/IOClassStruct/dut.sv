package uvm_pkg;

class uvm_resource_types;

  typedef struct
  {
    int unsigned read_count;
  } access_t;

endclass

class uvm_resource_base;

  function void record_read_access();

     uvm_resource_types::access_t access_record;

     access_record.read_count++;

  endfunction


  function void init_access_record (inout uvm_resource_types::access_t access_record);
  access_record.read_count = 0;
endfunction


endclass

endpackage
