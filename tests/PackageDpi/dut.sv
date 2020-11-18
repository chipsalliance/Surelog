package pack;

import "DPI-C" context function int uvm_hdl_check_path(string path);

string uvm_aa_string_key;

typedef enum {

UVM_CORE_UNINITIALIZED,
UVM_CORE_PRE_INIT

} uvm_core_state;

uvm_core_state m_uvm_core_state = UVM_CORE_UNINITIALIZED;


uvm_object_wrapper uvm_deferred_init[$];


class toto;
const static int DO_NOT_CATCH      = 1; 
endclass

const static int DO_NOT_CATCH_2     = 1; 


endpackage

