

class Packet extends uvm_transaction;
function void uvm_default_factory::print (int all_types=1);
`wrapper("UVM/FACTORY/PRINT",`UVM_STRING_QUEUE_STREAMING_PACK(qs),UVM_NONE)
endfunction
endclass
