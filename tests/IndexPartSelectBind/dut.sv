package pkg;


typedef struct {
  uvm_reg_data_t data;
} uvm_reg_bus_op;

class tt;

virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);

for (int i = 0; i < nbytes; i++) begin
   rw.data[i] = rw.data[i*8+:8];
   
end

return gp;

endfunction

endclass

endpackage

