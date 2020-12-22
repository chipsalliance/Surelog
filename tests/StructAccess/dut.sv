module top();
	
	typedef enum logic [1:0] {
	  PMP_MODE_OFF   = 2'b00
	} pmp_cfg_enum;
	
	typedef struct packed {
			logic a;
	} pmp_cfg_struct;
	
	typedef struct packed {
	  pmp_cfg_enum mode;
	  pmp_cfg_struct struct_var;
	} pmp_cfg_t;
	
	pmp_cfg_t      csr_pmp_cfg_i  [4];
	pmp_cfg_t      csr_pmp_cfg_ie;
	pmp_cfg_enum enum_test;
	
	assign enum_test = PMP_MODE_OFF;
	
	logic t = enum_test[0];
	
	pmp_cfg_enum first = csr_pmp_cfg_i[0].mode;
	logic second = csr_pmp_cfg_ie.mode[0];
	logic third = csr_pmp_cfg_ie.struct_var.a;
	
	assign csr_pmp_cfg_ie.mode = PMP_MODE_OFF;

endmodule
